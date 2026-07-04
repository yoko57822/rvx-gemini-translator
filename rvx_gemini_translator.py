#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RPG Maker VX (.rvdata) / VX Ace (.rvdata2) Gemini auto translator.

- Select a RPG Maker VX or VX Ace Game.exe.
- Reads Data/*.rvdata and Data/*.rvdata2 Ruby Marshal files without Ruby.
- Backs up Data first.
- Translates likely player-visible strings through Gemini API.
- Writes patched files while preserving the original Marshal structure.

Use only for games you are legally allowed to modify/translate.
"""

from __future__ import annotations

import argparse
import base64
import dataclasses
import datetime as _dt
import hashlib
import json
import os
import queue
import re
import shutil
import struct
import sys
import tempfile
import threading
import time
import traceback
import webbrowser
import zlib
from pathlib import Path
from typing import Any, Callable, Iterable, Optional

APP_NAME = "RVX Gemini Translator"
APP_VERSION = "0.3.1"
DEFAULT_MODEL = "gemini-3.1-flash-lite"

# RPG Maker VX / VX Ace data files where translating strings is usually meaningful.
SAFE_FILE_RE = re.compile(
    r"^(Actors|Classes|Skills|Items|Weapons|Armors|Enemies|Troops|States|CommonEvents|MapInfos|System|Map\d{3})\.rvdata2?$",
    re.IGNORECASE,
)

# Files where changing strings tends to break scripts/assets or has little player-visible value.
ALWAYS_SKIP_FILES = {
    "scripts.rvdata",
    "scripts.rvdata2",
}
DEFAULT_SKIP_FILES = {
    "animations.rvdata",
    "areas.rvdata",
    "animations.rvdata2",
    "tilesets.rvdata2",
}

# Event command codes whose string parameters are player-visible in VX.
# 401: Show Text line, 102: Choices, 402: choice branch label, 405: scrolling text line,
# 320/324: change actor name/nickname. 325 is VX Ace profile but harmless if present.
VISIBLE_EVENT_CODES = {102, 401, 402, 405, 320, 324, 325}

# Ruby/RPG Maker control codes and common format placeholders to protect during translation.
TOKEN_PATTERN = re.compile(
    r"(\\[A-Za-z!\.\|><\^\$\\\{\}](?:\[[^\]\r\n]{0,80}\])?"
    r"|%\d+\$[sdif]"
    r"|%[+#\- 0]*(?:\d+|\*)?(?:\.(?:\d+|\*))?[sdif]"
    r"|\{\d+\}"
    r"|<[^>\r\n]{1,80}>)"
)

FILE_EXT_RE = re.compile(r"\.(png|jpe?g|bmp|gif|ogg|wav|mp3|mid|midi|wma|dll|exe|rvdata2?|rxdata|rb|txt)$", re.I)

# Ruby encoding names (from :encoding ivars) -> Python codec names.
RUBY_ENCODING_ALIASES = {
    "utf-8": "utf-8",
    "windows-31j": "cp932",
    "shift_jis": "cp932",
    "cp932": "cp932",
    "euc-jp": "euc_jp",
    "us-ascii": "ascii",
    "ascii-8bit": "latin-1",
}
CJK_RE = re.compile(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff\uac00-\ud7a3]")
LETTER_RE = re.compile(r"[A-Za-z\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff\uac00-\ud7a3]")
CONTROL_CHARS_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f]")

LogFn = Callable[[str], None]
# phase("scan"|"translate"|"save"), current, total, detail
ProgressFn = Callable[[str, int, int, str], None]


class RubyMarshalParseError(Exception):
    pass


class TranslationCancelled(Exception):
    """Raised when the user requests a cooperative stop between batches/files."""


class GeminiParseError(RuntimeError):
    """The API answered, but the response could not be parsed as translations.

    Distinguished from transport/SDK errors so only genuine parse failures trigger
    the split-and-retry strategy instead of an endless retry cascade.
    """


@dataclasses.dataclass
class MarshalNode:
    typ: str
    start: int
    end: int = 0
    children: list["MarshalNode"] = dataclasses.field(default_factory=list)
    path: tuple[str, ...] = dataclasses.field(default_factory=tuple)
    text_bytes: Optional[bytes] = None
    text: Optional[str] = None
    encoding: Optional[str] = None
    replacement_bytes: Optional[bytes] = None
    value: Any = None
    class_name: Optional[str] = None
    fields: list[tuple[str, "MarshalNode"]] = dataclasses.field(default_factory=list)
    meta: dict[str, Any] = dataclasses.field(default_factory=dict)

    def is_modified(self) -> bool:
        if self.replacement_bytes is not None:
            return True
        return any(child.is_modified() for child in self.children)


@dataclasses.dataclass
class TextCandidate:
    node: MarshalNode
    file_path: Path
    text: str
    path_text: str


@dataclasses.dataclass
class TranslatorConfig:
    exe_path: Path
    api_key: str
    model: str = DEFAULT_MODEL
    source_lang: str = "auto"
    target_lang: str = "Korean"
    include_ascii: bool = True
    include_internal_names: bool = False
    process_all_files: bool = False
    dry_run: bool = False
    batch_size: int = 60
    batch_chars: int = 10000
    request_delay: float = 0.25
    # Free-form user guidance appended to the system prompt (tone, style, honorifics...).
    extra_instructions: str = ""


@dataclasses.dataclass
class TranslationReport:
    game_dir: Path
    data_dir: Path
    backup_dir: Optional[Path]
    files_seen: int = 0
    files_parsed: int = 0
    files_written: int = 0
    candidates: int = 0
    unique_texts: int = 0
    translated_now: int = 0
    cache_hits: int = 0
    skipped_files: list[str] = dataclasses.field(default_factory=list)
    parse_errors: list[str] = dataclasses.field(default_factory=list)
    warnings: list[str] = dataclasses.field(default_factory=list)
    report_file: Optional[Path] = None


# ---------------------------------------------------------------------------
# Ruby Marshal reader / patch renderer
# ---------------------------------------------------------------------------


def _to_signed_byte(b: int) -> int:
    return b - 256 if b >= 128 else b


def encode_ruby_long(n: int) -> bytes:
    """Encode a Ruby Marshal integer. Used for translated string byte lengths."""
    if n == 0:
        return b"\x00"
    if 0 < n < 123:
        return bytes([n + 5])
    if -124 < n < 0:
        return bytes([(n - 5) & 0xFF])
    if n > 0:
        parts: list[int] = []
        x = n
        while x:
            parts.append(x & 0xFF)
            x >>= 8
        if len(parts) > 255:
            raise ValueError("integer too large for Marshal length")
        return bytes([len(parts)]) + bytes(parts)

    # Negative fixnum encoding. Not needed for string lengths, but implemented for completeness.
    x = n
    parts = []
    for size in range(1, 9):
        parts = [(x >> (8 * i)) & 0xFF for i in range(size)]
        sign_extended = int.from_bytes(bytes(parts), "little", signed=True)
        if sign_extended == n:
            if size > 127:
                break
            return bytes([(-size) & 0xFF]) + bytes(parts)
    raise ValueError("negative integer too large for Marshal long")


class RubyMarshalParser:
    def __init__(self, data: bytes, source_name: str = "<memory>") -> None:
        self.data = data
        self.source_name = source_name
        self.pos = 0
        self.symbols: list[str] = []
        self.string_nodes: list[MarshalNode] = []

    def parse(self) -> MarshalNode:
        if len(self.data) < 2 or self.data[:2] != b"\x04\x08":
            raise RubyMarshalParseError(f"{self.source_name}: Ruby Marshal 4.8 header not found")
        root = MarshalNode("root", 0, path=())
        self.pos = 2
        child = self._parse_value(())
        root.children.append(child)
        if self.pos != len(self.data):
            raise RubyMarshalParseError(
                f"{self.source_name}: trailing bytes after Marshal object at {self.pos}/{len(self.data)}"
            )
        root.end = len(self.data)
        self._annotate_event_command_context(root)
        return root

    def _eof_check(self, n: int = 1) -> None:
        if self.pos + n > len(self.data):
            raise RubyMarshalParseError(f"{self.source_name}: unexpected EOF at {self.pos}")

    def _read_byte(self) -> int:
        self._eof_check(1)
        b = self.data[self.pos]
        self.pos += 1
        return b

    def _read_long(self) -> int:
        c = _to_signed_byte(self._read_byte())
        if c == 0:
            return 0
        if c > 0:
            if c > 4:
                return c - 5
            self._eof_check(c)
            x = 0
            for i in range(c):
                x |= self._read_byte() << (8 * i)
            return x
        if c < -4:
            return c + 5
        size = -c
        self._eof_check(size)
        x = -1
        for i in range(size):
            b = self._read_byte()
            x &= ~(0xFF << (8 * i))
            x |= b << (8 * i)
        return x

    def _read_raw_bytes(self) -> bytes:
        length = self._read_long()
        if length < 0:
            raise RubyMarshalParseError(f"{self.source_name}: negative byte length at {self.pos}")
        self._eof_check(length)
        b = self.data[self.pos : self.pos + length]
        self.pos += length
        return b

    def _decode_symbol_bytes(self, b: bytes) -> str:
        for enc in ("utf-8", "cp932", "shift_jis", "cp949"):
            try:
                return b.decode(enc)
            except UnicodeDecodeError:
                pass
        return b.decode("latin-1", errors="replace")

    def _decode_text_bytes(self, b: bytes) -> tuple[Optional[str], Optional[str]]:
        if not b:
            return "", "utf-8"
        # RPG Maker VX .rvdata is normally UTF-8; cp932 fallback helps some Japanese dumps.
        for enc in ("utf-8", "cp932", "shift_jis", "cp949"):
            try:
                return b.decode(enc), enc
            except UnicodeDecodeError:
                pass
        return None, None

    def _parse_symbol(self) -> tuple[MarshalNode, str]:
        start = self.pos
        tag = chr(self._read_byte())
        if tag == ":":
            raw = self._read_raw_bytes()
            name = self._decode_symbol_bytes(raw)
            self.symbols.append(name)
            node = MarshalNode("symbol", start, self.pos, value=name)
            return node, name
        if tag == ";":
            idx = self._read_long()
            if idx < 0 or idx >= len(self.symbols):
                raise RubyMarshalParseError(f"{self.source_name}: bad symbol link {idx} at {start}")
            name = self.symbols[idx]
            node = MarshalNode("symbol_link", start, self.pos, value=name)
            return node, name
        raise RubyMarshalParseError(f"{self.source_name}: expected symbol at {start}, got {tag!r}")

    def _parse_value(self, path: tuple[str, ...]) -> MarshalNode:
        start = self.pos
        tag_b = self._read_byte()
        tag = chr(tag_b)

        if tag == "0":
            return MarshalNode("nil", start, self.pos, path=path, value=None)
        if tag == "T":
            return MarshalNode("true", start, self.pos, path=path, value=True)
        if tag == "F":
            return MarshalNode("false", start, self.pos, path=path, value=False)
        if tag == "i":
            val = self._read_long()
            return MarshalNode("fixnum", start, self.pos, path=path, value=val)
        if tag == "l":
            sign = chr(self._read_byte())
            length = self._read_long()
            if length < 0:
                raise RubyMarshalParseError(f"{self.source_name}: negative bignum length at {start}")
            self._eof_check(length * 2)
            raw = self.data[self.pos : self.pos + length * 2]
            self.pos += length * 2
            return MarshalNode("bignum", start, self.pos, path=path, value=(sign, raw))
        if tag == "f":
            raw = self._read_raw_bytes()
            txt = raw.decode("ascii", errors="replace")
            return MarshalNode("float", start, self.pos, path=path, value=txt)
        if tag == '"':
            raw = self._read_raw_bytes()
            text, enc = self._decode_text_bytes(raw)
            node = MarshalNode(
                "string",
                start,
                self.pos,
                path=path,
                text_bytes=raw,
                text=text,
                encoding=enc,
            )
            self.string_nodes.append(node)
            return node
        if tag in (":", ";"):
            # Rewind so _parse_symbol can handle both new and linked symbols consistently.
            self.pos = start
            sym_node, name = self._parse_symbol()
            sym_node.path = path
            return sym_node
        if tag == "[":
            count = self._read_long()
            if count < 0:
                raise RubyMarshalParseError(f"{self.source_name}: negative array length at {start}")
            node = MarshalNode("array", start, path=path)
            for i in range(count):
                child = self._parse_value(path + (f"[{i}]",))
                node.children.append(child)
            node.end = self.pos
            return node
        if tag in ("{", "}"):
            count = self._read_long()
            if count < 0:
                raise RubyMarshalParseError(f"{self.source_name}: negative hash length at {start}")
            node = MarshalNode("hash" if tag == "{" else "hash_default", start, path=path)
            for i in range(count):
                key = self._parse_value(path + (f"{{key{i}}}",))
                # Hash keys are lookup identifiers; translating them breaks script lookups.
                annotate_meta(key, "hash_key", True)
                key_label = self._key_label(key, i)
                val = self._parse_value(path + (f"{{{key_label}}}",))
                node.children.extend([key, val])
            if tag == "}":
                default = self._parse_value(path + ("{default}",))
                node.children.append(default)
            node.end = self.pos
            return node
        if tag == "@":
            idx = self._read_long()
            return MarshalNode("object_link", start, self.pos, path=path, value=idx)
        if tag == "I":
            node = MarshalNode("ivar", start, path=path)
            obj = self._parse_value(path)
            node.children.append(obj)
            count = self._read_long()
            if count < 0:
                raise RubyMarshalParseError(f"{self.source_name}: negative ivar count at {start}")
            for _ in range(count):
                _sym_node, ivar = self._parse_symbol()
                val = self._parse_value(path + (f"<ivar:{ivar}>",))
                node.fields.append((ivar, val))
                node.children.append(val)
            node.end = self.pos
            if obj.typ == "string":
                # Ruby 1.9 (VX Ace) encoding ivars. :E false marks US-ASCII; replacing the
                # payload with non-ASCII bytes requires flipping that flag to true, so keep
                # a handle to the flag node. :encoding "name" strings are metadata, never
                # translation candidates, and force re-encoding of any replacement.
                for field_name, field_val in node.fields:
                    if field_name == "E" and field_val.typ == "false":
                        obj.meta["ascii_flag_node"] = field_val
                    elif field_name == "encoding" and field_val.typ == "string" and field_val.text:
                        obj.meta["ruby_encoding"] = field_val.text
                        field_val.meta["is_encoding_name"] = True
            return node
        if tag == "o":
            node = MarshalNode("object", start, path=path)
            _sym_node, class_name = self._parse_symbol()
            node.class_name = class_name
            count = self._read_long()
            if count < 0:
                raise RubyMarshalParseError(f"{self.source_name}: negative object field count at {start}")
            for _ in range(count):
                _field_sym, ivar = self._parse_symbol()
                child_path = path + (f"{class_name}.{ivar}",)
                child = self._parse_value(child_path)
                node.fields.append((ivar, child))
                node.children.append(child)
            node.end = self.pos
            return node
        if tag == "S":
            node = MarshalNode("struct", start, path=path)
            _sym_node, class_name = self._parse_symbol()
            node.class_name = class_name
            count = self._read_long()
            if count < 0:
                raise RubyMarshalParseError(f"{self.source_name}: negative struct field count at {start}")
            for _ in range(count):
                _field_sym, name = self._parse_symbol()
                child = self._parse_value(path + (f"{class_name}.{name}",))
                node.fields.append((name, child))
                node.children.append(child)
            node.end = self.pos
            return node
        if tag == "C":
            node = MarshalNode("user_class", start, path=path)
            _sym_node, class_name = self._parse_symbol()
            node.class_name = class_name
            obj = self._parse_value(path + (f"<{class_name}>",))
            node.children.append(obj)
            node.end = self.pos
            return node
        if tag == "e":
            node = MarshalNode("extended", start, path=path)
            _sym_node, module_name = self._parse_symbol()
            node.class_name = module_name
            obj = self._parse_value(path + (f"<{module_name}>",))
            node.children.append(obj)
            node.end = self.pos
            return node
        if tag == "U":
            node = MarshalNode("user_marshal", start, path=path)
            _sym_node, class_name = self._parse_symbol()
            node.class_name = class_name
            obj = self._parse_value(path + (f"{class_name}._marshal",))
            node.children.append(obj)
            node.end = self.pos
            return node
        if tag == "u":
            _sym_node, class_name = self._parse_symbol()
            raw = self._read_raw_bytes()
            return MarshalNode("user_defined", start, self.pos, path=path, value=(class_name, raw))
        if tag == "/":
            raw = self._read_raw_bytes()
            options = self._read_byte()
            return MarshalNode("regexp", start, self.pos, path=path, value=(raw, options))
        if tag in ("c", "m", "M"):
            raw = self._read_raw_bytes()
            name = self._decode_symbol_bytes(raw)
            return MarshalNode("class_module", start, self.pos, path=path, value=(tag, name))
        if tag == "d":
            # TYPE_DATA is rare in RPG Maker data. It normally stores a class name and
            # implementation-defined payload. We parse the class symbol; if more data follows,
            # it must be represented by other Marshal values and will be caught by EOF checks.
            _sym_node, class_name = self._parse_symbol()
            return MarshalNode("data", start, self.pos, path=path, class_name=class_name)

        raise RubyMarshalParseError(
            f"{self.source_name}: unsupported Marshal tag {tag!r} / 0x{tag_b:02x} at offset {start}"
        )

    def _key_label(self, key: MarshalNode, i: int) -> str:
        if key.typ == "string" and key.text:
            s = key.text.strip().replace("/", "_")
            return s[:40] or f"value{i}"
        if key.typ in {"symbol", "symbol_link"} and key.value:
            return str(key.value)[:40]
        if key.typ == "fixnum":
            return str(key.value)
        return f"value{i}"

    def _annotate_event_command_context(self, root: MarshalNode) -> None:
        for node in iter_nodes(root):
            if node.typ == "object" and node.class_name == "RPG::EventCommand":
                code = None
                params = None
                for name, child in node.fields:
                    if name == "@code" and child.typ == "fixnum":
                        code = child.value
                    elif name == "@parameters":
                        params = child
                if isinstance(code, int) and params is not None:
                    annotate_meta(params, "event_code", code)


def iter_nodes(node: MarshalNode) -> Iterable[MarshalNode]:
    yield node
    for child in node.children:
        yield from iter_nodes(child)


def annotate_meta(node: MarshalNode, key: str, value: Any) -> None:
    node.meta[key] = value
    for child in node.children:
        annotate_meta(child, key, value)


def render_patched(data: bytes, node: MarshalNode) -> bytes:
    """Render original Marshal bytes with translated string nodes spliced in."""
    if node.typ == "root":
        if not node.is_modified():
            return data
        out = bytearray()
        cursor = node.start
        for child in sorted(node.children, key=lambda c: c.start):
            out += data[cursor : child.start]
            out += render_patched(data, child)
            cursor = child.end
        out += data[cursor : node.end]
        return bytes(out)

    if node.replacement_bytes is not None:
        if node.typ == "string":
            return b'"' + encode_ruby_long(len(node.replacement_bytes)) + node.replacement_bytes
        # Raw splice for non-string nodes, e.g. flipping an :E encoding flag F -> T.
        return node.replacement_bytes

    if not node.is_modified():
        return data[node.start : node.end]

    out = bytearray()
    cursor = node.start
    for child in sorted(node.children, key=lambda c: c.start):
        out += data[cursor : child.start]
        out += render_patched(data, child)
        cursor = child.end
    out += data[cursor : node.end]
    return bytes(out)


# ---------------------------------------------------------------------------
# Candidate detection
# ---------------------------------------------------------------------------


def normalize_path(path: tuple[str, ...]) -> str:
    return "/".join(path)


def contains_excluded_asset_path(path_text: str) -> bool:
    p = path_text.lower()
    # Never translate strings that are likely to be asset identifiers.
    # RPG Maker VX stores audio in RPG::BGM/BGS/ME/SE objects rather than only
    # RPG::AudioFile; v0.1.1 skipped RPG::AudioFile but could still translate
    # System.rvdata sound-effect names, causing errors such as Audio/SE/<translated>.
    excluded_bits = [
        "@character_name",
        "@face_name",
        "@battler_name",
        "@animation_name",
        "@windowskin_name",
        "@title_name",
        "@gameover_name",
        "@battleback_name",
        "@picture_name",
        "@parallax_name",
        "@panorama_name",
        "@fog_name",
        "@filename",
        "@graphic",
        "rpg::movecommand.@parameters",
        "rpg::audiofile.@name",
        "rpg::bgm.@name",
        "rpg::bgs.@name",
        "rpg::me.@name",
        "rpg::se.@name",
        # VX Ace additions: numbered title/battleback graphics and tileset name lists.
        "@title1_name",
        "@title2_name",
        "@battleback1_name",
        "@battleback2_name",
        "@tileset_names",
        "rpg::system.@sounds",
        "rpg::system.@title_bgm",
        "rpg::system.@battle_bgm",
        "rpg::system.@battle_end_me",
        "rpg::system.@gameover_me",
        "rpg::map.@bgm",
        "rpg::map.@bgs",
    ]
    return any(bit in p for bit in excluded_bits)


def contains_internal_name_path(path_text: str) -> bool:
    p = path_text.lower()
    internal_bits = [
        "rpg::system.@switches",
        "rpg::system.@variables",
        "rpg::animation",
        "rpg::area.@name",
    ]
    return any(bit in p for bit in internal_bits)


def is_event_param_path(path_text: str) -> bool:
    return "RPG::EventCommand.@parameters" in path_text


def looks_like_binary_or_asset(text: str) -> bool:
    if not text:
        return True
    if CONTROL_CHARS_RE.search(text):
        return True
    stripped = text.strip()
    if not stripped:
        return True
    if FILE_EXT_RE.search(stripped):
        return True
    asset_probe = TOKEN_PATTERN.sub("", stripped)
    if "\\" in asset_probe:
        # A backslash surviving token-stripping is an unrecognized control code.
        return True
    if "/" in asset_probe and not CJK_RE.search(asset_probe) and re.fullmatch(r"[\w\-./]+", asset_probe):
        # Path-like: slash-separated identifier with no spaces/CJK, e.g. Audio/SE/Cursor.
        # Ordinary text such as "HP/MPを回復" or "Attack/Defense up" must stay translatable.
        return True
    if len(stripped) > 3000:
        # Very large strings are often scripts or compressed-ish payloads.
        return True
    # Mostly gibberish / high symbol ratio.
    useful = sum(1 for ch in stripped if ch.isalnum() or ch.isspace() or CJK_RE.match(ch))
    if len(stripped) >= 8 and useful / max(1, len(stripped)) < 0.35:
        return True
    return False


def should_translate_text(text: str, include_ascii: bool) -> bool:
    stripped = text.strip()
    if looks_like_binary_or_asset(text):
        return False
    if len(stripped) <= 1 and not CJK_RE.search(stripped):
        return False
    if not LETTER_RE.search(stripped):
        return False
    if not include_ascii and not CJK_RE.search(stripped):
        return False
    return True


def should_process_file(file_path: Path, process_all_files: bool) -> bool:
    lower = file_path.name.lower()
    if lower in ALWAYS_SKIP_FILES:
        return False
    if process_all_files:
        return lower.endswith((".rvdata", ".rvdata2"))
    if lower in DEFAULT_SKIP_FILES:
        return False
    return SAFE_FILE_RE.match(file_path.name) is not None


def list_game_data_files(data_dir: Path) -> list[Path]:
    """All VX (.rvdata) and VX Ace (.rvdata2) data files, sorted by name."""
    return sorted([*data_dir.glob("*.rvdata"), *data_dir.glob("*.rvdata2")], key=lambda p: p.name.lower())


def collect_candidates(
    file_path: Path,
    parser: RubyMarshalParser,
    include_ascii: bool,
    include_internal_names: bool,
) -> list[TextCandidate]:
    result: list[TextCandidate] = []
    for node in parser.string_nodes:
        if node.text is None:
            continue
        if node.meta.get("hash_key") or node.meta.get("is_encoding_name"):
            continue
        path_text = normalize_path(node.path)
        if contains_excluded_asset_path(path_text):
            continue
        if not include_internal_names and contains_internal_name_path(path_text):
            continue
        if is_event_param_path(path_text):
            code = node.meta.get("event_code")
            if code not in VISIBLE_EVENT_CODES:
                continue
        if should_translate_text(node.text, include_ascii=include_ascii):
            result.append(TextCandidate(node=node, file_path=file_path, text=node.text, path_text=path_text))
    return result


def candidate_category_label(cand: TextCandidate) -> str:
    """Korean category hint sent to Gemini so each string is translated in context."""
    p = cand.path_text.lower()
    code = cand.node.meta.get("event_code")
    if isinstance(code, int):
        if code in (401, 405):
            return "대사"
        if code in (102, 402):
            return "선택지"
        if code in (320, 324, 325):
            return "이름"
    if ".@name" in p or "@nickname" in p or "@display_name" in p:
        return "이름"
    if "@description" in p:
        return "설명"
    if (
        "words.@" in p
        or "terms.@" in p
        or "@currency_unit" in p
        or "@elements" in p
        or "@skill_types" in p
        or "@weapon_types" in p
        or "@armor_types" in p
    ):
        return "용어"
    return "기타"


# ---------------------------------------------------------------------------
# Gemini translation
# ---------------------------------------------------------------------------


def protect_tokens(text: str) -> tuple[str, dict[str, str]]:
    mapping: dict[str, str] = {}

    def repl(match: re.Match[str]) -> str:
        token = match.group(0)
        placeholder = f"⟦PH{len(mapping)}⟧"
        mapping[placeholder] = token
        return placeholder

    return TOKEN_PATTERN.sub(repl, text), mapping


def restore_tokens(text: str, mapping: dict[str, str]) -> str:
    restored = text
    # Gemini sometimes inserts spaces inside the brackets, swaps bracket styles, or
    # changes case. Try the exact placeholder first, then a tolerant pattern.
    for ph, token in mapping.items():
        if ph in restored:
            restored = restored.replace(ph, token)
            continue
        digits = re.escape(ph[3:-1])  # ⟦PH{n}⟧ -> n
        fuzzy = re.compile(r"[⟦\[\(【]\s*[Pp][Hh]\s*" + digits + r"\s*[⟧\]\)】]")
        restored = fuzzy.sub(lambda _m, _t=token: _t, restored)
    return restored


def tokens_restored_ok(restored: str, mapping: dict[str, str]) -> bool:
    """True if every protected token survived the model round-trip."""
    if not mapping:
        return True
    if "⟦" in restored or "⟧" in restored:
        return False
    needed: dict[str, int] = {}
    for token in mapping.values():
        needed[token] = needed.get(token, 0) + 1
    return all(restored.count(token) >= count for token, count in needed.items())


def restore_outer_whitespace(original: str, translated: str) -> str:
    pre = re.match(r"^\s*", original).group(0)
    suf = re.search(r"\s*$", original).group(0)
    core = translated.strip()
    return f"{pre}{core}{suf}"


def cache_key(model: str, source_lang: str, target_lang: str, source: str) -> str:
    h = hashlib.sha256()
    h.update(model.encode("utf-8"))
    h.update(b"\0")
    h.update(source_lang.encode("utf-8"))
    h.update(b"\0")
    h.update(target_lang.encode("utf-8"))
    h.update(b"\0")
    h.update(source.encode("utf-8"))
    return h.hexdigest()


class TranslationCache:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.data: dict[str, Any] = {"version": 1, "entries": {}}
        if path.exists():
            try:
                self.data = json.loads(path.read_text("utf-8"))
                if "entries" not in self.data:
                    self.data = {"version": 1, "entries": {}}
            except Exception:
                self.data = {"version": 1, "entries": {}}

    def get(self, key: str) -> Optional[str]:
        val = self.data.get("entries", {}).get(key)
        if isinstance(val, dict):
            t = val.get("translated")
            return t if isinstance(t, str) else None
        if isinstance(val, str):
            return val
        return None

    def set(self, key: str, source: str, translated: str) -> None:
        self.data.setdefault("entries", {})[key] = {"source": source, "translated": translated}

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self.path.with_suffix(self.path.suffix + ".tmp")
        tmp.write_text(json.dumps(self.data, ensure_ascii=False, indent=2), "utf-8")
        tmp.replace(self.path)


class GeminiBatchTranslator:
    def __init__(
        self,
        api_key: str,
        model: str,
        source_lang: str,
        target_lang: str,
        log: LogFn = print,
        debug_dir: Optional[Path] = None,
        extra_instructions: str = "",
    ) -> None:
        self.api_key = api_key.strip()
        self.model = model.strip() or DEFAULT_MODEL
        self.source_lang = source_lang.strip() or "auto"
        self.target_lang = target_lang.strip() or "Korean"
        self.log = log
        self.debug_dir = debug_dir
        self.extra_instructions = extra_instructions.strip()
        # source text -> category hint ("대사", "이름", ...); set once per run by translate_game.
        self.categories: dict[str, str] = {}
        # source term -> fixed translation, built from the name pass; injected per batch.
        self.glossary: dict[str, str] = {}
        if not self.api_key:
            raise ValueError("Gemini API 키가 비어 있습니다.")
        try:
            from google import genai  # type: ignore
        except Exception as exc:
            raise RuntimeError(
                "google-genai 패키지가 필요합니다. 설치: python -m pip install -r requirements.txt"
            ) from exc
        self._genai = genai
        self.client = genai.Client(api_key=self.api_key)

    def translate_batch(self, sources: list[str]) -> dict[str, str]:
        """Translate one batch using a compact numbered request.

        v0.1.3 is deliberately tolerant of imperfect Gemini responses. Gemini can
        sometimes return markdown, an array, a truncated JSON object, or one bad
        line inside an otherwise usable response. Instead of stopping the whole
        translation job, this method salvages what it can, retries missing IDs,
        and automatically splits an unparsable batch into smaller sub-batches.
        """
        if not sources:
            return {}

        translated_by_idx: dict[int, str] = {}
        pending = list(range(len(sources)))

        # Round 1: full batch. Rounds 2-3: missing IDs only.
        for round_no in range(1, 4):
            if not pending:
                break
            if round_no > 1:
                shown = ", ".join(str(i + 1) for i in pending[:12])
                suffix = "..." if len(pending) > 12 else ""
                self.log(f"Gemini 응답 누락 {len(pending)}개 재요청: {shown}{suffix}")
                time.sleep(min(2.0, 0.4 * round_no))
            partial = self._translate_resilient_subset(sources, pending)
            translated_by_idx.update(partial)
            pending = [i for i in range(len(sources)) if i not in translated_by_idx]

        # Final rescue: retry each remaining item alone. This is used only for the few
        # IDs that Gemini repeatedly omitted, so it barely affects cost but prevents
        # one bad item from stopping a large translation run.
        if pending:
            self.log(f"누락 항목 {len(pending)}개를 단독으로 최종 재시도합니다.")
            for idx in pending:
                try:
                    partial = self._translate_resilient_subset(sources, [idx])
                    translated_by_idx.update(partial)
                except Exception as exc:
                    self.log(f"단독 재시도 실패 ID {idx + 1}: {str(exc)[:180]}")
                time.sleep(0.15)
            pending = [i for i in pending if i not in translated_by_idx]
            if pending:
                shown = ", ".join(str(i + 1) for i in pending[:12])
                suffix = "..." if len(pending) > 12 else ""
                self.log(f"주의: 최종적으로 번역하지 못한 항목 {len(pending)}개는 이번 실행에서 원문 유지: {shown}{suffix}")

        return {sources[i]: translated_by_idx[i] for i in range(len(sources)) if i in translated_by_idx}

    def _translate_resilient_subset(self, all_sources: list[str], indices: list[int], depth: int = 0) -> dict[int, str]:
        """Translate a subset; split it if the response is unparsable.

        Splitting is cheaper than aborting and restarting the whole job. Cached
        translations are saved after every outer batch, so even if the process is
        stopped later, completed strings are reused on the next run.
        """
        if not indices:
            return {}
        try:
            return self._translate_numbered_subset(all_sources, indices)
        except GeminiParseError as exc:
            msg = str(exc).replace("\n", " ")
            if len(indices) <= 1:
                self.log(f"항목 {indices[0] + 1} 파싱 실패로 원문 유지 예정: {msg[:220]}")
                return {}
            mid = len(indices) // 2
            left = indices[:mid]
            right = indices[mid:]
            if depth == 0:
                self.log(f"Gemini 응답 파싱 실패. 배치를 {len(left)}개/{len(right)}개로 나눠 재시도합니다: {msg[:220]}")
            else:
                self.log(f"부분 배치 파싱 실패. 더 작게 나눠 재시도합니다({len(indices)}개): {msg[:160]}")
            out: dict[int, str] = {}
            time.sleep(min(1.5, 0.25 * (depth + 1)))
            out.update(self._translate_resilient_subset(all_sources, left, depth + 1))
            time.sleep(0.15)
            out.update(self._translate_resilient_subset(all_sources, right, depth + 1))
            return out

    def _translate_numbered_subset(self, all_sources: list[str], indices: list[int]) -> dict[int, str]:
        if not indices:
            return {}

        token_maps: dict[int, dict[str, str]] = {}
        input_lines: list[str] = []
        required_keys: list[str] = []
        local_to_global: dict[int, int] = {}

        for local_no, global_idx in enumerate(indices, 1):
            source = all_sources[global_idx]
            protected, token_map = protect_tokens(source)
            token_maps[local_no] = token_map
            local_to_global[local_no] = global_idx
            required_keys.append(str(local_no))
            # JSON-quoted text keeps one item per line even when the original string
            # contains quotes, backslashes, or line breaks.
            category = self.categories.get(source, "")
            prefix = f"{local_no} [{category}]" if category else str(local_no)
            input_lines.append(f"{prefix}: {json.dumps(protected, ensure_ascii=False)}")

        schema = {
            "type": "object",
            "properties": {key: {"type": "string"} for key in required_keys},
            "required": required_keys,
            "additionalProperties": False,
        }

        system_instruction = (
            "You are a professional game localization engine for RPG Maker VX / VX Ace games. "
            f"Translate every numbered string independently into natural, fluent {self.target_lang} "
            "that reads like an official game localization, not a literal machine translation. "
            "Guidelines: dialogue should sound natural and colloquial for the speaker; item, skill, and enemy names "
            "should be short and game-like; descriptions and system messages should use a concise, consistent register. "
            "For Korean, use natural speech levels in dialogue and plain declarative style (~다/명사형) for "
            "system messages and descriptions; keep honorifics consistent across lines. "
            "Preserve placeholders such as ⟦PH0⟧ exactly, preserve RPG Maker control sequences, "
            "preserve line breaks by using JSON escapes, and do not add explanations or translator notes. "
            "Return compact JSON only. Never use markdown code fences."
        )
        if self.extra_instructions:
            system_instruction += " Additional instructions from the user (follow them): " + self.extra_instructions

        glossary_lines: list[str] = []
        if self.glossary:
            batch_texts = [all_sources[i] for i in indices]
            for term, translated in self.glossary.items():
                if len(glossary_lines) >= 60:
                    break
                if len(term) < 2:
                    continue
                if any(term in text and term != text for text in batch_texts):
                    glossary_lines.append(f"- {json.dumps(term, ensure_ascii=False)} -> {json.dumps(translated, ensure_ascii=False)}")

        src_desc = "the detected source language" if self.source_lang.lower() == "auto" else self.source_lang
        prompt = (
            f"Translate each numbered item from {src_desc} to {self.target_lang}.\n"
            "Each input line looks like `number [category]: \"text\"`. The category is context for you: "
            "대사=dialogue line, 선택지=player choice, 이름=proper noun/name, 설명=description, "
            "용어=system term, 기타=other. Translate each item according to its category.\n"
            "Return exactly one compact JSON object. Keys must be the item numbers as strings. "
            "Values must be the translated strings. Do not omit, merge, split, renumber, or reorder items. "
            "If an item should stay unchanged, return it unchanged. "
            "Do not wrap the result in ```json or any markdown. Escape literal line breaks as \\n inside JSON strings.\n"
        )
        if glossary_lines:
            prompt += (
                "Glossary — when these terms appear inside an item, always use these exact translations:\n"
                + "\n".join(glossary_lines)
                + "\n"
            )
        prompt += f"Required keys: {', '.join(required_keys)}\n\nItems:\n" + "\n".join(input_lines)

        config: dict[str, Any] = {
            "system_instruction": system_instruction,
            "response_mime_type": "application/json",
            "response_json_schema": schema,
            "temperature": 0.1,
            # Gemini 3.1 Flash-Lite supports minimal thinking; this keeps bulk translation low-latency.
            "thinking_config": {"thinking_level": "minimal"},
        }

        response_text = self._call_generate_content(prompt, config)
        try:
            single_source = all_sources[indices[0]] if len(indices) == 1 else None
            parsed_map = self._parse_translation_map(response_text, len(indices), single_source=single_source)
        except Exception as exc:
            preview = self._preview_response(response_text)
            saved = self._save_bad_response(response_text, len(indices))
            suffix = f" / 저장: {saved}" if saved else ""
            raise GeminiParseError(f"Gemini 번역 응답을 파싱할 수 없습니다. 응답 일부: {preview}{suffix}") from exc

        out: dict[int, str] = {}
        for local_no, translated in parsed_map.items():
            global_idx = local_to_global.get(local_no)
            if global_idx is None:
                continue
            token_map = token_maps.get(local_no, {})
            restored = restore_tokens(translated, token_map)
            if not tokens_restored_ok(restored, token_map):
                # A control-code placeholder was dropped or mangled; writing this would
                # break color/name/variable codes in game. Leave it missing so the outer
                # retry rounds request this item again.
                self.log(f"주의: 항목 {local_no} 응답에서 제어 코드가 손상되어 해당 항목을 재요청합니다.")
                continue
            restored = restore_outer_whitespace(all_sources[global_idx], restored)
            out[global_idx] = restored
        return out

    def _call_generate_content(self, prompt: str, config: dict[str, Any]) -> str:
        last_exc: Optional[Exception] = None

        # Try the richest config first, then gracefully fall back if a specific API
        # deployment rejects thinking_config, the JSON schema option, or strict schema keywords.
        configs_to_try: list[dict[str, Any]] = []
        schema = config.get("response_json_schema")
        loose_schema = None
        if isinstance(schema, dict):
            loose_schema = {k: v for k, v in schema.items() if k != "additionalProperties"}
        variants = [config]
        if loose_schema is not None:
            loose_cfg = dict(config)
            loose_cfg["response_json_schema"] = loose_schema
            variants.append(loose_cfg)
        variants.extend([
            {k: v for k, v in config.items() if k != "thinking_config"},
            {k: v for k, v in config.items() if k != "response_json_schema"},
            {k: v for k, v in config.items() if k not in {"thinking_config", "response_json_schema"}},
        ])
        seen_configs: set[str] = set()
        for cfg in variants:
            marker = json.dumps(cfg, ensure_ascii=False, sort_keys=True, default=str)
            if marker not in seen_configs:
                configs_to_try.append(cfg)
                seen_configs.add(marker)

        for cfg in configs_to_try:
            for attempt in range(4):
                try:
                    response = self.client.models.generate_content(
                        model=self.model,
                        contents=prompt,
                        config=cfg,
                    )
                    text = getattr(response, "text", None)
                    if not isinstance(text, str) or not text.strip():
                        raise RuntimeError("Gemini 응답 텍스트가 비어 있습니다.")
                    return text
                except Exception as exc:
                    last_exc = exc
                    msg = str(exc)
                    lower_msg = msg.lower()
                    # If the SDK/API rejects a non-essential config field, immediately
                    # move to the next simpler config instead of wasting retries.
                    if "additionalproperties" in lower_msg and "response_json_schema" in cfg:
                        break
                    if "thinking" in lower_msg and "thinking_config" in cfg:
                        break
                    if ("schema" in lower_msg or "response_json_schema" in lower_msg) and "response_json_schema" in cfg:
                        break
                    if "invalid_argument" in lower_msg and ("thinking_config" in cfg or "response_json_schema" in cfg):
                        break
                    sleep_s = min(12, 1.5 * (2**attempt))
                    self.log(f"Gemini 요청 재시도 {attempt + 1}/4: {msg[:180]}")
                    time.sleep(sleep_s)
        raise RuntimeError(f"Gemini 요청 실패: {last_exc}")

    def _parse_translation_map(
        self, text: str, expected_count: int, single_source: Optional[str] = None
    ) -> dict[int, str]:
        # 1) Strict/normal JSON: dict, {"translations": ...}, or array.
        try:
            parsed = self._parse_json_response(text)
            direct = self._extract_numbered_map(parsed, expected_count)
            if direct:
                return direct
        except Exception:
            pass

        # 2) Loose salvage for truncated objects such as {"1":"...","2":"..."
        loose_pairs = self._parse_loose_json_pairs(text, expected_count)
        if loose_pairs:
            return loose_pairs

        # 3) Safety net if the API ignored JSON mode and returned numbered lines.
        line_map = self._parse_numbered_lines(text, expected_count)
        if line_map:
            return line_map

        # 4) Final singleton fallback. When only one string is retried, the model may
        # return just the translated sentence instead of JSON. Accept that, but only
        # for single-item requests.
        clean = text.strip().lstrip("\ufeff")
        fence = re.match(r"^```(?:json)?\s*(.*?)\s*```$", clean, flags=re.S | re.I)
        if fence:
            clean = fence.group(1).strip()
        if expected_count == 1 and clean and not clean.startswith(("{", "[")):
            # Reject responses that are far longer than the source — those are usually
            # refusals or explanations, not translations, and must not be cached.
            limit = max(80, 3 * len(single_source) + 40) if single_source is not None else 200
            multiline_ok = "\n" not in clean or "\n" in (single_source or "")
            if len(clean) <= limit and multiline_ok:
                return {1: clean}

        raise RuntimeError("Gemini 번역 응답을 파싱할 수 없습니다.")

    def _extract_numbered_map(self, parsed: Any, expected_count: int) -> dict[int, str]:
        # Sometimes the model returns a plain array despite being asked for a JSON object.
        if isinstance(parsed, list):
            out: dict[int, str] = {}
            for i, value in enumerate(parsed, 1):
                if i > expected_count:
                    break
                if isinstance(value, str):
                    out[i] = value
                elif isinstance(value, dict):
                    translated = value.get("text") or value.get("translation") or value.get("translated")
                    if isinstance(translated, str):
                        out[i] = translated
            if out:
                return out

        if not isinstance(parsed, dict):
            return {}

        # Preferred compact format: {"1":"...","2":"..."}
        candidates: list[Any] = [parsed]
        for nested_key in ("translations", "translation", "result", "results", "items", "data", "output", "outputs"):
            if isinstance(parsed.get(nested_key), dict):
                candidates.append(parsed[nested_key])

        for obj in candidates:
            if not isinstance(obj, dict):
                continue
            out: dict[int, str] = {}
            for key, value in obj.items():
                key_str = str(key).strip().strip('"\'')
                if not key_str.isdigit():
                    continue
                local_no = int(key_str)
                if not (1 <= local_no <= expected_count):
                    continue
                if isinstance(value, str):
                    out[local_no] = value
                elif isinstance(value, dict):
                    translated = value.get("text") or value.get("translation") or value.get("translated")
                    if isinstance(translated, str):
                        out[local_no] = translated
            if out:
                return out

        # Backward compatibility with the old shape: {"translations":[{"id":0,"text":"..."}]}
        for key in ("translations", "translation", "items", "results", "result", "data", "output", "outputs"):
            old_items = parsed.get(key)
            if isinstance(old_items, list):
                out: dict[int, str] = {}
                ids: list[int] = []
                for item in old_items:
                    if not isinstance(item, dict):
                        continue
                    idx = item.get("id")
                    translated = item.get("text") or item.get("translation") or item.get("translated")
                    if isinstance(idx, int) and isinstance(translated, str):
                        ids.append(idx)
                zero_based = 0 in ids
                for ordinal, item in enumerate(old_items, 1):
                    if isinstance(item, str):
                        if ordinal <= expected_count:
                            out[ordinal] = item
                        continue
                    if not isinstance(item, dict):
                        continue
                    idx = item.get("id")
                    translated = item.get("text") or item.get("translation") or item.get("translated")
                    if isinstance(idx, int) and isinstance(translated, str):
                        local_no = idx + 1 if zero_based else idx
                    elif isinstance(translated, str):
                        local_no = ordinal
                    else:
                        continue
                    if 1 <= local_no <= expected_count:
                        out[local_no] = translated
                if out:
                    return out
        return {}

    def _parse_numbered_lines(self, text: str, expected_count: int) -> dict[int, str]:
        out: dict[int, str] = {}
        decoder = json.JSONDecoder()
        for raw_line in text.splitlines():
            line = raw_line.strip()
            if not line or line.startswith("```"):
                continue
            # Accept all of these common accidental formats:
            # 1: text
            # 1. text
            # "1": "text",
            # - 1: text
            m = re.match(
                r"^\s*(?:[-*•]\s*)?[\"']?(\d+)[\"']?\s*(?:번)?\s*(?:=>|[:：=]|[.)]|[-–—]|\t)\s*(.*?)\s*$",
                line,
            )
            if not m:
                continue
            local_no = int(m.group(1))
            if not (1 <= local_no <= expected_count):
                continue
            value = m.group(2).strip()
            if value.endswith(","):
                value = value[:-1].rstrip()
            if (value.startswith('"') or value.startswith("'")) and len(value) >= 2:
                try:
                    decoded, _end = decoder.raw_decode(value)
                    if isinstance(decoded, str):
                        value = decoded
                    else:
                        value = str(decoded)
                except Exception:
                    if (value.startswith('"') and value.endswith('"')) or (value.startswith("'") and value.endswith("'")):
                        value = value[1:-1]
            out[local_no] = value
        return out

    def _parse_loose_json_pairs(self, text: str, expected_count: int) -> dict[int, str]:
        out: dict[int, str] = {}
        # Captures valid JSON-style string pairs even if the surrounding object is
        # incomplete/truncated. The value part allows escaped quotes/backslashes.
        pair_re = re.compile(r'(?<!\\)["\'](\d+)["\']\s*:\s*"((?:\\.|[^"\\])*)"', re.S)
        for m in pair_re.finditer(text):
            local_no = int(m.group(1))
            if not (1 <= local_no <= expected_count):
                continue
            raw_val = m.group(2)
            try:
                value = json.loads('"' + raw_val + '"')
            except Exception:
                value = raw_val.replace('\\n', '\n').replace('\\"', '"').replace('\\\\', '\\')
            out[local_no] = value
        return out

    def _parse_json_response(self, text: str) -> Any:
        stripped = text.strip()
        # Remove simple markdown fences when JSON mode was ignored.
        fence = re.match(r"^```(?:json)?\s*(.*?)\s*```$", stripped, flags=re.S | re.I)
        if fence:
            stripped = fence.group(1).strip()
        try:
            return json.loads(stripped)
        except json.JSONDecodeError:
            pass

        # Try to raw-decode from each likely JSON start. This is safer than a greedy
        # \{.*\} regex because translated strings can themselves contain braces.
        decoder = json.JSONDecoder()
        for start, ch in enumerate(stripped):
            if ch not in "[{":
                continue
            try:
                val, _end = decoder.raw_decode(stripped[start:])
                if isinstance(val, (dict, list)):
                    return val
            except json.JSONDecodeError:
                continue
        raise RuntimeError("Gemini JSON 응답을 파싱할 수 없습니다.")

    def _save_bad_response(self, text: str, expected_count: int) -> str:
        if self.debug_dir is None:
            return ""
        try:
            self.debug_dir.mkdir(parents=True, exist_ok=True)
            stamp = _dt.datetime.now().strftime("%Y%m%d_%H%M%S_%f")
            digest = hashlib.sha1(text.encode("utf-8", errors="replace")).hexdigest()[:10]
            path = self.debug_dir / f"bad_response_{stamp}_{expected_count}items_{digest}.txt"
            path.write_text(text, "utf-8", errors="replace")
            return str(path)
        except Exception:
            return ""

    def _preview_response(self, text: str, limit: int = 500) -> str:
        preview = text.strip().replace("\r", "\\r").replace("\n", "\\n")
        if len(preview) > limit:
            preview = preview[:limit] + "..."
        return preview


# ---------------------------------------------------------------------------
# Main workflow
# ---------------------------------------------------------------------------


def make_batches(items: list[str], max_items: int, max_chars: int) -> list[list[str]]:
    batches: list[list[str]] = []
    current: list[str] = []
    chars = 0
    for text in items:
        cost = len(text) + 20
        if current and (len(current) >= max_items or chars + cost > max_chars):
            batches.append(current)
            current = []
            chars = 0
        current.append(text)
        chars += cost
    if current:
        batches.append(current)
    return batches


def validate_config(config: TranslatorConfig) -> tuple[Path, Path]:
    exe = Path(config.exe_path).expanduser().resolve()
    if not exe.exists() or exe.suffix.lower() != ".exe":
        raise FileNotFoundError("RPG Maker VX Game.exe 파일을 선택해야 합니다.")
    game_dir = exe.parent
    data_dir = game_dir / "Data"
    if not data_dir.exists() or not data_dir.is_dir():
        raise FileNotFoundError(f"Data 폴더를 찾을 수 없습니다: {data_dir}")
    return game_dir, data_dir


def create_backup(data_dir: Path, log: LogFn) -> Path:
    stamp = _dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_dir = data_dir.parent / f"Data_backup_before_gemini_{stamp}"
    shutil.copytree(data_dir, backup_dir)
    log(f"백업 생성: {backup_dir}")
    return backup_dir


def find_latest_backup(game_dir: Path) -> Optional[Path]:
    backups = [p for p in game_dir.glob("Data_backup_before_gemini_*") if p.is_dir()]
    if not backups:
        return None
    return max(backups, key=lambda p: p.name)


def restore_latest_backup(exe_path: Path, log: LogFn = print, backup_dir: Optional[Path] = None) -> Path:
    exe = Path(exe_path).expanduser().resolve()
    if not exe.exists() or exe.suffix.lower() != ".exe":
        raise FileNotFoundError("복원할 게임의 Game.exe 파일을 선택해야 합니다.")
    game_dir = exe.parent
    data_dir = game_dir / "Data"
    latest = Path(backup_dir).expanduser().resolve() if backup_dir else find_latest_backup(game_dir)
    if latest is None or not latest.exists() or not latest.is_dir():
        raise FileNotFoundError("Data_backup_before_gemini_* 백업 폴더를 찾을 수 없습니다.")
    stamp = _dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    if data_dir.exists():
        keep_dir = game_dir / f"Data_before_restore_{stamp}"
        if keep_dir.exists():
            raise FileExistsError(f"복원 임시 폴더가 이미 있습니다: {keep_dir}")
        data_dir.rename(keep_dir)
        log(f"현재 Data 보관: {keep_dir}")
    shutil.copytree(latest, data_dir)
    log(f"백업 복원 완료: {latest} -> {data_dir}")
    return latest


def find_gemini_backup_dirs(game_dir: Path) -> list[Path]:
    return sorted(
        [p for p in game_dir.glob("Data_backup_before_gemini_*") if p.is_dir()],
        key=lambda p: p.name,
    )


def _asset_node_groups(parser: RubyMarshalParser) -> dict[str, list[MarshalNode]]:
    groups: dict[str, list[MarshalNode]] = {}
    for node in parser.string_nodes:
        if node.text is None:
            continue
        path_text = normalize_path(node.path)
        if contains_excluded_asset_path(path_text):
            groups.setdefault(path_text, []).append(node)
    return groups


def repair_asset_references(
    exe_path: Path,
    backup_dir: Optional[Path] = None,
    log: LogFn = print,
) -> tuple[int, int, Optional[Path]]:
    """Restore asset filename strings from a pre-translation Data backup.

    This keeps already-translated dialogue where possible, but restores strings such
    as Audio/SE names, BGM names, character graphic names, face graphic names,
    windowskin names, and similar asset identifiers from the backup.
    """
    exe = Path(exe_path).expanduser().resolve()
    if not exe.exists() or exe.suffix.lower() != ".exe":
        raise FileNotFoundError("자산명을 복구할 게임의 Game.exe 파일을 선택해야 합니다.")
    game_dir = exe.parent
    data_dir = game_dir / "Data"
    if not data_dir.exists() or not data_dir.is_dir():
        raise FileNotFoundError(f"Data 폴더를 찾을 수 없습니다: {data_dir}")

    if backup_dir is None:
        backups = find_gemini_backup_dirs(game_dir)
        if not backups:
            raise FileNotFoundError(
                "Data_backup_before_gemini_* 백업 폴더를 찾을 수 없습니다. "
                "백업 폴더가 있으면 --backup-dir 로 직접 지정하세요."
            )
        # The oldest gemini backup is normally the untouched original Data folder.
        source_backup = backups[0]
    else:
        source_backup = Path(backup_dir).expanduser().resolve()
        if not source_backup.exists() or not source_backup.is_dir():
            raise FileNotFoundError(f"백업 폴더를 찾을 수 없습니다: {source_backup}")

    log(f"자산명 복구 기준 백업: {source_backup}")

    parsed_to_write: list[tuple[Path, bytes, MarshalNode, int]] = []
    restored_nodes = 0

    for current_file in list_game_data_files(data_dir):
        backup_file = source_backup / current_file.name
        if not backup_file.exists():
            continue
        try:
            cur_data = current_file.read_bytes()
            bak_data = backup_file.read_bytes()
            cur_parser = RubyMarshalParser(cur_data, current_file.name)
            bak_parser = RubyMarshalParser(bak_data, backup_file.name)
            cur_root = cur_parser.parse()
            bak_parser.parse()
            cur_groups = _asset_node_groups(cur_parser)
            bak_groups = _asset_node_groups(bak_parser)
            changed_here = 0
            for path_text, cur_nodes in cur_groups.items():
                bak_nodes = bak_groups.get(path_text, [])
                if not bak_nodes:
                    continue
                if len(cur_nodes) != len(bak_nodes):
                    log(
                        f"주의: {current_file.name} {path_text} 개수 차이 "
                        f"현재 {len(cur_nodes)}개 / 백업 {len(bak_nodes)}개. 가능한 만큼만 복구합니다."
                    )
                for cur_node, bak_node in zip(cur_nodes, bak_nodes):
                    if bak_node.text_bytes is None:
                        continue
                    if cur_node.text_bytes != bak_node.text_bytes:
                        cur_node.replacement_bytes = bak_node.text_bytes
                        changed_here += 1
            if changed_here:
                parsed_to_write.append((current_file, cur_data, cur_root, changed_here))
                restored_nodes += changed_here
                log(f"복구 예정: {current_file.name} - 자산명 {changed_here}개")
        except Exception as exc:
            log(f"복구 스캔 건너뜀: {current_file.name}: {exc}")

    if not parsed_to_write:
        log("복구할 자산명 변경이 없습니다.")
        return 0, 0, None

    safety_backup = data_dir.parent / f"Data_backup_before_asset_repair_{_dt.datetime.now().strftime('%Y%m%d_%H%M%S')}"
    shutil.copytree(data_dir, safety_backup)
    log(f"복구 전 현재 Data 백업 생성: {safety_backup}")

    for file_path, cur_data, cur_root, changed_here in parsed_to_write:
        patched = render_patched(cur_data, cur_root)
        tmp_path = file_path.with_suffix(file_path.suffix + ".tmp")
        tmp_path.write_bytes(patched)
        tmp_path.replace(file_path)
        log(f"복구 저장 완료: {file_path.name} - {changed_here}개")

    files_changed = len(parsed_to_write)
    log(f"자산명 복구 완료: 파일 {files_changed}개, 문자열 {restored_nodes}개")
    return files_changed, restored_nodes, safety_backup


def write_report(report: TranslationReport, config: TranslatorConfig) -> Path:
    stamp = _dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    path = report.game_dir / f"rvx_gemini_translation_report_{stamp}.txt"
    lines = [
        f"{APP_NAME} {APP_VERSION}",
        f"Time: {_dt.datetime.now().isoformat(timespec='seconds')}",
        f"Game dir: {report.game_dir}",
        f"Data dir: {report.data_dir}",
        f"Model: {config.model}",
        f"Source: {config.source_lang}",
        f"Target: {config.target_lang}",
        f"Dry run: {config.dry_run}",
        f"Backup dir: {report.backup_dir}",
        "",
        f"Files seen: {report.files_seen}",
        f"Files parsed: {report.files_parsed}",
        f"Files written: {report.files_written}",
        f"Candidates: {report.candidates}",
        f"Unique texts: {report.unique_texts}",
        f"Cache hits: {report.cache_hits}",
        f"Translated now: {report.translated_now}",
    ]
    if report.skipped_files:
        lines += ["", "Skipped files:"] + [f"- {x}" for x in report.skipped_files]
    if report.parse_errors:
        lines += ["", "Parse errors:"] + [f"- {x}" for x in report.parse_errors]
    if report.warnings:
        lines += ["", "Warnings:"] + [f"- {x}" for x in report.warnings]
    path.write_text("\n".join(lines), "utf-8")
    return path


def translate_game(
    config: TranslatorConfig,
    log: LogFn = print,
    progress: Optional[ProgressFn] = None,
    cancel: Optional[threading.Event] = None,
) -> TranslationReport:
    def _progress(phase: str, cur: int, total: int, detail: str = "") -> None:
        if progress is not None:
            progress(phase, cur, total, detail)

    def _check_cancel() -> None:
        if cancel is not None and cancel.is_set():
            raise TranslationCancelled("사용자가 작업을 중지했습니다.")

    game_dir, data_dir = validate_config(config)
    report = TranslationReport(game_dir=game_dir, data_dir=data_dir, backup_dir=None)

    rvdata_files = list_game_data_files(data_dir)
    report.files_seen = len(rvdata_files)
    if not rvdata_files:
        raise FileNotFoundError(f".rvdata/.rvdata2 파일이 없습니다: {data_dir}")

    selected_files: list[Path] = []
    for f in rvdata_files:
        if should_process_file(f, config.process_all_files):
            selected_files.append(f)
        else:
            report.skipped_files.append(f.name)
    if not selected_files:
        raise RuntimeError("처리할 .rvdata/.rvdata2 파일이 없습니다. '모든 데이터 파일 처리' 옵션을 켜 보세요.")

    log(f"처리 대상 파일: {len(selected_files)}개 / 전체 {len(rvdata_files)}개")

    parsed_docs: list[tuple[Path, bytes, MarshalNode, list[TextCandidate]]] = []
    all_candidates: list[TextCandidate] = []

    for fi, f in enumerate(selected_files, 1):
        _check_cancel()
        _progress("scan", fi, len(selected_files), f.name)
        try:
            data = f.read_bytes()
            parser = RubyMarshalParser(data, f.name)
            root = parser.parse()
            candidates = collect_candidates(
                file_path=f,
                parser=parser,
                include_ascii=config.include_ascii,
                include_internal_names=config.include_internal_names,
            )
            parsed_docs.append((f, data, root, candidates))
            all_candidates.extend(candidates)
            report.files_parsed += 1
            log(f"스캔 완료: {f.name} - 후보 {len(candidates)}개")
        except Exception as exc:
            msg = f"{f.name}: {exc}"
            report.parse_errors.append(msg)
            log(f"파싱 건너뜀: {msg}")

    report.candidates = len(all_candidates)
    if not all_candidates:
        report.report_file = write_report(report, config)
        log("번역 후보가 없습니다.")
        return report

    unique_sources: list[str] = []
    seen: set[str] = set()
    categories: dict[str, str] = {}
    for cand in all_candidates:
        if cand.text not in seen:
            unique_sources.append(cand.text)
            seen.add(cand.text)
        if cand.text not in categories:
            categories[cand.text] = candidate_category_label(cand)
    report.unique_texts = len(unique_sources)
    log(f"번역 후보: 전체 {report.candidates}개, 고유 문자열 {report.unique_texts}개")

    cache_path = game_dir / ".rvx_gemini_cache" / "translation_cache.json"
    cache = TranslationCache(cache_path)
    translations: dict[str, str] = {}
    to_translate: list[str] = []

    for text in unique_sources:
        key = cache_key(config.model, config.source_lang, config.target_lang, text)
        cached = cache.get(key)
        if cached is not None:
            translations[text] = cached
            report.cache_hits += 1
        else:
            to_translate.append(text)

    log(f"캐시 적중: {report.cache_hits}개, 새 요청: {len(to_translate)}개")

    if to_translate and config.dry_run:
        log("드라이런: Gemini 요청과 파일 쓰기를 수행하지 않습니다.")
    elif to_translate:
        translator = GeminiBatchTranslator(
            api_key=config.api_key,
            model=config.model,
            source_lang=config.source_lang,
            target_lang=config.target_lang,
            log=log,
            debug_dir=game_dir / ".rvx_gemini_cache" / "bad_responses",
            extra_instructions=config.extra_instructions,
        )
        translator.categories = categories

        # Two passes: names/proper nouns first, then everything else with the resulting
        # glossary injected, so the same character/item name is translated identically
        # inside dialogue and descriptions.
        name_sources = [s for s in to_translate if categories.get(s) == "이름"]
        other_sources = [s for s in to_translate if categories.get(s) != "이름"]
        name_batches = make_batches(name_sources, max_items=config.batch_size, max_chars=config.batch_chars)
        other_batches = make_batches(other_sources, max_items=config.batch_size, max_chars=config.batch_chars)
        total_batches = len(name_batches) + len(other_batches)
        log(f"Gemini 요청 방식: 번호 매핑 묶음 요청 / 배치당 최대 {config.batch_size}개, 약 {config.batch_chars}자")

        bi = 0

        def run_batch(batch: list[str]) -> None:
            nonlocal bi
            bi += 1
            # Checked before each request: the previous batch's cache.save() has already
            # run, so a cancel here loses nothing and the next run resumes from cache.
            _check_cancel()
            _progress("translate", bi - 1, total_batches, f"배치 {bi}/{total_batches} ({len(batch)}개)")
            log(f"Gemini 번역 중: 배치 {bi}/{total_batches} - {len(batch)}개")
            batch_result = translator.translate_batch(batch)
            if len(batch_result) < len(batch):
                log(f"주의: 배치 {bi}에서 {len(batch) - len(batch_result)}개 문자열은 번역하지 못해 원문으로 유지됩니다. 재실행하면 캐시된 항목은 건너뛰고 남은 항목만 다시 시도합니다.")
            for src, dst in batch_result.items():
                translations[src] = dst
                key = cache_key(config.model, config.source_lang, config.target_lang, src)
                cache.set(key, src, dst)
                report.translated_now += 1
            cache.save()
            _progress("translate", bi, total_batches, f"배치 {bi}/{total_batches} 완료")
            if config.request_delay > 0 and bi < total_batches:
                if cancel is not None:
                    cancel.wait(config.request_delay)
                else:
                    time.sleep(config.request_delay)

        if name_batches:
            log(f"1단계: 이름/고유명사 {len(name_sources)}개 번역 (배치 {len(name_batches)}개)")
        for batch in name_batches:
            run_batch(batch)

        # Cached name translations also feed the glossary, so re-runs stay consistent.
        glossary: dict[str, str] = {}
        for src_text, category in categories.items():
            if category != "이름":
                continue
            translated = translations.get(src_text)
            if translated and translated != src_text:
                glossary[src_text.strip()] = translated.strip()
        translator.glossary = glossary
        if glossary:
            log(f"용어집 구성 완료: {len(glossary)}개 항목 (이후 배치에 일관성 적용)")

        if other_batches:
            log(f"2단계: 대사/설명/용어 {len(other_sources)}개 번역 (배치 {len(other_batches)}개)")
        for batch in other_batches:
            run_batch(batch)

    # Apply translations to nodes. UTF-8 by default; strings carrying an explicit Ruby
    # :encoding ivar are re-encoded to that encoding, and US-ASCII (:E false) strings that
    # become non-ASCII get their flag flipped to true so Ruby 1.9 (VX Ace) loads them.
    applied = 0
    non_utf8_sources = 0
    for cand in all_candidates:
        translated = translations.get(cand.text)
        if translated is None:
            continue
        if translated == cand.text:
            continue
        ruby_enc = cand.node.meta.get("ruby_encoding")
        try:
            if ruby_enc:
                codec = RUBY_ENCODING_ALIASES.get(ruby_enc.lower(), ruby_enc)
                encoded = translated.encode(codec)
            else:
                encoded = translated.encode("utf-8")
        except (UnicodeEncodeError, LookupError) as exc:
            report.warnings.append(f"인코딩 실패로 건너뜀: {cand.file_path.name} {cand.path_text}: {exc}")
            continue
        cand.node.replacement_bytes = encoded
        flag_node = cand.node.meta.get("ascii_flag_node")
        if flag_node is not None and any(b > 127 for b in encoded):
            flag_node.replacement_bytes = b"T"
        if not ruby_enc and cand.node.encoding not in (None, "utf-8"):
            non_utf8_sources += 1
        applied += 1
    if non_utf8_sources:
        log(
            f"주의: 원본 인코딩이 UTF-8이 아닌 문자열 {non_utf8_sources}개를 UTF-8로 저장합니다. "
            "게임 화면에서 글자가 깨지면 백업을 복원하세요."
        )

    log(f"적용할 문자열: {applied}개")

    if config.dry_run:
        report.report_file = write_report(report, config)
        log(f"드라이런 보고서: {report.report_file}")
        return report

    # Last cancellation point: once writing starts, the loop runs to completion so the
    # Data folder is never left half-patched (a fresh backup exists by then anyway).
    _check_cancel()

    if applied > 0:
        report.backup_dir = create_backup(data_dir, log)

    modified_docs = [(f, data, root) for f, data, root, _cands in parsed_docs if root.is_modified()]
    for wi, (f, data, root) in enumerate(modified_docs, 1):
        _progress("save", wi, len(modified_docs), f.name)
        patched = render_patched(data, root)
        # Atomic write: a crash or forced exit mid-save must never leave a truncated file.
        tmp_path = f.with_suffix(f.suffix + ".tmp")
        tmp_path.write_bytes(patched)
        tmp_path.replace(f)
        report.files_written += 1
        log(f"저장 완료: {f.name}")

    report.report_file = write_report(report, config)
    log(f"완료. 보고서: {report.report_file}")
    return report


# ---------------------------------------------------------------------------
# App icon (generated with stdlib only; no image dependencies)
# ---------------------------------------------------------------------------


def _icon_render_rgba(size: int) -> bytes:
    """Render the app icon (blue rounded square + white speech bubble) as RGBA."""
    ss = 4  # supersampling factor for smooth edges
    big = size * ss

    def rounded_rect_dist(x: float, y: float, cx: float, cy: float, hw: float, hh: float, r: float) -> float:
        dx = abs(x - cx) - (hw - r)
        dy = abs(y - cy) - (hh - r)
        ax = dx if dx > 0 else 0.0
        ay = dy if dy > 0 else 0.0
        outside = (ax * ax + ay * ay) ** 0.5
        inside = min(max(dx, dy), 0.0)
        return outside + inside - r

    def in_triangle(x: float, y: float, p1: tuple, p2: tuple, p3: tuple) -> bool:
        def sign(a: tuple, b: tuple, c: tuple) -> float:
            return (a[0] - c[0]) * (b[1] - c[1]) - (b[0] - c[0]) * (a[1] - c[1])

        d1 = sign((x, y), p1, p2)
        d2 = sign((x, y), p2, p3)
        d3 = sign((x, y), p3, p1)
        has_neg = (d1 < 0) or (d2 < 0) or (d3 < 0)
        has_pos = (d1 > 0) or (d2 > 0) or (d3 > 0)
        return not (has_neg and has_pos)

    top = (0x5B, 0x8C, 0xFF)
    bottom = (0x2F, 0x5B, 0xD0)
    dot = (0x3B, 0x6E, 0xF5)
    tail = ((0.36, 0.58), (0.54, 0.58), (0.40, 0.78))

    # Accumulate premultiplied color per output pixel to avoid dark fringes.
    out = bytearray(size * size * 4)
    for py in range(size):
        for px_i in range(size):
            r_acc = g_acc = b_acc = a_acc = 0.0
            for sy in range(ss):
                for sx in range(ss):
                    x = (px_i * ss + sx + 0.5) / big
                    y = (py * ss + sy + 0.5) / big
                    if rounded_rect_dist(x, y, 0.5, 0.5, 0.47, 0.47, 0.20) > 0:
                        continue
                    t = min(1.0, max(0.0, y))
                    cr = top[0] + (bottom[0] - top[0]) * t
                    cg = top[1] + (bottom[1] - top[1]) * t
                    cb = top[2] + (bottom[2] - top[2]) * t
                    bubble = rounded_rect_dist(x, y, 0.5, 0.42, 0.30, 0.19, 0.11) <= 0
                    if bubble or in_triangle(x, y, *tail):
                        cr = cg = cb = 255.0
                        if bubble:
                            for dot_x in (0.38, 0.50, 0.62):
                                ddx = x - dot_x
                                ddy = y - 0.42
                                if ddx * ddx + ddy * ddy <= 0.0475 * 0.0475:
                                    cr, cg, cb = float(dot[0]), float(dot[1]), float(dot[2])
                                    break
                    r_acc += cr
                    g_acc += cg
                    b_acc += cb
                    a_acc += 255.0
            n = ss * ss
            a = a_acc / n
            i = (py * size + px_i) * 4
            if a_acc > 0:
                # Straight (non-premultiplied) average over covered subsamples.
                out[i] = min(255, round(r_acc * 255.0 / a_acc))
                out[i + 1] = min(255, round(g_acc * 255.0 / a_acc))
                out[i + 2] = min(255, round(b_acc * 255.0 / a_acc))
                out[i + 3] = min(255, round(a))
    return bytes(out)


def _encode_png(width: int, height: int, rgba: bytes) -> bytes:
    def chunk(typ: bytes, data: bytes) -> bytes:
        payload = typ + data
        return struct.pack(">I", len(data)) + payload + struct.pack(">I", zlib.crc32(payload) & 0xFFFFFFFF)

    raw = b"".join(b"\x00" + rgba[y * width * 4 : (y + 1) * width * 4] for y in range(height))
    return (
        b"\x89PNG\r\n\x1a\n"
        + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0))
        + chunk(b"IDAT", zlib.compress(raw, 9))
        + chunk(b"IEND", b"")
    )


def _encode_ico(images: list[tuple[int, bytes]]) -> bytes:
    """Pack (size, rgba) images into an .ico. PNG entry for 256px, BMP for smaller."""
    blobs: list[bytes] = []
    for size, rgba in images:
        if size >= 256:
            blobs.append(_encode_png(size, size, rgba))
            continue
        header = struct.pack("<IiiHHIIiiII", 40, size, size * 2, 1, 32, 0, size * size * 4, 0, 0, 0, 0)
        rows: list[bytes] = []
        for y in range(size - 1, -1, -1):
            row = rgba[y * size * 4 : (y + 1) * size * 4]
            bgra = bytearray(len(row))
            bgra[0::4] = row[2::4]
            bgra[1::4] = row[1::4]
            bgra[2::4] = row[0::4]
            bgra[3::4] = row[3::4]
            rows.append(bytes(bgra))
        mask_row_len = ((size + 31) // 32) * 4
        mask = b"\x00" * (mask_row_len * size)
        blobs.append(header + b"".join(rows) + mask)

    out = struct.pack("<HHH", 0, 1, len(images))
    offset = 6 + 16 * len(images)
    for (size, _), blob in zip(images, blobs):
        dim = 0 if size >= 256 else size
        out += struct.pack("<BBBBHHII", dim, dim, 0, 0, 1, 32, len(blob), offset)
        offset += len(blob)
    return out + b"".join(blobs)


_ICON_CACHE: dict[str, bytes] = {}


def app_icon_ico_bytes(sizes: tuple[int, ...] = (16, 32, 48)) -> bytes:
    """Small sizes render instantly; 256 (exe icon) is only worth it at build time."""
    key = "ico" + ",".join(map(str, sizes))
    cached = _ICON_CACHE.get(key)
    if cached is None:
        cached = _encode_ico([(s, _icon_render_rgba(s)) for s in sizes])
        _ICON_CACHE[key] = cached
    return cached


def app_icon_png_base64(size: int = 64) -> str:
    key = f"png{size}"
    cached = _ICON_CACHE.get(key)
    if cached is None:
        cached = base64.b64encode(_encode_png(size, size, _icon_render_rgba(size)))
        _ICON_CACHE[key] = cached
    return cached.decode("ascii")


def write_icon_file(path: Path) -> Path:
    path = Path(path)
    if path.parent != Path("."):
        path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(app_icon_ico_bytes(sizes=(16, 32, 48, 256)))
    return path


# ---------------------------------------------------------------------------
# GUI settings persistence
# ---------------------------------------------------------------------------


def settings_path() -> Path:
    base = os.environ.get("APPDATA") or str(Path.home())
    return Path(base) / "RVXGeminiTranslator" / "settings.json"


def load_settings() -> dict[str, Any]:
    try:
        data = json.loads(settings_path().read_text("utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def save_settings(data: dict[str, Any]) -> None:
    try:
        path = settings_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), "utf-8")
        tmp.replace(path)
    except OSError:
        pass


# ---------------------------------------------------------------------------
# GUI
# ---------------------------------------------------------------------------


# tkinter is imported lazily so CLI-only runs never load it (see _import_tkinter).
tk: Any = None
ttk: Any = None
filedialog: Any = None
messagebox: Any = None
scrolledtext: Any = None
tkfont: Any = None

_UI_BG = "#eef1f6"
_UI_SURFACE = "#ffffff"
_UI_BORDER = "#d4dae3"
_UI_ACCENT = "#3b6ef5"
_UI_ACCENT_HOVER = "#2f5bd0"
_UI_ACCENT_DOWN = "#2a51ba"
_UI_TEXT = "#1f2328"
_UI_MUTED = "#68707c"

_LOG_COLORS = {
    "err": "#d1242f",
    "warn": "#9a6700",
    "ok": "#1a7f37",
    "info": _UI_TEXT,
    "ts": "#9aa1ab",
}


def _import_tkinter() -> None:
    global tk, ttk, filedialog, messagebox, scrolledtext, tkfont
    import tkinter as _tk
    import tkinter.font as _tkfont
    from tkinter import filedialog as _fd
    from tkinter import messagebox as _mb
    from tkinter import scrolledtext as _st
    from tkinter import ttk as _ttk

    tk, ttk, filedialog, messagebox, scrolledtext, tkfont = _tk, _ttk, _fd, _mb, _st, _tkfont


def _enable_windows_dpi_awareness() -> None:
    """Must run before tk.Tk() so text renders crisply on high-DPI displays."""
    if sys.platform != "win32":
        return
    try:
        import ctypes

        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(2)
        except Exception:
            ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass


def classify_log(msg: str) -> str:
    if msg.startswith("오류") or "실패" in msg:
        return "err"
    if msg.startswith("주의") or "건너뜀" in msg or "재시도" in msg or "누락" in msg or "중지" in msg:
        return "warn"
    if "완료" in msg or "백업 생성" in msg or "복원" in msg:
        return "ok"
    return "info"


class _Tooltip:
    def __init__(self, widget: Any, text: str, wraplength: int = 340) -> None:
        self.widget = widget
        self.text = text
        self.wraplength = wraplength
        self.tip: Any = None
        self.after_id: Any = None
        widget.bind("<Enter>", self._schedule, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonPress>", self._hide, add="+")

    def _schedule(self, _event: Any = None) -> None:
        self._cancel()
        self.after_id = self.widget.after(450, self._show)

    def _cancel(self) -> None:
        if self.after_id is not None:
            try:
                self.widget.after_cancel(self.after_id)
            except Exception:
                pass
            self.after_id = None

    def _show(self) -> None:
        if self.tip is not None:
            return
        try:
            x = self.widget.winfo_rootx() + 14
            y = self.widget.winfo_rooty() + self.widget.winfo_height() + 6
            tip = tk.Toplevel(self.widget)
            tip.wm_overrideredirect(True)
            tip.wm_geometry(f"+{x}+{y}")
            tk.Label(
                tip,
                text=self.text,
                justify="left",
                wraplength=self.wraplength,
                background="#22272e",
                foreground="#f0f3f6",
                padx=9,
                pady=6,
            ).pack()
            self.tip = tip
        except Exception:
            # The widget/window can be destroyed between scheduling and firing.
            self.tip = None

    def _hide(self, _event: Any = None) -> None:
        self._cancel()
        if self.tip is not None:
            try:
                self.tip.destroy()
            except Exception:
                pass
            self.tip = None


class TranslatorApp:
    _PROGRESS_SPANS = {"scan": (0.0, 10.0), "translate": (10.0, 85.0), "save": (95.0, 5.0)}
    _PHASE_NAMES = {"scan": "스캔 중", "translate": "번역 중", "save": "저장 중"}

    def __init__(self) -> None:
        self.root = tk.Tk()
        self.root.withdraw()  # hide until layout is done to avoid flicker
        self.root.title(f"{APP_NAME} {APP_VERSION}")

        self.scale = max(1.0, self.root.winfo_fpixels("1i") / 96.0)
        self.q: "queue.Queue[tuple[str, Any]]" = queue.Queue()
        self.worker: Optional[threading.Thread] = None
        self.cancel_event = threading.Event()
        self.job_kind = ""
        self._job_t0 = 0.0
        self._elapsed_after: Any = None
        self._icon_img: Any = None

        self.exe_var = tk.StringVar()
        self.api_var = tk.StringVar()
        self.model_var = tk.StringVar(value=DEFAULT_MODEL)
        self.source_var = tk.StringVar(value="auto")
        self.target_var = tk.StringVar(value="Korean")
        self.include_ascii_var = tk.BooleanVar(value=True)
        self.internal_var = tk.BooleanVar(value=False)
        self.all_files_var = tk.BooleanVar(value=False)
        self.dry_run_var = tk.BooleanVar(value=False)
        self.batch_size_var = tk.StringVar(value="60")
        self.batch_chars_var = tk.StringVar(value="10000")
        self.save_api_var = tk.BooleanVar(value=False)
        self._api_hidden = True

        self._setup_style()
        self._setup_icon()
        self._build_ui()
        self._load_settings()

        for var in (self.exe_var, self.api_var, self.dry_run_var):
            var.trace_add("write", self._update_start_state)
        self._update_start_state()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.after(100, self._poll_queue)

        self.append_log(
            "주의: 반드시 합법적으로 수정·번역할 권리가 있는 게임에만 사용하세요. "
            "번역 시작 시 Data 폴더를 자동으로 백업합니다.",
            "info",
        )
        self.root.deiconify()

    # ----- setup -----------------------------------------------------------

    def px(self, n: float) -> int:
        return round(n * self.scale)

    def _setup_style(self) -> None:
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except Exception:
            pass

        for name in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont"):
            try:
                tkfont.nametofont(name).configure(family="맑은 고딕", size=10)
            except Exception:
                pass
        try:
            tkfont.nametofont("TkFixedFont").configure(family="Consolas", size=9)
        except Exception:
            pass
        self._bold_font = tkfont.nametofont("TkDefaultFont").copy()
        self._bold_font.configure(weight="bold")
        self._link_font = tkfont.nametofont("TkDefaultFont").copy()
        self._link_font.configure(underline=True)

        self.root.configure(background=_UI_BG)
        style.configure(
            ".",
            background=_UI_BG,
            foreground=_UI_TEXT,
            bordercolor=_UI_BORDER,
            lightcolor=_UI_SURFACE,
            darkcolor=_UI_BORDER,
            troughcolor="#e2e6ee",
            focuscolor=_UI_ACCENT,
        )
        style.configure("TFrame", background=_UI_BG)
        style.configure("Card.TFrame", background=_UI_SURFACE, relief="solid", borderwidth=1)
        style.configure("CardInner.TFrame", background=_UI_SURFACE)
        style.configure("TLabel", background=_UI_BG, foreground=_UI_TEXT)
        style.configure("Card.TLabel", background=_UI_SURFACE, foreground=_UI_TEXT)
        style.configure("CardHeading.TLabel", background=_UI_SURFACE, foreground=_UI_MUTED, font=self._bold_font)
        style.configure("Status.TLabel", background=_UI_BG, foreground=_UI_MUTED)
        style.configure("Link.TLabel", background=_UI_SURFACE, foreground=_UI_ACCENT, font=self._link_font)
        style.configure("Pct.TLabel", background=_UI_BG, foreground=_UI_TEXT, font=self._bold_font)

        style.configure("TButton", background="#e6eaf1", padding=(self.px(12), self.px(6)), relief="flat")
        style.map(
            "TButton",
            background=[("disabled", "#edeff3"), ("pressed", "#cfd6e1"), ("active", "#dbe1ea")],
            foreground=[("disabled", "#9aa1ab")],
        )
        style.configure(
            "Accent.TButton",
            background=_UI_ACCENT,
            foreground="#ffffff",
            bordercolor=_UI_ACCENT,
            padding=(self.px(18), self.px(7)),
            font=self._bold_font,
        )
        style.map(
            "Accent.TButton",
            background=[("disabled", "#aabdf2"), ("pressed", _UI_ACCENT_DOWN), ("active", _UI_ACCENT_HOVER)],
            foreground=[("disabled", "#f4f7ff")],
            bordercolor=[("disabled", "#aabdf2")],
        )
        style.configure("TCheckbutton", background=_UI_SURFACE, foreground=_UI_TEXT)
        style.map("TCheckbutton", background=[("active", _UI_SURFACE)])
        style.configure("TEntry", fieldbackground="#ffffff", padding=self.px(4))
        style.configure("TCombobox", fieldbackground="#ffffff", padding=self.px(4))
        style.configure("TSpinbox", fieldbackground="#ffffff", padding=self.px(4))
        style.configure(
            "Horizontal.TProgressbar",
            troughcolor="#e2e6ee",
            background=_UI_ACCENT,
            bordercolor=_UI_BORDER,
            lightcolor=_UI_ACCENT,
            darkcolor=_UI_ACCENT,
        )

    def _setup_icon(self) -> None:
        try:
            # Always rewrite: rendering the small sizes is instant, and this avoids ever
            # loading a stale/corrupt icon left in temp by an older version.
            ico_path = Path(tempfile.gettempdir()) / "rvx_gemini_translator.ico"
            ico_path.write_bytes(app_icon_ico_bytes())
            self.root.iconbitmap(default=str(ico_path))
        except Exception:
            try:
                self._icon_img = tk.PhotoImage(data=app_icon_png_base64(64))
                self.root.iconphoto(True, self._icon_img)
            except Exception:
                pass

    def _card(self, parent: Any, title: str) -> Any:
        outer = ttk.Frame(parent, style="Card.TFrame", padding=(self.px(14), self.px(10), self.px(14), self.px(12)))
        ttk.Label(outer, text=title, style="CardHeading.TLabel").grid(
            row=0, column=0, sticky="w", pady=(0, self.px(7))
        )
        body = ttk.Frame(outer, style="CardInner.TFrame")
        body.grid(row=1, column=0, sticky="nsew")
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(1, weight=1)
        return outer, body

    def _build_ui(self) -> None:
        px = self.px
        self.root.geometry(f"{px(920)}x{px(720)}")
        self.root.minsize(px(760), px(580))

        main = ttk.Frame(self.root, padding=(px(14), px(12), px(14), px(8)))
        main.pack(fill="both", expand=True)
        main.columnconfigure(0, weight=1)
        main.rowconfigure(5, weight=1)

        # --- game card ---
        game_card, game = self._card(main, "게임")
        game_card.grid(row=0, column=0, sticky="ew")
        game.columnconfigure(1, weight=1)
        ttk.Label(game, text="Game.exe", style="Card.TLabel").grid(row=0, column=0, sticky="w", padx=(0, px(10)))
        self.exe_entry = ttk.Entry(game, textvariable=self.exe_var)
        self.exe_entry.grid(row=0, column=1, sticky="ew")
        ttk.Button(game, text="찾기...", command=self._browse_exe).grid(row=0, column=2, padx=(px(8), 0))

        # --- api card ---
        api_card, api = self._card(main, "Gemini API")
        api_card.grid(row=1, column=0, sticky="ew", pady=(px(10), 0))
        api.columnconfigure(1, weight=1)

        ttk.Label(api, text="API 키", style="Card.TLabel").grid(row=0, column=0, sticky="w", padx=(0, px(10)))
        self.api_entry = ttk.Entry(api, textvariable=self.api_var, show="•")
        self.api_entry.grid(row=0, column=1, sticky="ew")
        self.api_toggle_btn = ttk.Button(api, text="표시", width=6, command=self._toggle_api_visibility)
        self.api_toggle_btn.grid(row=0, column=2, padx=(px(8), 0))
        link = ttk.Label(api, text="API 키 발급받기", style="Link.TLabel", cursor="hand2")
        link.grid(row=0, column=3, padx=(px(12), 0))
        link.bind("<Button-1>", lambda _e: webbrowser.open("https://aistudio.google.com/apikey"))

        save_key_chk = ttk.Checkbutton(api, text="API 키 저장", variable=self.save_api_var)
        save_key_chk.grid(row=1, column=1, sticky="w", pady=(px(6), 0))
        _Tooltip(
            save_key_chk,
            "API 키를 설정 파일(%APPDATA%\\RVXGeminiTranslator\\settings.json)에 평문으로 저장합니다. "
            "공용 PC에서는 사용하지 마세요.",
        )

        ttk.Label(api, text="모델", style="Card.TLabel").grid(row=2, column=0, sticky="w", padx=(0, px(10)), pady=(px(8), 0))
        model_box = ttk.Combobox(
            api,
            textvariable=self.model_var,
            values=(DEFAULT_MODEL, "gemini-3.1-flash", "gemini-2.5-flash-lite", "gemini-2.5-flash"),
        )
        model_box.grid(row=2, column=1, sticky="ew", pady=(px(8), 0))

        lang_row = ttk.Frame(api, style="CardInner.TFrame")
        lang_row.grid(row=3, column=1, sticky="w", pady=(px(8), 0))
        ttk.Label(api, text="언어", style="Card.TLabel").grid(row=3, column=0, sticky="w", padx=(0, px(10)), pady=(px(8), 0))
        ttk.Label(lang_row, text="원문", style="Card.TLabel").pack(side="left")
        ttk.Combobox(lang_row, textvariable=self.source_var, width=13, values=("auto", "Japanese", "English", "Chinese")).pack(
            side="left", padx=(px(5), px(16))
        )
        ttk.Label(lang_row, text="대상", style="Card.TLabel").pack(side="left")
        ttk.Combobox(lang_row, textvariable=self.target_var, width=13, values=("Korean", "English", "Japanese")).pack(
            side="left", padx=(px(5), 0)
        )

        # --- options card ---
        opt_card, opts = self._card(main, "번역 옵션")
        opt_card.grid(row=2, column=0, sticky="ew", pady=(px(10), 0))

        batch_row = ttk.Frame(opts, style="CardInner.TFrame")
        batch_row.grid(row=0, column=0, columnspan=2, sticky="w")
        ttk.Label(batch_row, text="배치 개수", style="Card.TLabel").pack(side="left")
        batch_size_spin = ttk.Spinbox(batch_row, textvariable=self.batch_size_var, from_=1, to=500, width=7)
        batch_size_spin.pack(side="left", padx=(px(5), px(18)))
        ttk.Label(batch_row, text="배치 글자수", style="Card.TLabel").pack(side="left")
        batch_chars_spin = ttk.Spinbox(
            batch_row, textvariable=self.batch_chars_var, from_=1000, to=100000, increment=1000, width=9
        )
        batch_chars_spin.pack(side="left", padx=(px(5), 0))
        _Tooltip(batch_size_spin, "Gemini 요청 1회에 담을 최대 문자열 수입니다. 크면 빠르지만 응답 누락 가능성이 올라갑니다. 기본 60.")
        _Tooltip(batch_chars_spin, "Gemini 요청 1회의 대략적인 최대 글자 수입니다. 기본 10000.")

        checks = (
            (self.include_ascii_var, "영어/ASCII 문자열도 번역", "영어 등 ASCII로만 된 문자열도 번역 대상에 포함합니다."),
            (self.internal_var, "내부 이름도 번역", "스위치/변수 이름 등 플레이어에게 보이지 않는 내부 이름도 번역합니다. 보통 꺼두는 것을 권장합니다."),
            (self.all_files_var, "모든 데이터 파일 처리 (위험)", "Scripts를 제외한 모든 .rvdata/.rvdata2 파일을 처리합니다. 예상하지 못한 파일까지 수정될 수 있어 위험합니다."),
            (self.dry_run_var, "드라이런 (파일 변경 없음)", "Gemini 요청과 파일 쓰기 없이 번역 후보만 스캔해 보고서를 만듭니다. API 키 없이 사용할 수 있습니다."),
        )
        for i, (var, label, tip) in enumerate(checks):
            chk = ttk.Checkbutton(opts, text=label, variable=var)
            chk.grid(row=1 + i // 2, column=i % 2, sticky="w", padx=(0, px(24)), pady=(px(7), 0))
            _Tooltip(chk, tip)

        opts.columnconfigure(1, weight=1)
        instr_label = ttk.Label(opts, text="번역 지침 (선택)", style="Card.TLabel")
        instr_label.grid(row=3, column=0, sticky="w", pady=(px(10), px(3)))
        self.instr_text = tk.Text(
            opts,
            height=2,
            relief="flat",
            borderwidth=0,
            highlightthickness=1,
            highlightbackground=_UI_BORDER,
            highlightcolor=_UI_ACCENT,
            background="#fbfcfe",
            foreground=_UI_TEXT,
            insertbackground=_UI_TEXT,
            font=tkfont.nametofont("TkDefaultFont"),
            wrap="word",
        )
        self.instr_text.grid(row=4, column=0, columnspan=2, sticky="ew")
        _Tooltip(
            instr_label,
            "번역 톤/문체 지침을 자유롭게 적으면 모든 번역 요청에 함께 전달됩니다.\n"
            "예: 주인공 '유리'는 밝은 반말, 집사 '한스'는 극존댓말. 게임 배경은 중세 판타지.",
        )

        # --- action row ---
        action = ttk.Frame(main)
        action.grid(row=3, column=0, sticky="ew", pady=(px(12), 0))
        self.start_btn = ttk.Button(action, text="번역 시작", style="Accent.TButton", command=self._start_translate)
        self.start_btn.pack(side="left")
        self.stop_btn = ttk.Button(action, text="중지", command=self._on_stop, state="disabled")
        self.stop_btn.pack(side="left", padx=(px(8), 0))
        self.repair_btn = ttk.Button(action, text="자산명 복구", command=self._start_repair_assets)
        self.repair_btn.pack(side="right")
        self.restore_btn = ttk.Button(action, text="최근 백업 복원", command=self._start_restore_backup)
        self.restore_btn.pack(side="right", padx=(0, px(8)))
        _Tooltip(self.stop_btn, "진행 중인 배치가 끝나면 안전하게 중지합니다. 이미 번역된 내용은 캐시에 남아 다음 실행에서 재사용됩니다.")
        _Tooltip(self.restore_btn, "가장 최근 Data_backup_before_gemini_* 백업으로 Data 폴더 전체를 되돌립니다.")
        _Tooltip(
            self.repair_btn,
            "번역 후 오디오/그래픽 파일 누락 오류가 날 때, 백업 기준으로 자산 파일명 문자열만 복구합니다. 대사 번역은 유지됩니다.",
        )

        # --- progress ---
        prog_frame = ttk.Frame(main)
        prog_frame.grid(row=4, column=0, sticky="ew", pady=(px(10), 0))
        prog_frame.columnconfigure(0, weight=1)
        self.progressbar = ttk.Progressbar(prog_frame, mode="determinate", maximum=100.0)
        self.progressbar.grid(row=0, column=0, sticky="ew")
        self.pct_label = ttk.Label(prog_frame, text="", style="Pct.TLabel", width=5, anchor="e")
        self.pct_label.grid(row=0, column=1, padx=(px(8), 0))
        self.status_label = ttk.Label(prog_frame, text="", style="Status.TLabel")
        self.status_label.grid(row=1, column=0, columnspan=2, sticky="w", pady=(px(3), 0))

        # --- log card ---
        log_card = ttk.Frame(main, style="Card.TFrame", padding=(px(14), px(10), px(14), px(12)))
        log_card.grid(row=5, column=0, sticky="nsew", pady=(px(10), 0))
        log_card.columnconfigure(0, weight=1)
        log_card.rowconfigure(1, weight=1)
        log_head = ttk.Frame(log_card, style="CardInner.TFrame")
        log_head.grid(row=0, column=0, sticky="ew", pady=(0, px(7)))
        log_head.columnconfigure(0, weight=1)
        ttk.Label(log_head, text="로그", style="CardHeading.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Button(log_head, text="로그 지우기", command=self.clear_log).grid(row=0, column=1, sticky="e")

        self.log_text = scrolledtext.ScrolledText(
            log_card,
            height=12,
            state="disabled",
            relief="flat",
            borderwidth=0,
            highlightthickness=1,
            highlightbackground=_UI_BORDER,
            highlightcolor=_UI_BORDER,
            background="#fbfcfe",
            foreground=_UI_TEXT,
            insertbackground=_UI_TEXT,
            font=tkfont.nametofont("TkFixedFont"),
            wrap="word",
        )
        self.log_text.grid(row=1, column=0, sticky="nsew")
        for tag, color in _LOG_COLORS.items():
            self.log_text.tag_configure(tag, foreground=color)

        # --- status bar ---
        status_bar = ttk.Frame(main)
        status_bar.grid(row=6, column=0, sticky="ew", pady=(px(6), 0))
        status_bar.columnconfigure(0, weight=1)
        self.state_label = ttk.Label(status_bar, text="", style="Status.TLabel")
        self.state_label.grid(row=0, column=0, sticky="w")
        self.elapsed_label = ttk.Label(status_bar, text="", style="Status.TLabel")
        self.elapsed_label.grid(row=0, column=1, sticky="e")

    # ----- settings --------------------------------------------------------

    def _load_settings(self) -> None:
        data = load_settings()
        self.exe_var.set(str(data.get("exe_path", "") or ""))
        self.model_var.set(str(data.get("model", DEFAULT_MODEL) or DEFAULT_MODEL))
        self.source_var.set(str(data.get("source_lang", "auto") or "auto"))
        self.target_var.set(str(data.get("target_lang", "Korean") or "Korean"))
        self.batch_size_var.set(str(data.get("batch_size", 60) or 60))
        self.batch_chars_var.set(str(data.get("batch_chars", 10000) or 10000))
        self.include_ascii_var.set(bool(data.get("include_ascii", True)))
        self.internal_var.set(bool(data.get("include_internal_names", False)))
        self.all_files_var.set(bool(data.get("process_all_files", False)))
        self.dry_run_var.set(bool(data.get("dry_run", False)))
        self.save_api_var.set(bool(data.get("save_api_key", False)))
        env_key = os.environ.get("GEMINI_API_KEY", "").strip()
        saved_key = str(data.get("api_key", "") or "") if self.save_api_var.get() else ""
        self.api_var.set(env_key or saved_key)
        instructions = str(data.get("extra_instructions", "") or "")
        if instructions:
            self.instr_text.delete("1.0", "end")
            self.instr_text.insert("1.0", instructions)
        geometry = str(data.get("geometry", "") or "")
        # Tk on Windows reports "+-N" offsets on secondary monitors, and -32000 when the
        # window was closed while minimized — accept the former, reject the latter.
        if re.fullmatch(r"\d+x\d+([+-]-?\d{1,5}[+-]-?\d{1,5})?", geometry) and "-32000" not in geometry:
            try:
                self.root.geometry(geometry)
            except Exception:
                pass

    def _collect_settings(self) -> dict[str, Any]:
        data: dict[str, Any] = {
            "exe_path": self.exe_var.get().strip(),
            "model": self.model_var.get().strip(),
            "source_lang": self.source_var.get().strip(),
            "target_lang": self.target_var.get().strip(),
            "batch_size": self.batch_size_var.get().strip(),
            "batch_chars": self.batch_chars_var.get().strip(),
            "include_ascii": self.include_ascii_var.get(),
            "include_internal_names": self.internal_var.get(),
            "process_all_files": self.all_files_var.get(),
            "dry_run": self.dry_run_var.get(),
            "save_api_key": self.save_api_var.get(),
            "extra_instructions": self.instr_text.get("1.0", "end").strip(),
            "geometry": self.root.geometry(),
        }
        if self.save_api_var.get():
            data["api_key"] = self.api_var.get().strip()
        return data

    def _on_close(self) -> None:
        if self._job_running() and not messagebox.askyesno(
            APP_NAME,
            "작업이 아직 진행 중입니다. 지금 종료하면 현재 처리 중인 내용이 중단될 수 있습니다.\n"
            "정말 종료할까요?",
            parent=self.root,
        ):
            return
        self.cancel_event.set()
        save_settings(self._collect_settings())
        self.root.destroy()

    # ----- log -------------------------------------------------------------

    def append_log(self, msg: str, level: Optional[str] = None) -> None:
        tag = level or classify_log(msg)
        at_bottom = self.log_text.yview()[1] >= 0.999
        self.log_text.configure(state="normal")
        self.log_text.insert("end", time.strftime("[%H:%M:%S] "), "ts")
        self.log_text.insert("end", msg + "\n", tag)
        self.log_text.configure(state="disabled")
        if at_bottom:
            self.log_text.see("end")

    def clear_log(self) -> None:
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")

    # ----- state / validation ----------------------------------------------

    def _job_running(self) -> bool:
        return bool(self.worker and self.worker.is_alive())

    def _update_start_state(self, *_args: Any) -> None:
        exe_text = self.exe_var.get().strip()
        exe_ok = bool(exe_text) and Path(exe_text).is_file() and exe_text.lower().endswith(".exe")
        api_ok = bool(self.api_var.get().strip()) or self.dry_run_var.get()
        running = self._job_running()
        self.start_btn.configure(state=("normal" if exe_ok and api_ok and not running else "disabled"))
        self.restore_btn.configure(state=("normal" if exe_ok and not running else "disabled"))
        self.repair_btn.configure(state=("normal" if exe_ok and not running else "disabled"))
        if running:
            return
        if not exe_ok:
            self.state_label.configure(text="번역할 게임의 Game.exe를 선택하세요.")
        elif not api_ok:
            self.state_label.configure(text="Gemini API 키를 입력하세요. (드라이런은 키 없이 가능)")
        else:
            self.state_label.configure(text="준비 완료")

    def _set_running(self, running: bool, allow_stop: bool = False) -> None:
        state = "disabled" if running else "normal"
        self.start_btn.configure(state=state)
        self.restore_btn.configure(state=state)
        self.repair_btn.configure(state=state)
        self.stop_btn.configure(state=("normal" if running and allow_stop else "disabled"))
        if not running:
            self._update_start_state()

    # ----- actions ----------------------------------------------------------

    def _browse_exe(self) -> None:
        path = filedialog.askopenfilename(
            title="RPG Maker VX / VX Ace Game.exe 선택",
            filetypes=[("EXE files", "*.exe"), ("All files", "*.*")],
        )
        if path:
            self.exe_var.set(path)

    def _toggle_api_visibility(self) -> None:
        self._api_hidden = not self._api_hidden
        self.api_entry.configure(show=("•" if self._api_hidden else ""))
        self.api_toggle_btn.configure(text=("표시" if self._api_hidden else "숨김"))

    def _ui_log(self, msg: str) -> None:
        self.q.put(("log", msg))

    def _ui_progress(self, phase: str, cur: int, total: int, detail: str) -> None:
        self.q.put(("progress", (phase, cur, total, detail)))

    def _start_job(self, kind: str, target: Callable[[], str], determinate: bool) -> None:
        if self._job_running():
            messagebox.showinfo(APP_NAME, "이미 작업 중입니다.", parent=self.root)
            return
        self.clear_log()
        self.cancel_event.clear()
        self.job_kind = kind
        self._job_t0 = time.monotonic()
        self._set_running(True, allow_stop=(kind == "translate"))
        if determinate:
            self.progressbar.configure(mode="determinate", maximum=100.0, value=0.0)
            self.pct_label.configure(text="0%")
        else:
            self.pct_label.configure(text="")
            self.progressbar.configure(mode="indeterminate")
            self.progressbar.start(12)

        def job() -> None:
            try:
                self.q.put(("done", target()))
            except TranslationCancelled as exc:
                self.q.put(("cancelled", str(exc)))
            except Exception as exc:
                self.q.put(("error", f"{exc}\n\n{traceback.format_exc()}"))

        self.worker = threading.Thread(target=job, daemon=True)
        self.worker.start()
        self._tick_elapsed()

    def _start_translate(self) -> None:
        if self._job_running():
            return
        try:
            cfg = TranslatorConfig(
                exe_path=Path(self.exe_var.get().strip()),
                api_key=self.api_var.get().strip(),
                model=self.model_var.get().strip(),
                source_lang=self.source_var.get().strip(),
                target_lang=self.target_var.get().strip(),
                include_ascii=self.include_ascii_var.get(),
                include_internal_names=self.internal_var.get(),
                process_all_files=self.all_files_var.get(),
                dry_run=self.dry_run_var.get(),
                batch_size=max(1, int(self.batch_size_var.get() or "60")),
                batch_chars=max(1000, int(self.batch_chars_var.get() or "10000")),
                extra_instructions=self.instr_text.get("1.0", "end").strip(),
            )
        except Exception as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self.root)
            return

        if not cfg.dry_run and not messagebox.askyesno(
            APP_NAME,
            "Data 폴더의 .rvdata 파일을 번역해 수정합니다.\n"
            "시작 전에 Data 폴더 전체가 자동으로 백업됩니다. 계속할까요?",
            parent=self.root,
        ):
            return

        save_settings(self._collect_settings())
        self.status_label.configure(text="준비 중...")
        self.state_label.configure(text="번역 작업 실행 중")

        def target() -> str:
            translate_game(cfg, log=self._ui_log, progress=self._ui_progress, cancel=self.cancel_event)
            return "드라이런이 완료되었습니다." if cfg.dry_run else "번역이 완료되었습니다."

        self._start_job("translate", target, determinate=True)

    def _start_restore_backup(self) -> None:
        if self._job_running():
            return
        exe_text = self.exe_var.get().strip()
        if not messagebox.askyesno(
            APP_NAME,
            "가장 최근 Data_backup_before_gemini_* 백업으로 Data 폴더를 복원합니다.\n"
            "현재 Data 폴더는 Data_before_restore_* 이름으로 보관됩니다. 계속할까요?",
            parent=self.root,
        ):
            return
        self.state_label.configure(text="백업 복원 실행 중")

        def target() -> str:
            restored = restore_latest_backup(Path(exe_text), log=self._ui_log)
            return f"백업 복원 완료:\n{restored}"

        self._start_job("restore", target, determinate=False)

    def _start_repair_assets(self) -> None:
        if self._job_running():
            return
        exe_text = self.exe_var.get().strip()
        if not messagebox.askyesno(
            APP_NAME,
            "백업에서 오디오/그래픽 같은 자산 파일명만 원래대로 복구합니다.\n"
            "대사 번역은 최대한 유지하고, 복구 전 현재 Data도 다시 백업합니다. 계속할까요?",
            parent=self.root,
        ):
            return
        self.state_label.configure(text="자산명 복구 실행 중")

        def target() -> str:
            files_changed, restored_nodes, _backup = repair_asset_references(Path(exe_text), log=self._ui_log)
            return f"자산명 복구 완료: 파일 {files_changed}개, 문자열 {restored_nodes}개"

        self._start_job("repair", target, determinate=False)

    def _on_stop(self) -> None:
        if not self._job_running():
            return
        self.cancel_event.set()
        self.stop_btn.configure(state="disabled")
        self.status_label.configure(text="중지 요청됨 — 현재 배치가 끝나면 중지됩니다")
        self.append_log("중지 요청됨 — 진행 중인 배치가 끝나면 안전하게 중지됩니다.", "warn")

    # ----- polling ----------------------------------------------------------

    def _stop_marquee(self) -> None:
        try:
            self.progressbar.stop()
        except Exception:
            pass
        self.progressbar.configure(mode="determinate", maximum=100.0)

    def _tick_elapsed(self) -> None:
        if self._elapsed_after is not None:
            try:
                self.root.after_cancel(self._elapsed_after)
            except Exception:
                pass
            self._elapsed_after = None
        elapsed = int(time.monotonic() - self._job_t0)
        self.elapsed_label.configure(text=f"경과 {elapsed // 60:02d}:{elapsed % 60:02d}")
        if self._job_running():
            self._elapsed_after = self.root.after(500, self._tick_elapsed)

    def _on_progress_msg(self, phase: str, cur: int, total: int, detail: str) -> None:
        base, span = self._PROGRESS_SPANS.get(phase, (0.0, 100.0))
        frac = (cur / total) if total > 0 else 1.0
        pct = min(100.0, base + span * frac)
        self.progressbar.configure(value=pct)
        self.pct_label.configure(text=f"{pct:.0f}%")
        name = self._PHASE_NAMES.get(phase, phase)
        self.status_label.configure(text=f"{name} · {detail}" if detail else name)

    def _finish_job(self) -> None:
        self._stop_marquee()
        self._set_running(False)
        self._tick_elapsed()

    def _poll_queue(self) -> None:
        try:
            while True:
                kind, payload = self.q.get_nowait()
                if kind == "log":
                    self.append_log(str(payload))
                elif kind == "progress":
                    self._on_progress_msg(*payload)
                elif kind == "done":
                    # A terminal message means the job is over even if the worker thread
                    # is still in its final instructions; without this, _update_start_state
                    # can see is_alive() and leave the buttons stuck disabled.
                    self.worker = None
                    self._finish_job()
                    if self.job_kind == "translate":
                        self.progressbar.configure(value=100.0)
                        self.pct_label.configure(text="100%")
                    self.status_label.configure(text="완료")
                    self.append_log(str(payload), "ok")
                    messagebox.showinfo(APP_NAME, str(payload), parent=self.root)
                elif kind == "cancelled":
                    self.worker = None
                    self._finish_job()
                    self.status_label.configure(text="중지됨")
                    self.append_log(
                        "작업이 중지되었습니다. 게임 파일은 변경되지 않았고, 이미 번역된 문자열은 캐시에 저장되어 "
                        "다음 실행 시 이어서 진행됩니다.",
                        "warn",
                    )
                    messagebox.showinfo(
                        APP_NAME,
                        "중지되었습니다.\n완료된 배치는 캐시에 저장되어 재실행 시 이어서 진행됩니다.",
                        parent=self.root,
                    )
                elif kind == "error":
                    self.worker = None
                    self._finish_job()
                    msg = str(payload)
                    self.status_label.configure(text="오류")
                    self.append_log("오류:\n" + msg, "err")
                    messagebox.showerror(APP_NAME, msg.splitlines()[0] if msg else "오류", parent=self.root)
        except queue.Empty:
            pass
        except Exception:
            # A handler exception (e.g. TclError during teardown) must never kill the
            # polling loop, or logs/progress/completion would silently freeze.
            pass
        finally:
            try:
                self.root.after(100, self._poll_queue)
            except Exception:
                pass

    def run(self) -> None:
        self.root.mainloop()


def run_gui() -> None:
    _enable_windows_dpi_awareness()
    _import_tkinter()
    TranslatorApp().run()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=f"{APP_NAME} {APP_VERSION}")
    p.add_argument("--exe", type=Path, help="RPG Maker VX/VX Ace Game.exe 경로")
    p.add_argument("--api-key", default=os.environ.get("GEMINI_API_KEY", ""), help="Gemini API 키")
    p.add_argument("--model", default=DEFAULT_MODEL, help=f"Gemini 모델 ID (기본: {DEFAULT_MODEL})")
    p.add_argument("--source", default="auto", help="원문 언어 (기본: auto)")
    p.add_argument("--target", default="Korean", help="대상 언어 (기본: Korean)")
    p.add_argument("--no-ascii", action="store_true", help="ASCII/영어처럼 보이는 문자열은 건너뜀")
    p.add_argument("--include-internal", action="store_true", help="스위치/변수 등 내부 이름도 번역")
    p.add_argument("--all-files", action="store_true", help="Scripts 제외 모든 .rvdata/.rvdata2 처리(위험)")
    p.add_argument("--instructions", default="", help="추가 번역 지침 (톤/문체/등장인물 말투 등)")
    p.add_argument("--dry-run", action="store_true", help="스캔만 하고 Gemini 요청/파일 쓰기 안 함")
    p.add_argument("--batch-size", type=int, default=60, help="Gemini 요청당 최대 문자열 수")
    p.add_argument("--batch-chars", type=int, default=10000, help="Gemini 요청당 대략 최대 글자 수")
    p.add_argument("--restore-latest-backup", action="store_true", help="가장 최근 Data_backup_before_gemini_* 백업으로 Data 복원")
    p.add_argument("--repair-assets", action="store_true", help="백업 기준으로 오디오/그래픽 파일명 참조만 복구")
    p.add_argument("--backup-dir", type=Path, help="복원/자산명 복구에 사용할 백업 Data 폴더 경로")
    p.add_argument("--gui", action="store_true", help="GUI 실행")
    p.add_argument("--write-icon", type=Path, metavar="PATH", help="앱 아이콘 .ico 파일을 생성하고 종료 (빌드용)")
    return p


def main(argv: Optional[list[str]] = None) -> int:
    args = build_arg_parser().parse_args(argv)
    if args.write_icon:
        try:
            path = write_icon_file(args.write_icon)
            print(f"아이콘 저장: {path}")
            return 0
        except Exception as exc:
            print(f"오류: {exc}", file=sys.stderr)
            return 1
    if args.restore_latest_backup:
        if not args.exe:
            print("오류: --restore-latest-backup에는 --exe 경로가 필요합니다.", file=sys.stderr)
            return 1
        try:
            restore_latest_backup(args.exe, log=print, backup_dir=args.backup_dir)
            return 0
        except Exception as exc:
            print(f"오류: {exc}", file=sys.stderr)
            return 1
    if args.repair_assets:
        if not args.exe:
            print("오류: --repair-assets에는 --exe 경로가 필요합니다.", file=sys.stderr)
            return 1
        try:
            repair_asset_references(args.exe, backup_dir=args.backup_dir, log=print)
            return 0
        except Exception as exc:
            print(f"오류: {exc}", file=sys.stderr)
            return 1
    if args.gui or not args.exe:
        run_gui()
        return 0
    cfg = TranslatorConfig(
        exe_path=args.exe,
        api_key=args.api_key,
        model=args.model,
        source_lang=args.source,
        target_lang=args.target,
        include_ascii=not args.no_ascii,
        include_internal_names=args.include_internal,
        process_all_files=args.all_files,
        dry_run=args.dry_run,
        batch_size=max(1, args.batch_size),
        batch_chars=max(1000, args.batch_chars),
        extra_instructions=args.instructions,
    )
    try:
        translate_game(cfg, log=print)
        return 0
    except Exception as exc:
        print(f"오류: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
