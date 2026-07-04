@echo off
setlocal
cd /d "%~dp0"

echo [1/4] Installing dependencies...
python -m pip install --upgrade pip
python -m pip install -r requirements.txt
python -m pip install pyinstaller
if errorlevel 1 goto :error

echo [2/4] Generating app icon...
python rvx_gemini_translator.py --write-icon app.ico
if errorlevel 1 goto :error

echo [3/4] Building exe...
pyinstaller --onefile --windowed --clean --noconfirm --name RVX_Gemini_Translator --icon app.ico rvx_gemini_translator.py
if errorlevel 1 goto :error

echo [4/4] Cleaning up intermediate files...
rmdir /s /q build 2>nul
del /q RVX_Gemini_Translator.spec 2>nul
del /q app.ico 2>nul

echo.
echo Build complete: dist\RVX_Gemini_Translator.exe
pause
exit /b 0

:error
echo.
echo Build failed.
pause
exit /b 1
