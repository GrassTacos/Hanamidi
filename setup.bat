@echo off
setlocal EnableExtensions
title Hanamidi - Setup
cd /d "%~dp0"

echo ==================================================
echo   Hanamidi - one-time setup
echo ==================================================
echo.

rem ---------- 1. Python 3.11 ----------
py -3.11 --version >nul 2>&1
if not errorlevel 1 goto python_ok

echo [1/4] Python 3.11 was not found. Installing it with winget...
where winget >nul 2>&1
if errorlevel 1 goto no_winget
winget install -e --id Python.Python.3.11 --accept-package-agreements --accept-source-agreements
py -3.11 --version >nul 2>&1
if errorlevel 1 goto restart_needed

:python_ok
echo [1/4] Python 3.11 is installed.
echo.

rem ---------- 2. ffmpeg, only needed for some audio formats ----------
where ffmpeg >nul 2>&1
if not errorlevel 1 goto ffmpeg_ok
where winget >nul 2>&1
if errorlevel 1 goto ffmpeg_skip
echo [2/4] Installing ffmpeg, which some audio formats need...
winget install -e --id Gyan.FFmpeg --accept-package-agreements --accept-source-agreements
goto ffmpeg_done
:ffmpeg_skip
echo [2/4] Skipping ffmpeg because winget is not available. WAV files will still work.
goto ffmpeg_done
:ffmpeg_ok
echo [2/4] ffmpeg is installed.
:ffmpeg_done
echo.

rem ---------- 3. Python libraries ----------
echo [3/4] Installing libraries. This downloads several GB and can take
echo       10 to 20 minutes. Please leave this window open.
echo.
py -3.11 -m pip install --upgrade pip
py -3.11 -m pip install --no-warn-script-location demucs basic-pitch pretty_midi librosa "setuptools<81"
if errorlevel 1 goto pip_failed

rem ---------- 4. Verify ----------
echo.
echo [4/4] Checking the install...
py -3.11 -c "import demucs, basic_pitch, pretty_midi, librosa, pkg_resources" >nul 2>&1
if errorlevel 1 goto verify_failed
echo All libraries are working.
echo.

rem ---------- Optional shortcut and launch ----------
set "APP=%~dp0hanamidi.pyw"
if not exist "%APP%" goto no_app
py -3.11 "%APP%" --make-icon >nul 2>&1
set "PYW="
for /f "delims=" %%p in ('where pyw 2^>nul') do set "PYW=%%p"
if not defined PYW goto finish

set "ANS="
set /p ANS=Create a desktop shortcut? [Y/N]: 
if /i not "%ANS%"=="Y" goto ask_launch
powershell -NoProfile -ExecutionPolicy Bypass -Command "$s=(New-Object -ComObject WScript.Shell).CreateShortcut([Environment]::GetFolderPath('Desktop')+'\Hanamidi.lnk'); $s.TargetPath='%PYW%'; $s.Arguments='-3.11 \"%APP%\"'; $s.WorkingDirectory='%~dp0'; $s.IconLocation='%~dp0hanamidi.ico'; $s.Description='Hanamidi'; $s.Save()"
if errorlevel 1 echo Could not create the shortcut. You can still open the app by double-clicking it.

:ask_launch
set "ANS="
set /p ANS=Open Hanamidi now? [Y/N]: 
if /i "%ANS%"=="Y" start "" "%PYW%" -3.11 "%APP%"
goto finish

:finish
echo.
echo ==================================================
echo   Setup complete.
echo   The first conversion also downloads a separation model, a few
echo   hundred MB, so it will take a little longer.
echo ==================================================
pause
exit /b 0

:no_app
echo.
echo Libraries are installed, but hanamidi.pyw was not found next to this file.
echo Put setup.bat in the same folder as the app and run it again to create a shortcut.
pause
exit /b 0

:no_winget
echo.
echo winget is not available on this PC, so Python could not be installed automatically.
echo Install Python 3.11 from python.org/downloads/windows ^(choose the 64-bit Windows
echo installer and tick "Add python.exe to PATH"^), then run setup.bat again.
pause
exit /b 1

:restart_needed
echo.
echo Python was installed, but this window cannot see it yet.
echo Close this window and double-click setup.bat again to continue.
pause
exit /b 0

:pip_failed
echo.
echo The library install failed. Scroll up for the line starting with ERROR.
echo Common fixes: free up 5 GB of disk space, pause your antivirus for a few
echo minutes, then run setup.bat again.
pause
exit /b 1

:verify_failed
echo.
echo The libraries installed but could not be loaded. Run this to see the error:
echo   py -3.11 -c "import demucs, basic_pitch, pretty_midi, librosa, pkg_resources"
pause
exit /b 1
