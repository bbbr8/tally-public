@echo off
cd /d "%~dp0"
where python >nul 2>&1
if errorlevel 1 (
  echo Install Python 3.12 or newer from python.org, with Python on PATH.
  pause
  exit /b 1
)
set TALLY_NO_EXPERIMENT_LOG=1
python -X utf8 -B tally.py --selftest
if errorlevel 1 (
  pause
  exit /b 1
)
python -X utf8 -B tally.py
pause
