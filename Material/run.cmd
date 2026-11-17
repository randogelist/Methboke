@echo off
setlocal
cd /d "%~dp0"
where py >nul 2>nul
if errorlevel 1 (
  python ci\build.py --native --report registry\current.json %*
) else (
  py -3 ci\build.py --native --report registry\current.json %*
)
exit /b %errorlevel%
