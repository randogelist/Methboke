@echo off
call "%~dp0..\run.cmd" --endpoint QFBTraceUniqueness %*
exit /b %errorlevel%
