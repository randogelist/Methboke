@echo off
call "%~dp0..\run.cmd" --endpoint SerrinComparison %*
exit /b %errorlevel%
