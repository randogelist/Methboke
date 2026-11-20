@echo off
call "%~dp0..\run.cmd" --endpoint QFBRestart %*
exit /b %errorlevel%
