@echo off
call "%~dp0..\run.cmd" --endpoint QFBTail %*
exit /b %errorlevel%
