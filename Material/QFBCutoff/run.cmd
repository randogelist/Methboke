@echo off
call "%~dp0..\run.cmd" --endpoint QFBCutoff %*
exit /b %errorlevel%
