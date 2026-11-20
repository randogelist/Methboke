@echo off
call "%~dp0..\run.cmd" --endpoint QFBRoot %*
exit /b %errorlevel%
