@echo off
call "%~dp0..\run.cmd" --endpoint MathlibAnalytic %*
exit /b %errorlevel%
