@echo off
call "%~dp0..\run.cmd" --endpoint MathlibODE %*
exit /b %errorlevel%
