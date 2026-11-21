@echo off
call "%~dp0..\run.cmd" --endpoint SmallH12 %*
exit /b %errorlevel%
