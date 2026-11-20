@echo off
call "%~dp0..\run.cmd" --endpoint PhysicalNSE %*
exit /b %errorlevel%
