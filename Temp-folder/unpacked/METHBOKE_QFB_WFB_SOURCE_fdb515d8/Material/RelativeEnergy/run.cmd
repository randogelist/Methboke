@echo off
call "%~dp0..\run.cmd" --endpoint RelativeEnergy %*
exit /b %errorlevel%
