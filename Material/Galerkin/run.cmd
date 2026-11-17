@echo off
call "%~dp0..\run.cmd" --endpoint Galerkin %*
exit /b %errorlevel%
