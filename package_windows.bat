@echo off
setlocal

if not exist ".venv\Scripts\python.exe" (
    py -3 -m venv .venv
    if errorlevel 1 exit /b 1
)

".venv\Scripts\python.exe" -m pip install -r requirements-build.txt
if errorlevel 1 exit /b %errorlevel%

".venv\Scripts\python.exe" -m PyInstaller --noconfirm --clean --onefile --console --name StockBill --distpath dist --workpath build --specpath build stockbill.py
if errorlevel 1 exit /b %errorlevel%

echo.
echo Built dist\StockBill.exe
echo User data and logs are stored in the Local AppData StockBill folder.
