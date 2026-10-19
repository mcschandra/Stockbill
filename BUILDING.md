# Building StockBill for Windows

1. Install Python 3.8 or newer and make sure the Windows `py` launcher is available.
2. Run `package_windows.bat` from this folder.
3. Distribute `dist\StockBill.exe`. The build is a one-file executable and includes the Python dependencies.

The executable starts the StockBill web server and opens it in the default browser. By default, it listens on all network interfaces so phones on the same Wi-Fi can connect. Use `--host 127.0.0.1` to restrict access to this computer, or `--no-browser` to prevent opening a browser automatically.

The executable stores `stockbill_data.json`, backups, and `stockbill.log` under `%LOCALAPPDATA%\StockBill` so data persists outside the temporary folder used by one-file executables. The `--data` option can select a different JSON data file.

To try the app with sample records, run `StockBill.exe --demo`. Use `StockBill.exe --help` for all supported command-line options.
