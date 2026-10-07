#!/usr/bin/env python3
"""
StockBill - inventory and billing in a single Python file.

* No database: everything lives in one JSON file (default: stockbill_data.json).
* Python 3.8+; the qrcode dependency generates payment QR codes locally.
* Desktop + mobile: it runs a small web server with a responsive UI. Open it in
  a browser on the computer, and on any phone/tablet on the same Wi-Fi.

Install dependencies:
    python -m pip install -r requirements.txt

Run:
    python stockbill.py                      # create an email/password account on first open
    python stockbill.py --demo               # load sample items to try it out
    python stockbill.py --data D:/shop.json  # choose where the data file lives
    python stockbill.py --host 127.0.0.1     # this computer only (no phone access)
    python stockbill.py --tls-cert cert.pem --tls-key key.pem  # enable HTTPS camera access

Features: items and stock, customers, billing with GST/tax + discounts, part payments
and credit (dues), stock history, void bills (stock returns), print invoices,
WhatsApp Web reminders, monthly simple interest on credit, single-key keyboard navigation, expense register,
cash summaries, CSV exports, JSON backup, and a persistent activity log.
"""
import argparse
import calendar
import csv
import hashlib
import hmac
import io
import json
import os
import re
import secrets
import shutil
import socket
import ssl
import sys
import threading
import traceback
import webbrowser
from datetime import datetime, timedelta
from decimal import Decimal, ROUND_HALF_UP, InvalidOperation
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlencode, urlparse

import qrcode
from qrcode.image.svg import SvgPathImage

APP_NAME = "StockBill"
CENT = Decimal("0.01")
MILLI = Decimal("0.001")
PAY_METHODS = ("Cash", "UPI", "Card", "Bank", "Other")
ACTIVITY_LOG_MAX_BYTES = 2_000_000
ACTIVITY_LOG_BACKUPS = 5

DEFAULT_SETTINGS = {
    "business_name": "My Shop",
    "address": "",
    "phone": "",
    "upi_id": "",
    "credit_interest_monthly": 0.0,
    "gstin": "",
    "currency": "\u20b9",
    "country_code": "91",
    "invoice_prefix": "INV-",
    "footer_note": "Thank you for your business!",
    "round_off": True,
    "allow_negative_stock": False,
}


# --------------------------------------------------------------------------- #
# Small helpers
# --------------------------------------------------------------------------- #
class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


def now():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def text(value, max_len=120):
    return str(value if value is not None else "").strip()[:max_len]


def to_int(value, label):
    try:
        return int(value)
    except (TypeError, ValueError):
        raise ApiError(400, f"{label} is not valid")


def dec(value, label, default=None):
    """Parse a number into Decimal. Blank uses `default` if given, else errors."""
    if value is None or (isinstance(value, str) and not value.strip()):
        if default is not None:
            return default
        raise ApiError(400, f"{label} is required")
    try:
        d = Decimal(str(value).strip())
    except InvalidOperation:
        raise ApiError(400, f"{label} must be a number")
    if not d.is_finite():
        raise ApiError(400, f"{label} must be a number")
    return d


def money(d):
    return d.quantize(CENT, ROUND_HALF_UP)


def qty_round(d):
    return d.quantize(MILLI, ROUND_HALF_UP)


def status_for(grand, paid):
    if paid >= grand:
        return "paid"
    return "partial" if paid > 0 else "unpaid"


def csv_safe(value):
    """Stop spreadsheet apps from running cells that start with = + - @ as formulas."""
    s = str(value if value is not None else "")
    return "'" + s if s[:1] in ("=", "+", "-", "@") else s


def financial_year_bounds(value=None):
    if value == "all":
        return None, None
    if value in (None, ""):
        clock = datetime.now()
        year = clock.year if clock.month >= 4 else clock.year - 1
    else:
        if not re.fullmatch(r"\d{4}", str(value)):
            raise ApiError(400, "Financial year must be a four-digit starting year or 'all'")
        year = int(value)
    try:
        start = datetime(year, 4, 1).date().isoformat()
        end = datetime(year + 1, 4, 1).date().isoformat()
    except ValueError:
        raise ApiError(400, "Financial year is not valid")
    return start, end


def date_in_financial_year(stamp, bounds):
    start, end = bounds
    day = stamp[:10]
    return (start is None or day >= start) and (end is None or day < end)


def pin_digest(pin, salt):
    return hashlib.pbkdf2_hmac("sha256", pin.encode("utf-8"), salt, 200_000)


def stored_pin_matches(candidate, salt_hex, hash_hex):
    if not isinstance(candidate, str) or not salt_hex or not hash_hex:
        return False
    try:
        salt = bytes.fromhex(salt_hex)
        expected = bytes.fromhex(hash_hex)
    except ValueError:
        return False
    return hmac.compare_digest(pin_digest(candidate, salt), expected)


def valid_pin(pin):
    return isinstance(pin, str) and re.fullmatch(r"\d{4,12}", pin) is not None


def normalize_email(email):
    return email.strip().lower() if isinstance(email, str) else ""


def valid_email(email):
    return isinstance(email, str) and len(email) <= 254 and re.fullmatch(
        r"[^@\s]+@[^@\s]+\.[^@\s]+", email
    ) is not None


def password_digest(password, salt):
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 600_000)


def stored_password_matches(candidate, salt_hex, hash_hex):
    if not isinstance(candidate, str) or not salt_hex or not hash_hex:
        return False
    try:
        salt = bytes.fromhex(salt_hex)
        expected = bytes.fromhex(hash_hex)
    except ValueError:
        return False
    return hmac.compare_digest(password_digest(candidate, salt), expected)


def valid_password(password):
    return isinstance(password, str) and 8 <= len(password) <= 256


def valid_upi_id(value):
    return isinstance(value, str) and re.fullmatch(
        r"[A-Za-z0-9][A-Za-z0-9._-]{0,99}@[A-Za-z][A-Za-z0-9.-]{1,62}", value
    ) is not None


def month_anniversary(day, months):
    month_index = day.month - 1 + months
    year = day.year + month_index // 12
    month = month_index % 12 + 1
    return day.replace(year=year, month=month, day=min(day.day, calendar.monthrange(year, month)[1]))


# --------------------------------------------------------------------------- #
# JSON-file store + business logic
# --------------------------------------------------------------------------- #
class Store:
    def __init__(self, path):
        self.path = os.path.abspath(path)
        self.log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "stockbill.log")
        self.lock = threading.RLock()
        self.info = {}
        self.data = self._load()

    @staticmethod
    def _fresh():
        return {
            "version": 1,
            "counters": {"product": 0, "customer": 0, "invoice": 0, "stock": 0, "expense": 0},
            "settings": dict(DEFAULT_SETTINGS),
            "security": {
                "account_email": "", "account_password_salt": "", "account_password_hash": "",
                "mobile_pin_salt": "", "mobile_pin_hash": "",
            },
            "products": [],
            "customers": [],
            "invoices": [],
            "stock_log": [],
            "expenses": [],
        }

    def _load(self):
        if not os.path.exists(self.path):
            data = self._fresh()
            self._write(data)
            return data
        try:
            with open(self.path, encoding="utf-8") as f:
                data = json.load(f)
        except json.JSONDecodeError as e:
            self.log_activity("technical", "Data file load failed", str(e), 500)
            sys.exit(
                f"\nCould not read {self.path}: the file is not valid JSON ({e}).\n"
                f"Nothing was changed. Restore from '{self.path}.bak' or the 'backups' "
                f"folder next to it, then start again.\n"
            )
        fresh = self._fresh()
        for key, value in fresh.items():
            data.setdefault(key, value)
        for key, value in fresh["settings"].items():
            data["settings"].setdefault(key, value)
        for key, value in fresh["counters"].items():
            data["counters"].setdefault(key, value)
        data.setdefault("security", fresh["security"])
        for key, value in fresh["security"].items():
            data["security"].setdefault(key, value)
        return data

    # -- persistence ------------------------------------------------------- #
    def _snapshot(self):
        """Keep one dated copy per day (last 30 days) in a 'backups' folder."""
        try:
            if not os.path.exists(self.path):
                return
            folder = os.path.join(os.path.dirname(self.path), "backups")
            os.makedirs(folder, exist_ok=True)
            base = os.path.splitext(os.path.basename(self.path))[0]
            target = os.path.join(folder, f"{base}-{datetime.now():%Y-%m-%d}.json")
            if not os.path.exists(target):
                shutil.copy2(self.path, target)
            old = sorted(f for f in os.listdir(folder) if f.startswith(base + "-"))
            for name in old[:-30]:
                os.remove(os.path.join(folder, name))
        except OSError:
            pass  # a failed backup must never block a sale

    def _write(self, data):
        """Atomic save: write a temp file, then swap it in, so a crash can't corrupt data."""
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
            f.flush()
            os.fsync(f.fileno())
        if os.path.exists(self.path):
            self._snapshot()
            shutil.copy2(self.path, self.path + ".bak")
        os.replace(tmp, self.path)

    def _commit(self):
        try:
            self._write(self.data)
        except OSError as e:
            self.log_activity("technical", "Data save failed", str(e), 500)
            raise ApiError(500, f"Could not write the data file: {e}")

    def log_activity(self, category, event, details="", status=None):
        record = {
            "timestamp": now(),
            "category": text(category, 20),
            "event": text(event, 120),
            "details": text(details, 2000),
            "status": status,
        }
        encoded = (json.dumps(record, ensure_ascii=False) + "\n").encode("utf-8")
        try:
            with self.lock:
                if (os.path.exists(self.log_path)
                        and os.path.getsize(self.log_path) + len(encoded) > ACTIVITY_LOG_MAX_BYTES):
                    for index in range(ACTIVITY_LOG_BACKUPS - 1, 0, -1):
                        source = f"{self.log_path}.{index}"
                        if os.path.exists(source):
                            os.replace(source, f"{self.log_path}.{index + 1}")
                    if os.path.exists(self.log_path):
                        os.replace(self.log_path, self.log_path + ".1")
                with open(self.log_path, "ab") as f:
                    f.write(encoded)
                    f.flush()
                    os.fsync(f.fileno())
        except OSError as e:
            print(f"Warning: could not write developer log {self.log_path}: {e}", file=sys.stderr)

    def _next(self, kind):
        self.data["counters"][kind] += 1
        return self.data["counters"][kind]

    def _find(self, collection, item_id, label):
        for row in self.data[collection]:
            if row["id"] == item_id:
                return row
        raise ApiError(404, f"{label} not found")

    # -- settings ---------------------------------------------------------- #
    def update_settings(self, p):
        with self.lock:
            s = self.data["settings"]
            interest_rate = None
            if "credit_interest_monthly" in p:
                interest_rate = dec(p.get("credit_interest_monthly"), "Monthly credit interest rate")
                if not 0 <= interest_rate <= 100:
                    raise ApiError(400, "Monthly credit interest rate must be between 0 and 100")
            if "upi_id" in p:
                upi_id = text(p["upi_id"], 164)
                if upi_id and not valid_upi_id(upi_id):
                    raise ApiError(400, "Enter a valid UPI ID, such as name@bank")
                s["upi_id"] = upi_id
            long_fields = ("address", "footer_note")
            for key in ("business_name", "address", "phone", "gstin", "currency",
                        "country_code", "invoice_prefix", "footer_note"):
                if key in p:
                    s[key] = text(p[key], 300 if key in long_fields else 40)
            if not s["business_name"]:
                s["business_name"] = "My Shop"
            if not s["currency"]:
                s["currency"] = DEFAULT_SETTINGS["currency"]
            s["country_code"] = re.sub(r"\D", "", s["country_code"])
            for key in ("round_off", "allow_negative_stock"):
                if key in p:
                    s[key] = bool(p[key])
            if interest_rate is not None:
                s["credit_interest_monthly"] = float(interest_rate)
            self._commit()
            return s

    def upi_qr(self, q):
        with self.lock:
            settings = self.data["settings"]
            upi_id = settings.get("upi_id", "")
            if not valid_upi_id(upi_id):
                raise ApiError(400, "Add a valid UPI ID in Settings before generating a payment QR")
            amount = dec(qs(q, "amount"), "Amount")
            if amount <= 0:
                raise ApiError(400, "QR payment amount must be more than zero")
            if amount > Decimal("999999999999.99"):
                raise ApiError(400, "QR payment amount is too large")
            amount = money(amount)
            payment_uri = "upi://pay?" + urlencode({
                "pa": upi_id,
                "pn": text(settings.get("business_name"), 80) or "StockBill",
                "am": f"{amount:.2f}",
                "cu": "INR",
                "tn": "StockBill payment",
            })
            qr = qrcode.QRCode(box_size=8, border=4, error_correction=qrcode.constants.ERROR_CORRECT_M)
            qr.add_data(payment_uri)
            qr.make(fit=True)
            image = qr.make_image(image_factory=SvgPathImage)
            output = io.BytesIO()
            image.save(output)
            return output.getvalue()

    def update_account(self, email, password=None):
        email = normalize_email(email)
        if not valid_email(email):
            raise ApiError(400, "Enter a valid email address")
        if password is not None and not valid_password(password):
            raise ApiError(400, "Password must be 8 to 256 characters")
        with self.lock:
            security = self.data["security"]
            security["account_email"] = email
            if password is not None:
                salt = secrets.token_bytes(16)
                security["account_password_salt"] = salt.hex()
                security["account_password_hash"] = password_digest(password, salt).hex()
            self._commit()
        return email

    def update_mobile_pin(self, pin):
        if not valid_pin(pin):
            raise ApiError(400, "Mobile PIN must contain 4 to 12 digits")
        salt = secrets.token_bytes(16)
        with self.lock:
            self.data["security"]["mobile_pin_salt"] = salt.hex()
            self.data["security"]["mobile_pin_hash"] = pin_digest(pin, salt).hex()
            self._commit()

    def disable_mobile_pin(self):
        with self.lock:
            self.data["security"]["mobile_pin_salt"] = ""
            self.data["security"]["mobile_pin_hash"] = ""
            self._commit()

    # -- products ---------------------------------------------------------- #
    def list_products(self):
        with self.lock:
            return self.data["products"]

    def _log_stock(self, prod, change, reason, ref=""):
        self.data["stock_log"].append({
            "id": self._next("stock"),
            "date": now(),
            "product_id": prod["id"],
            "product_name": prod["name"],
            "change": float(change),
            "balance": prod["stock"],
            "reason": reason,
            "ref": ref,
        })

    def save_product(self, p, pid=None):
        with self.lock:
            name = text(p.get("name"), 120)
            if not name:
                raise ApiError(400, "Item name is required")
            price = money(dec(p.get("price"), "Selling price"))
            cost = money(dec(p.get("cost"), "Cost price", Decimal(0)))
            tax = dec(p.get("tax_rate"), "Tax rate", Decimal(0))
            low = qty_round(dec(p.get("low_stock"), "Low-stock alert", Decimal(0)))
            if price < 0 or cost < 0:
                raise ApiError(400, "Prices cannot be negative")
            if not 0 <= tax <= 100:
                raise ApiError(400, "Tax rate must be between 0 and 100")
            if low < 0:
                raise ApiError(400, "Low-stock alert cannot be negative")
            sku = text(p.get("sku"), 40)
            if sku:
                for other in self.data["products"]:
                    if other["id"] != pid and other["sku"].lower() == sku.lower():
                        raise ApiError(409, f"SKU {sku} is already used by {other['name']}")
            fields = {
                "name": name,
                "category": text(p.get("category"), 40),
                "unit": text(p.get("unit"), 12) or "pcs",
                "price": float(price),
                "cost": float(cost),
                "tax_rate": float(tax),
                "low_stock": float(low),
            }
            if pid is None:
                opening = qty_round(dec(p.get("stock"), "Opening stock", Decimal(0)))
                if opening < 0:
                    raise ApiError(400, "Opening stock cannot be negative")
                new_id = self._next("product")
                if not sku:
                    sku = f"P{new_id:04d}"
                    taken = {x["sku"].lower() for x in self.data["products"]}
                    while sku.lower() in taken:
                        sku += "x"
                prod = {"id": new_id, "sku": sku, "stock": float(opening), "active": True,
                        "created_at": now(), **fields}
                self.data["products"].append(prod)
                if opening > 0:
                    self._log_stock(prod, opening, "Opening stock")
            else:
                prod = self._find("products", pid, "Item")
                if sku:
                    prod["sku"] = sku
                prod.update(fields)  # stock is only changed through stock adjustments
            self._commit()
            return prod

    def delete_product(self, pid):
        with self.lock:
            prod = self._find("products", pid, "Item")
            used = any(li["product_id"] == pid for inv in self.data["invoices"] for li in inv["items"])
            if used:
                prod["active"] = False
                self._commit()
                return {"archived": True}
            self.data["products"].remove(prod)
            self._commit()
            return {"deleted": True}

    def restore_product(self, pid):
        with self.lock:
            prod = self._find("products", pid, "Item")
            prod["active"] = True
            self._commit()
            return prod

    def adjust_stock(self, p):
        with self.lock:
            prod = self._find("products", to_int(p.get("product_id"), "Item"), "Item")
            change = qty_round(dec(p.get("change"), "Quantity"))
            if change == 0:
                raise ApiError(400, "Quantity cannot be zero")
            new = qty_round(Decimal(str(prod["stock"])) + change)
            if new < 0 and not self.data["settings"]["allow_negative_stock"]:
                raise ApiError(409, f"You only have {prod['stock']:g} {prod['unit']} of {prod['name']}")
            prod["stock"] = float(new)
            self._log_stock(prod, change, text(p.get("reason"), 60) or "Manual adjustment")
            self._commit()
            return prod

    def list_stock_log(self, q):
        with self.lock:
            pid = to_int(qs(q, "product_id"), "Item") if qs(q, "product_id") else None
            limit = min(to_int(qs(q, "limit", "50"), "Limit"), 500)
            rows = [r for r in reversed(self.data["stock_log"]) if pid is None or r["product_id"] == pid]
            return rows[:limit]

    # -- customers --------------------------------------------------------- #
    def list_customers(self):
        with self.lock:
            due, principal_due, interest_due, bills = {}, {}, {}, {}
            for inv in self.data["invoices"]:
                self._recalc(inv)
                cid = inv["customer_id"]
                if cid is None:
                    continue
                bills[cid] = bills.get(cid, 0) + 1
                if inv["status"] != "void":
                    due[cid] = due.get(cid, Decimal(0)) + Decimal(str(inv["total_due"]))
                    principal_due[cid] = principal_due.get(cid, Decimal(0)) + Decimal(str(inv["principal_balance"]))
                    interest_due[cid] = interest_due.get(cid, Decimal(0)) + Decimal(str(inv["interest_balance"]))
            return [{**c, "due": float(due.get(c["id"], 0)),
                     "principal_due": float(principal_due.get(c["id"], 0)),
                     "interest_due": float(interest_due.get(c["id"], 0)),
                     "credit_interest_monthly": self.data["settings"].get("credit_interest_monthly", 0),
                     "bills": bills.get(c["id"], 0)}
                    for c in self.data["customers"]]

    def save_customer(self, p, cid=None):
        with self.lock:
            name = text(p.get("name"), 120)
            if not name:
                raise ApiError(400, "Customer name is required")
            phone = text(p.get("phone"), 20)
            if not phone:
                raise ApiError(400, "Customer phone number is required")
            fields = {
                "name": name,
                "phone": phone,
                "email": text(p.get("email"), 120),
                "address": text(p.get("address"), 300),
                "gstin": text(p.get("gstin"), 20),
            }
            if cid is None:
                cust = {"id": self._next("customer"), "created_at": now(), **fields}
                self.data["customers"].append(cust)
            else:
                cust = self._find("customers", cid, "Customer")
                cust.update(fields)
            self._commit()
            return {**cust, "due": 0.0, "bills": 0}

    def delete_customer(self, cid):
        with self.lock:
            cust = self._find("customers", cid, "Customer")
            if any(inv["customer_id"] == cid for inv in self.data["invoices"]):
                raise ApiError(409, "This customer has bills, so they can't be deleted")
            self.data["customers"].remove(cust)
            self._commit()
            return {"deleted": True}

    # -- invoices ---------------------------------------------------------- #
    def _recalc(self, inv):
        grand = Decimal(str(inv["grand_total"]))
        payments = inv.get("payments", [])
        principal_paid = sum(
            (Decimal(str(payment.get("principal_amount", payment["amount"]))) for payment in payments),
            Decimal(0),
        )
        interest_paid = sum(
            (Decimal(str(payment.get("interest_amount", 0))) for payment in payments),
            Decimal(0),
        )
        paid = sum((Decimal(str(payment["amount"])) for payment in payments), Decimal(0))
        principal_balance = max(Decimal(0), money(grand - principal_paid))
        interest_accrued = self._interest_accrued(inv)
        interest_balance = max(Decimal(0), money(interest_accrued - interest_paid))
        inv["paid"] = float(money(paid))
        inv["principal_balance"] = float(principal_balance)
        inv["interest_accrued"] = float(interest_accrued)
        inv["interest_paid"] = float(money(interest_paid))
        inv["interest_balance"] = float(interest_balance)
        inv["balance"] = float(principal_balance)
        inv["total_due"] = float(money(principal_balance + interest_balance))
        if inv["status"] != "void":
            inv["status"] = status_for(grand + interest_accrued, paid)

    def _interest_accrued(self, inv, as_of=None):
        rate = Decimal(str(self.data["settings"].get("credit_interest_monthly", 0)))
        if rate <= 0 or not inv.get("customer_id") or inv.get("status") == "void":
            return Decimal(0)
        issue_date = datetime.strptime(inv["date"][:10], "%Y-%m-%d").date()
        today = as_of or datetime.now().date()
        if issue_date >= today:
            return Decimal(0)
        payments = sorted(
            inv.get("payments", []),
            key=lambda payment: payment.get("date", "")[:10],
        )

        def principal_amount(payment):
            return Decimal(str(payment.get("principal_amount", payment["amount"])))

        principal = Decimal(str(inv["grand_total"]))
        for payment in payments:
            payment_day = datetime.strptime(payment.get("date", "")[:10], "%Y-%m-%d").date()
            if payment_day <= issue_date:
                principal = max(Decimal(0), principal - principal_amount(payment))

        accrued = Decimal(0)
        period_start = issue_date
        month = 1
        while principal > 0:
            period_end = month_anniversary(issue_date, month)
            if period_end > today:
                break
            accrued += money(principal * rate / 100)
            for payment in payments:
                payment_day = datetime.strptime(payment.get("date", "")[:10], "%Y-%m-%d").date()
                if period_start < payment_day <= period_end:
                    principal = max(Decimal(0), principal - principal_amount(payment))
            period_start = period_end
            month += 1
        return money(accrued)

    def create_invoice(self, p, mobile=False):
        with self.lock:
            raw_items = p.get("items")
            if not isinstance(raw_items, list) or not raw_items:
                raise ApiError(400, "Add at least one item to the bill")
            st = self.data["settings"]
            method = p.get("payment_method") if p.get("payment_method") in PAY_METHODS else "Cash"
            customer = None
            if p.get("customer_id"):
                customer = self._find("customers", to_int(p["customer_id"], "Customer"), "Customer")
            if p.get("payment_method") == "Credit" and customer is None:
                raise ApiError(400, "Choose a saved customer for a credit transaction")
            if customer and not text(customer.get("phone"), 20):
                raise ApiError(400, "Add a phone number to this customer before creating a bill")

            # 1) validate and price every line (nothing is changed yet)
            lines, need = [], {}
            gross_t = disc_t = taxable_t = tax_t = Decimal(0)
            for li in raw_items:
                if not isinstance(li, dict):
                    raise ApiError(400, "An item on the bill is not valid")
                prod = self._find("products", to_int(li.get("product_id"), "Item"), "Item")
                if not prod["active"]:
                    raise ApiError(409, f"{prod['name']} is archived and can't be billed")
                qty = qty_round(dec(li.get("qty"), "Quantity"))
                if qty <= 0:
                    raise ApiError(400, f"Quantity for {prod['name']} must be more than zero")
                price = money(Decimal(str(prod["price"])))
                pct = dec(li.get("discount_pct"), "Discount", Decimal(0))
                if pct != 0:
                    raise ApiError(400, "Discounts cannot be changed while billing")
                if price < 0:
                    raise ApiError(400, "Price cannot be negative")
                if not 0 <= pct <= 100:
                    raise ApiError(400, "Discount must be between 0 and 100")
                rate = Decimal(str(prod["tax_rate"]))
                gross = money(qty * price)
                disc = money(gross * pct / 100)
                taxable = gross - disc
                tax = money(taxable * rate / 100)
                gross_t += gross
                disc_t += disc
                taxable_t += taxable
                tax_t += tax
                need[prod["id"]] = need.get(prod["id"], Decimal(0)) + qty
                lines.append({
                    "product_id": prod["id"], "sku": prod["sku"], "name": prod["name"],
                    "unit": prod["unit"], "qty": float(qty), "price": float(price),
                    "unit_cost": float(money(Decimal(str(prod["cost"])))),
                    "discount_pct": float(pct), "discount": float(disc),
                    "tax_rate": float(rate), "taxable": float(taxable),
                    "tax": float(tax), "total": float(taxable + tax),
                })

            # 2) stock check
            if not st["allow_negative_stock"]:
                for pid, wanted in need.items():
                    prod = self._find("products", pid, "Item")
                    if Decimal(str(prod["stock"])) < wanted:
                        raise ApiError(409, f"Only {prod['stock']:g} {prod['unit']} of {prod['name']} in stock")

            # 3) totals and payment
            raw_total = taxable_t + tax_t
            grand = raw_total.quantize(Decimal("1"), ROUND_HALF_UP) if st["round_off"] else raw_total
            paid = money(dec(p.get("paid"), "Amount paid", Decimal(0)))
            if paid < 0:
                raise ApiError(400, "Amount paid cannot be negative")
            if mobile and p.get("payment_method") == "Credit" and paid != 0:
                raise ApiError(400, "Credit transactions cannot include an upfront payment")
            if mobile and p.get("payment_method") in ("Cash", "UPI") and paid > grand:
                raise ApiError(400, "Amount paid cannot be more than the bill total")
            if mobile and p.get("payment_method") in ("Cash", "UPI") and grand > 0 and paid == 0:
                raise ApiError(400, "Use Credit for a transaction with no upfront payment")
            paid = min(paid, grand)
            # 4) apply
            n = self._next("invoice")
            stamp = now()
            inv = {
                "id": n,
                "number": f"{st['invoice_prefix']}{n:05d}",
                "date": stamp,
                "customer_id": customer["id"] if customer else None,
                "customer": {
                    "name": customer["name"] if customer else "Walk-in customer",
                    "phone": customer["phone"] if customer else "",
                    "address": customer["address"] if customer else "",
                    "gstin": customer["gstin"] if customer else "",
                },
                "items": lines,
                "subtotal": float(gross_t),
                "discount_total": float(disc_t),
                "tax_total": float(tax_t),
                "round_off": float(grand - raw_total),
                "grand_total": float(grand),
                "payments": [{"date": stamp, "amount": float(paid), "method": method}] if paid > 0 else [],
                "paid": 0.0, "balance": 0.0, "status": "unpaid",
                "notes": text(p.get("notes"), 200),
            }
            self._recalc(inv)
            for pid, qty in need.items():
                prod = self._find("products", pid, "Item")
                prod["stock"] = float(qty_round(Decimal(str(prod["stock"])) - qty))
                self._log_stock(prod, -qty, "Sale", inv["number"])
            self.data["invoices"].append(inv)
            self._commit()
            return inv

    def get_invoice(self, iid):
        with self.lock:
            inv = self._find("invoices", iid, "Invoice")
            self._recalc(inv)
            return inv

    def list_invoices(self, q):
        with self.lock:
            term = qs(q, "q").lower()
            status = qs(q, "status", "all")
            cid = qs(q, "customer_id")
            year = financial_year_bounds(qs(q, "financial_year", "all"))
            limit = min(to_int(qs(q, "limit", "300"), "Limit"), 2000)
            rows = []
            for inv in reversed(self.data["invoices"]):
                self._recalc(inv)
                if not date_in_financial_year(inv["date"], year):
                    continue
                if status == "due":
                    if inv["status"] not in ("unpaid", "partial"):
                        continue
                elif status != "all" and inv["status"] != status:
                    continue
                if cid and str(inv["customer_id"]) != cid:
                    continue
                if term and term not in inv["number"].lower() and term not in inv["customer"]["name"].lower():
                    continue
                rows.append({k: v for k, v in inv.items() if k not in ("items", "payments")})
                if len(rows) >= limit:
                    break
            return rows

    def void_invoice(self, iid, p):
        with self.lock:
            inv = self._find("invoices", iid, "Invoice")
            if inv["status"] == "void":
                raise ApiError(409, "This bill is already void")
            for li in inv["items"]:
                prod = next((x for x in self.data["products"] if x["id"] == li["product_id"]), None)
                if prod:
                    back = qty_round(Decimal(str(li["qty"])))
                    prod["stock"] = float(qty_round(Decimal(str(prod["stock"])) + back))
                    self._log_stock(prod, back, "Bill voided", inv["number"])
            inv["status"] = "void"
            inv["voided_at"] = now()
            inv["void_reason"] = text(p.get("reason"), 120)
            self._commit()
            return inv

    def add_payment(self, iid, p):
        with self.lock:
            inv = self._find("invoices", iid, "Invoice")
            self._recalc(inv)
            if inv["status"] == "void":
                raise ApiError(409, "This bill is void")
            amount = money(dec(p.get("amount"), "Amount"))
            if amount <= 0:
                raise ApiError(400, "Amount must be more than zero")
            if amount > Decimal(str(inv["total_due"])):
                raise ApiError(400, f"Amount is more than the total due of {inv['total_due']:.2f}")
            method = p.get("method") if p.get("method") in PAY_METHODS else "Cash"
            principal_amount = min(amount, Decimal(str(inv["principal_balance"])))
            interest_amount = amount - principal_amount
            inv["payments"].append({
                "date": now(), "amount": float(amount), "method": method,
                "principal_amount": float(principal_amount),
                "interest_amount": float(interest_amount),
            })
            self._recalc(inv)
            self._commit()
            return inv

    # -- bookkeeping ------------------------------------------------------ #
    def save_expense(self, p):
        with self.lock:
            amount = money(dec(p.get("amount"), "Amount"))
            if amount <= 0:
                raise ApiError(400, "Amount must be more than zero")
            method = p.get("method") if p.get("method") in PAY_METHODS else "Cash"
            expense = {
                "id": self._next("expense"),
                "date": now(),
                "category": text(p.get("category"), 60) or "Other",
                "party": text(p.get("party"), 120),
                "reference": text(p.get("reference"), 60),
                "amount": float(amount),
                "method": method,
                "notes": text(p.get("notes"), 240),
            }
            self.data["expenses"].append(expense)
            self._commit()
            return expense

    def list_expenses(self, q):
        with self.lock:
            year = financial_year_bounds(qs(q, "financial_year", "all"))
            limit = min(to_int(qs(q, "limit", "500"), "Limit"), 2000)
            rows = [e for e in reversed(self.data["expenses"])
                    if date_in_financial_year(e["date"], year)]
            return rows[:limit]

    def accounts_summary(self, q=None):
        with self.lock:
            q = q or {}
            year = financial_year_bounds(qs(q, "financial_year", "all"))
            selected = [inv for inv in self.data["invoices"]
                        if date_in_financial_year(inv["date"], year)]
            for inv in selected:
                self._recalc(inv)
            live = [inv for inv in selected if inv["status"] != "void"]
            expenses = [e for e in self.data["expenses"]
                        if date_in_financial_year(e["date"], year)]
            net_sales = round(sum(inv["subtotal"] - inv["discount_total"] for inv in live), 2)
            cogs = float(round(sum((
                money(Decimal(str(line["unit_cost"])) * Decimal(str(line["qty"])))
                for inv in live for line in inv["items"] if "unit_cost" in line
            ), Decimal(0)), 2))
            uncosted_sales = round(sum(
                line["taxable"] for inv in live for line in inv["items"] if "unit_cost" not in line
            ), 2)
            cash_in_by_method, cash_out_by_method = {}, {}
            for inv in self.data["invoices"]:
                if inv["status"] == "void":
                    continue
                for payment in inv.get("payments", []):
                    if date_in_financial_year(payment["date"], year):
                        method = payment.get("method", "Other")
                        cash_in_by_method[method] = cash_in_by_method.get(method, 0) + payment["amount"]
            for expense in expenses:
                method = expense.get("method", "Other")
                cash_out_by_method[method] = cash_out_by_method.get(method, 0) + expense["amount"]
            customers = self.list_customers()
            credit_customers = [{
                "id": customer["id"], "name": customer["name"], "phone": customer["phone"],
                "principal_due": customer["principal_due"], "interest_due": customer["interest_due"],
                "credit_interest_monthly": customer["credit_interest_monthly"],
                "total_due": customer["due"],
            } for customer in customers if customer["due"] > 0]
            credit_customers.sort(key=lambda customer: customer["total_due"], reverse=True)
            collected = round(sum(
                payment["amount"] for inv in self.data["invoices"] if inv["status"] != "void"
                for payment in inv["payments"]
                if date_in_financial_year(payment["date"], year)
            ), 2)
            spent = round(sum(e["amount"] for e in expenses), 2)
            return {
                "year_collected": collected,
                "year_expenses": spent,
                "year_net_cash": round(collected - spent, 2),
                "receivables": round(sum(inv["total_due"] for inv in live), 2),
                "year_tax_billed": round(sum(inv["tax_total"] for inv in live), 2),
                "year_expense_count": len(expenses),
                "net_sales": net_sales,
                "cost_of_goods_sold": cogs,
                "gross_profit": round(net_sales - cogs, 2),
                "uncosted_sales": uncosted_sales,
                "income_statement_expenses": spent,
                "net_operating_profit": round(net_sales - cogs - spent, 2),
                "cash_in_by_method": {method: round(amount, 2) for method, amount in cash_in_by_method.items()},
                "cash_out_by_method": {method: round(amount, 2) for method, amount in cash_out_by_method.items()},
                "credit_customers": credit_customers,
            }

    # -- reports ----------------------------------------------------------- #
    def financial_years(self):
        clock = datetime.now()
        current = clock.year if clock.month >= 4 else clock.year - 1
        starts = {current}
        records = self.data["invoices"] + self.data["expenses"]
        records += [payment for inv in self.data["invoices"] for payment in inv.get("payments", [])]
        for record in records:
            try:
                day = datetime.strptime(record["date"][:10], "%Y-%m-%d")
            except (KeyError, TypeError, ValueError):
                continue
            starts.add(day.year if day.month >= 4 else day.year - 1)
        return {
            "current": str(current),
            "years": [
                {"start": str(start), "label": f"FY {start}-{str(start + 1)[-2:]}"}
                for start in sorted(starts, reverse=True)
            ],
        }

    def dashboard(self, q=None):
        with self.lock:
            q = q or {}
            clock = datetime.now()
            today, month = clock.strftime("%Y-%m-%d"), clock.strftime("%Y-%m")
            year = financial_year_bounds(qs(q, "financial_year", "all"))
            selected = [i for i in self.data["invoices"]
                        if date_in_financial_year(i["date"], year)]
            for inv in selected:
                self._recalc(inv)
            live = [i for i in selected if i["status"] != "void"]

            def total(rows):
                return round(sum(i["grand_total"] for i in rows), 2)

            week = []
            for back in range(6, -1, -1):
                day = clock - timedelta(days=back)
                key = day.strftime("%Y-%m-%d")
                week.append({"date": key, "label": day.strftime("%a"),
                             "total": total([i for i in live if i["date"].startswith(key)])})

            top = {}
            for inv in live:
                for li in inv["items"]:
                    row = top.setdefault(li["name"], {"name": li["name"], "qty": 0.0, "revenue": 0.0, "unit": li["unit"]})
                    row["qty"] += li["qty"]
                    row["revenue"] += li["total"]
            top_rows = sorted(top.values(), key=lambda r: r["revenue"], reverse=True)[:5]
            for r in top_rows:
                r["qty"], r["revenue"] = round(r["qty"], 3), round(r["revenue"], 2)

            active = [p for p in self.data["products"] if p["active"]]
            low = sorted((p for p in active if p["stock"] <= p["low_stock"]), key=lambda p: p["stock"])
            return {
                "today_sales": total([i for i in live if i["date"].startswith(today)]),
                "today_count": sum(1 for i in live if i["date"].startswith(today)),
                "month_sales": total([i for i in live if i["date"].startswith(month)]),
                "year_sales": total(live),
                "year_count": len(live),
                "outstanding": round(sum(i["total_due"] for i in live), 2),
                "stock_cost": round(sum(p["stock"] * p["cost"] for p in active), 2),
                "stock_retail": round(sum(p["stock"] * p["price"] for p in active), 2),
                "item_count": len(active),
                "week": week,
                "low_stock": [{"id": p["id"], "name": p["name"], "stock": p["stock"],
                               "unit": p["unit"], "low_stock": p["low_stock"]} for p in low[:10]],
                "recent": [{k: v for k, v in i.items() if k not in ("items", "payments")}
                           for i in list(reversed(selected))[:6]],
                "top": top_rows,
            }

    def invoices_csv(self, q=None):
        with self.lock:
            q = q or {}
            year = financial_year_bounds(qs(q, "financial_year", "all"))
            out = io.StringIO()
            w = csv.writer(out)
            w.writerow(["Invoice", "Date", "Customer", "Phone", "Subtotal", "Discount", "Tax",
                        "Round off", "Total", "Interest accrued", "Interest paid",
                        "Interest balance", "Paid", "Balance", "Total due", "Status"])
            for i in self.data["invoices"]:
                if not date_in_financial_year(i["date"], year):
                    continue
                self._recalc(i)
                w.writerow([i["number"], i["date"], csv_safe(i["customer"]["name"]),
                            csv_safe(i["customer"]["phone"]), i["subtotal"], i["discount_total"],
                            i["tax_total"], i["round_off"], i["grand_total"], i["interest_accrued"],
                            i["interest_paid"], i["interest_balance"], i["paid"], i["balance"],
                            i["total_due"], i["status"]])
            return out.getvalue().encode("utf-8-sig")  # BOM so Excel reads it correctly

    def expenses_csv(self, q=None):
        with self.lock:
            q = q or {}
            year = financial_year_bounds(qs(q, "financial_year", "all"))
            out = io.StringIO()
            writer = csv.writer(out)
            writer.writerow(["Date", "Category", "Party", "Reference", "Amount", "Method", "Notes"])
            for expense in self.data["expenses"]:
                if not date_in_financial_year(expense["date"], year):
                    continue
                writer.writerow([expense["date"], csv_safe(expense["category"]), csv_safe(expense["party"]),
                                 csv_safe(expense["reference"]), expense["amount"], expense["method"],
                                 csv_safe(expense["notes"])])
            return out.getvalue().encode("utf-8-sig")

    def backup_json(self):
        with self.lock:
            return json.dumps(self.data, indent=2, ensure_ascii=False).encode("utf-8")


def qs(query, key, default=""):
    return (query.get(key) or [default])[0]


def business_activity(method, path, result, store):
    if method not in ("POST", "PUT", "DELETE"):
        return None
    if path == "/api/settings":
        return "Shop settings updated", ""
    if path == "/api/invoices" and isinstance(result, dict):
        customer = result.get("customer", {}).get("name", "Walk-in customer")
        return "Invoice created", (
            f"{result.get('number', '')} for {customer}; total {result.get('grand_total', 0):.2f}, "
            f"paid {result.get('paid', 0):.2f}, balance {result.get('balance', 0):.2f}"
        )
    match = re.fullmatch(r"/api/invoices/(\d+)/void", path)
    if match and isinstance(result, dict):
        return "Invoice voided", f"{result.get('number', match.group(1))}; reason: {result.get('void_reason') or 'not specified'}"
    match = re.fullmatch(r"/api/invoices/(\d+)/payments", path)
    if match and isinstance(result, dict):
        payment = result.get("payments", [{}])[-1]
        return "Payment recorded", (
            f"{result.get('number', match.group(1))}; {payment.get('amount', 0):.2f} by "
            f"{payment.get('method', 'unknown')}; balance {result.get('balance', 0):.2f}"
        )
    if path == "/api/expenses" and isinstance(result, dict):
        return "Expense recorded", f"{result.get('category', 'Other')}; amount {result.get('amount', 0):.2f}"
    if path == "/api/products" and isinstance(result, dict):
        return "Item created", result.get("name", "")
    match = re.fullmatch(r"/api/products/(\d+)", path)
    if match:
        if method == "DELETE":
            action = "Item archived" if result.get("archived") else "Item deleted"
            return action, f"Item ID {match.group(1)}"
        if isinstance(result, dict):
            return "Item updated", result.get("name", "")
    match = re.fullmatch(r"/api/products/(\d+)/restore", path)
    if match:
        return "Item restored", result.get("name", f"Item ID {match.group(1)}")
    if path == "/api/stock" and isinstance(result, dict):
        stock = store.data["stock_log"][-1]
        return "Stock adjusted", (
            f"{result.get('name', 'Item')}; change {stock.get('change', 0):g} "
            f"{result.get('unit', '')}; reason: {stock.get('reason', '')}"
        )
    if path == "/api/customers" and isinstance(result, dict):
        return "Customer created", result.get("name", "")
    match = re.fullmatch(r"/api/customers/(\d+)", path)
    if match:
        if method == "DELETE":
            return "Customer deleted", f"Customer ID {match.group(1)}"
        if isinstance(result, dict):
            return "Customer updated", result.get("name", "")
    return None


# --------------------------------------------------------------------------- #
# HTTP layer
# --------------------------------------------------------------------------- #
class Raw:
    """A non-JSON response (file download)."""
    def __init__(self, body, ctype, filename=None):
        self.body, self.ctype, self.filename = body, ctype, filename


def build_routes(store):
    g = lambda m: int(m.group(1))
    return [
        ("GET", r"/api/info", lambda m, q, b: store.info),
        ("GET", r"/api/upi-qr", lambda m, q, b: Raw(
            store.upi_qr(q), "image/svg+xml; charset=utf-8"
        )),
        ("POST", r"/api/client-errors", lambda m, q, b: (
            store.log_activity("technical", "Browser error",
                               f"{text(b.get('message'), 500)}\n{text(b.get('stack'), 1200)}", 500)
            or {"recorded": True}
        )),
        ("GET", r"/api/financial-years", lambda m, q, b: store.financial_years()),
        ("GET", r"/api/settings", lambda m, q, b: store.data["settings"]),
        ("PUT", r"/api/settings", lambda m, q, b: store.update_settings(b)),
        ("GET", r"/api/dashboard", lambda m, q, b: store.dashboard(q)),
        ("GET", r"/api/accounts", lambda m, q, b: store.accounts_summary(q)),
        ("GET", r"/api/expenses", lambda m, q, b: store.list_expenses(q)),
        ("POST", r"/api/expenses", lambda m, q, b: store.save_expense(b)),
        ("GET", r"/api/products", lambda m, q, b: store.list_products()),
        ("POST", r"/api/products", lambda m, q, b: store.save_product(b)),
        ("PUT", r"/api/products/(\d+)", lambda m, q, b: store.save_product(b, g(m))),
        ("DELETE", r"/api/products/(\d+)", lambda m, q, b: store.delete_product(g(m))),
        ("POST", r"/api/products/(\d+)/restore", lambda m, q, b: store.restore_product(g(m))),
        ("GET", r"/api/stock", lambda m, q, b: store.list_stock_log(q)),
        ("POST", r"/api/stock", lambda m, q, b: store.adjust_stock(b)),
        ("GET", r"/api/customers", lambda m, q, b: store.list_customers()),
        ("POST", r"/api/customers", lambda m, q, b: store.save_customer(b)),
        ("PUT", r"/api/customers/(\d+)", lambda m, q, b: store.save_customer(b, g(m))),
        ("DELETE", r"/api/customers/(\d+)", lambda m, q, b: store.delete_customer(g(m))),
        ("GET", r"/api/invoices", lambda m, q, b: store.list_invoices(q)),
        ("POST", r"/api/invoices", lambda m, q, b: store.create_invoice(b)),
        ("GET", r"/api/invoices/(\d+)", lambda m, q, b: store.get_invoice(g(m))),
        ("POST", r"/api/invoices/(\d+)/void", lambda m, q, b: store.void_invoice(g(m), b)),
        ("POST", r"/api/invoices/(\d+)/payments", lambda m, q, b: store.add_payment(g(m), b)),
        ("GET", r"/api/export/invoices\.csv",
         lambda m, q, b: Raw(store.invoices_csv(q), "text/csv; charset=utf-8", "invoices.csv")),
        ("GET", r"/api/export/expenses\.csv",
         lambda m, q, b: Raw(store.expenses_csv(q), "text/csv; charset=utf-8", "expenses.csv")),
        ("GET", r"/api/export/backup\.json",
         lambda m, q, b: Raw(store.backup_json(), "application/json",
                             f"stockbill-backup-{datetime.now():%Y%m%d}.json")),
    ]


def make_handler(store):
    routes = [(meth, re.compile(pat), fn) for meth, pat, fn in build_routes(store)]
    desktop_sessions = set()
    mobile_pin_state = {
        "salt": store.data["security"].get("mobile_pin_salt", ""),
        "hash": store.data["security"].get("mobile_pin_hash", ""),
    }

    def account_configured():
        security = store.data["security"]
        return bool(
            security.get("account_email")
            and security.get("account_password_salt")
            and security.get("account_password_hash")
        )

    def mobile_pin_matches(candidate):
        return stored_pin_matches(candidate, mobile_pin_state["salt"], mobile_pin_state["hash"])
    page = PAGE.encode("utf-8")
    mobile_page = MOBILE_PAGE.encode("utf-8")
    manifest = json.dumps({
        "name": APP_NAME, "short_name": APP_NAME, "start_url": "/", "display": "standalone",
        "background_color": "#F1F4F2", "theme_color": "#14303A",
        "icons": [{"src": "/icon.svg", "sizes": "any", "type": "image/svg+xml", "purpose": "any"}],
    }).encode()
    icon = (
        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64"><rect width="64" height="64" rx="14" fill="#14303A"/>'
        '<path d="M18 12h28v40l-7-4-7 4-7-4-7 4z" fill="#F2A900"/><path d="M25 24h14M25 32h14" stroke="#14303A" '
        'stroke-width="3" stroke-linecap="round"/></svg>'
    ).encode()

    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"
        server_version = "StockBill"

        def log_message(self, *args):
            pass  # keep the console quiet

        # -- plumbing -- #
        def _send(self, status, body, ctype, extra=None):
            try:
                self.send_response(status)
                self.send_header("Content-Type", ctype)
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-store")
                self.send_header("X-Content-Type-Options", "nosniff")
                for k, v in (extra or {}).items():
                    self.send_header(k, v)
                self.end_headers()
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError) as e:
                store.log_activity(
                    "technical", "Client disconnected before response completed",
                    f"Remote address {self.client_address[0]}: {e}", status
                )

        def _json(self, status, obj):
            self._send(status, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                       "application/json; charset=utf-8")

        def _read_body(self):
            length = int(self.headers.get("Content-Length") or 0)
            if length > 5_000_000:
                self.close_connection = True
                raise ApiError(413, "Request is too large")
            raw = self.rfile.read(length) if length else b""
            if not raw:
                return {}
            # Requiring JSON blocks "simple" cross-site form posts from other web pages.
            if "application/json" not in (self.headers.get("Content-Type") or ""):
                raise ApiError(415, "Content-Type must be application/json")
            try:
                body = json.loads(raw.decode("utf-8"))
            except (ValueError, UnicodeDecodeError):
                raise ApiError(400, "Request body is not valid JSON")
            if not isinstance(body, dict):
                raise ApiError(400, "Request body must be a JSON object")
            return body

        def _dispatch(self, method):
            path = ""
            failure_category = "technical"
            try:
                url = urlparse(self.path)
                path = url.path
                body = self._read_body()  # always drain the body first (keep-alive safe)
                if method == "GET" and path in ("/", "/index.html"):
                    return self._send(200, page, "text/html; charset=utf-8")
                if method == "GET" and path in ("/mobile", "/mobile/"):
                    return self._send(200, mobile_page, "text/html; charset=utf-8")
                if method == "GET" and path == "/manifest.json":
                    return self._send(200, manifest, "application/manifest+json")
                if method == "GET" and path == "/icon.svg":
                    return self._send(200, icon, "image/svg+xml")
                if path == "/api/login":
                    if method == "GET":
                        return self._json(200, {"account_configured": account_configured()})
                    if method == "POST":
                        failure_category = "security"
                        email = normalize_email(body.get("email"))
                        password = body.get("password", "")
                        with store.lock:
                            if not account_configured():
                                if self.client_address[0] not in ("127.0.0.1", "::1"):
                                    raise ApiError(403, "Create the first account from the computer running StockBill")
                                if not valid_email(email):
                                    raise ApiError(400, "Enter a valid email address")
                                if not valid_password(password):
                                    raise ApiError(400, "Password must be 8 to 256 characters")
                                if body.get("confirm_password") != password:
                                    raise ApiError(400, "Password and confirmation do not match")
                                store.update_account(email, password)
                            else:
                                security = store.data["security"]
                                if (
                                    email != security.get("account_email")
                                    or not valid_password(password)
                                    or not stored_password_matches(
                                        password,
                                        security.get("account_password_salt", ""),
                                        security.get("account_password_hash", ""),
                                    )
                                ):
                                    raise ApiError(401, "Incorrect email or password")
                        session_token = secrets.token_urlsafe(32)
                        desktop_sessions.add(session_token)
                        store.info["account_email"] = email
                        store.log_activity(
                            "security", "Sign-in succeeded",
                            f"Remote address {self.client_address[0]}", 200
                        )
                        return self._json(200, {
                            "authenticated": True, "session_token": session_token,
                            "account_email": email,
                        })
                    raise ApiError(405, "Method not allowed")
                if path == "/api/mobile/login":
                    if method == "GET":
                        return self._json(200, {"pin_enabled": bool(mobile_pin_state["hash"])})
                    if method == "POST":
                        failure_category = "security"
                        if not mobile_pin_state["hash"]:
                            raise ApiError(403, "Mobile billing access is not configured")
                        if not mobile_pin_matches(body.get("pin", "")):
                            raise ApiError(401, "Incorrect mobile PIN")
                        store.log_activity(
                            "security", "Mobile billing sign-in succeeded",
                            f"Remote address {self.client_address[0]}", 200
                        )
                        return self._json(200, {"authenticated": True})
                    raise ApiError(405, "Method not allowed")
                if not path.startswith("/api/"):
                    raise ApiError(404, "Not found")
                if path.startswith("/api/mobile/"):
                    failure_category = "security"
                    if not mobile_pin_state["hash"] or not mobile_pin_matches(
                            self.headers.get("X-Mobile-Pin") or ""):
                        raise ApiError(401, "Mobile PIN required")
                    query = parse_qs(url.query)
                    if method == "GET" and path == "/api/mobile/products":
                        products = store.list_products()
                        result = [{
                            key: product[key]
                            for key in ("id", "name", "sku", "category", "unit", "price",
                                        "tax_rate", "stock", "low_stock", "active")
                        } for product in products if product["active"]]
                    elif method == "GET" and path == "/api/mobile/customers":
                        result = [{
                            key: customer[key]
                            for key in ("id", "name", "phone", "due", "interest_due")
                        } for customer in store.list_customers()]
                    elif method == "GET" and path == "/api/mobile/settings":
                        settings = store.data["settings"]
                        result = {key: settings[key] for key in (
                            "business_name", "currency", "round_off", "allow_negative_stock",
                            "upi_id", "country_code",
                        )}
                    elif method == "GET" and path == "/api/mobile/upi-qr":
                        return self._send(
                            200, store.upi_qr(query), "image/svg+xml; charset=utf-8"
                        )
                    elif method == "POST" and path == "/api/mobile/invoices":
                        payment_method = body.get("payment_method")
                        if payment_method not in ("Cash", "UPI", "Credit"):
                            raise ApiError(400, "Choose Cash, UPI, or Credit")
                        if payment_method == "Credit" and (
                                not body.get("customer_id")
                                or dec(body.get("paid"), "Amount paid", Decimal(0)) != 0):
                            raise ApiError(400, "Credit transactions require a customer and no upfront payment")
                        result = store.create_invoice(body, mobile=True)
                        activity = business_activity(method, "/api/invoices", result, store)
                        if activity:
                            store.log_activity("business", activity[0], activity[1], 200)
                    else:
                        raise ApiError(404, "Mobile endpoint not found")
                    if method == "POST" and path == "/api/mobile/invoices":
                        result = {
                            **result,
                            "items": [
                                {key: value for key, value in line.items() if key != "unit_cost"}
                                for line in result["items"]
                            ],
                        }
                    payload = json.dumps(result, ensure_ascii=False).encode("utf-8")
                    return self._send(200, payload, "application/json; charset=utf-8")
                if not account_configured():
                    failure_category = "security"
                    raise ApiError(401, "Create an account before accessing StockBill")
                session_token = self.headers.get("X-Session-Token") or ""
                if session_token not in desktop_sessions:
                    failure_category = "security"
                    raise ApiError(401, "Sign in required")
                query = parse_qs(url.query)
                if path == "/api/logout":
                    failure_category = "security"
                    if method != "POST":
                        raise ApiError(405, "Method not allowed")
                    store.log_activity(
                        "security", "Signed out",
                        f"Remote address {self.client_address[0]}", 200
                    )
                    desktop_sessions.discard(session_token)
                    return self._json(200, {"logged_out": True})
                if path == "/api/account":
                    failure_category = "security"
                    if method != "POST":
                        raise ApiError(405, "Method not allowed")
                    with store.lock:
                        security = store.data["security"]
                        current_password = body.get("current_password", "")
                        if not stored_password_matches(
                            current_password,
                            security.get("account_password_salt", ""),
                            security.get("account_password_hash", ""),
                        ):
                            raise ApiError(401, "Current password is incorrect")
                        new_password = body.get("new_password") or None
                        if not new_password and body.get("confirm_password"):
                            raise ApiError(400, "Enter a new password before confirming it")
                        if new_password is not None:
                            if not valid_password(new_password):
                                raise ApiError(400, "New password must be 8 to 256 characters")
                            if body.get("confirm_password") != new_password:
                                raise ApiError(400, "New password and confirmation do not match")
                        email = store.update_account(body.get("email"), new_password)
                        store.info["account_email"] = email
                        session_token = secrets.token_urlsafe(32)
                        desktop_sessions.clear()
                        desktop_sessions.add(session_token)
                    store.log_activity("security", "Account updated", email, 200)
                    return self._json(200, {
                        "account_email": email, "session_token": session_token
                    })
                if method == "GET" and path == "/api/mobile-access-qr":
                    lan_url = store.info.get("lan_url")
                    if not lan_url:
                        raise ApiError(400, "Mobile access is unavailable when the server is bound to localhost")
                    qr = qrcode.QRCode(box_size=8, border=4, error_correction=qrcode.constants.ERROR_CORRECT_M)
                    qr.add_data(lan_url + "/mobile")
                    qr.make(fit=True)
                    image = qr.make_image(image_factory=SvgPathImage)
                    output = io.BytesIO()
                    image.save(output)
                    return self._send(200, output.getvalue(), "image/svg+xml; charset=utf-8")
                if path == "/api/mobile-pin":
                    failure_category = "security"
                    if method != "POST":
                        raise ApiError(405, "Method not allowed")
                    if body.get("disable"):
                        store.disable_mobile_pin()
                        mobile_pin_state.update(salt="", hash="")
                        store.info["mobile_pin_enabled"] = False
                        store.log_activity(
                            "security", "Mobile billing access disabled",
                            "The mobile access PIN was removed", 200
                        )
                        return self._json(200, {"mobile_pin_enabled": False})
                    new_pin = body.get("new_pin")
                    if not valid_pin(new_pin):
                        raise ApiError(400, "Mobile PIN must contain 4 to 12 digits")
                    store.update_mobile_pin(new_pin)
                    mobile_pin_state["salt"] = store.data["security"]["mobile_pin_salt"]
                    mobile_pin_state["hash"] = store.data["security"]["mobile_pin_hash"]
                    store.info["mobile_pin_enabled"] = True
                    store.log_activity("security", "Mobile billing PIN updated", "", 200)
                    return self._json(200, {"mobile_pin_enabled": True})
                path_ok = False
                for meth, pattern, fn in routes:
                    m = pattern.fullmatch(path)
                    if not m:
                        continue
                    path_ok = True
                    if meth != method:
                        continue
                    with store.lock:  # compute AND serialize while no other request can modify the data
                        result = fn(m, query, body)
                        activity = business_activity(method, path, result, store)
                        if activity:
                            store.log_activity("business", activity[0], activity[1], 200)
                        payload = None if isinstance(result, Raw) else json.dumps(result, ensure_ascii=False).encode("utf-8")
                    if isinstance(result, Raw):
                        extra = {"Content-Disposition": f'attachment; filename="{result.filename}"'} if result.filename else {}
                        return self._send(200, result.body, result.ctype, extra)
                    return self._send(200, payload, "application/json; charset=utf-8")
                raise ApiError(405 if path_ok else 404, "Method not allowed" if path_ok else "Not found")
            except ApiError as e:
                if path.startswith("/api/"):
                    store.log_activity(
                        failure_category, "Request rejected",
                        f"{method} {path} returned HTTP {e.status}: {e.message}", e.status
                    )
                self._json(e.status, {"error": e.message})
            except Exception:
                stack = traceback.format_exc()
                traceback.print_exc()
                store.log_activity(
                    "technical", "Server exception", f"{method} {path}\n{stack}", 500
                )
                self._json(500, {"error": "Something went wrong on the server"})

        def do_GET(self):
            self._dispatch("GET")

        def do_POST(self):
            self._dispatch("POST")

        def do_PUT(self):
            self._dispatch("PUT")

        def do_DELETE(self):
            self._dispatch("DELETE")

    return Handler


# --------------------------------------------------------------------------- #
# Demo data + startup
# --------------------------------------------------------------------------- #
DEMO_ITEMS = [
    # name, category, unit, price, cost, tax %, stock, low-stock alert
    ("NPK 19:19:19 water-soluble fertilizer 1 kg", "Fertilizer", "pack", 420, 340, 5, 35, 8),
    ("Urea fertilizer 45 kg", "Fertilizer", "bag", 270, 240, 5, 20, 5),
    ("DAP fertilizer 50 kg", "Fertilizer", "bag", 1350, 1200, 5, 16, 4),
    ("Organic compost 5 kg", "Fertilizer", "bag", 180, 130, 5, 42, 10),
    ("Micronutrient mixture 1 kg", "Fertilizer", "pack", 260, 195, 5, 28, 6),
    ("Neem-based insecticide 1 L", "Pesticide", "btl", 350, 245, 18, 24, 6),
    ("Imidacloprid 17.8% SL 100 ml", "Pesticide", "btl", 190, 132, 18, 30, 8),
    ("Mancozeb 75% WP 500 g", "Pesticide", "pack", 240, 170, 18, 26, 6),
    ("Glyphosate 41% SL 1 L", "Pesticide", "btl", 520, 390, 18, 18, 5),
]


def seed_demo(store):
    if store.data["products"]:
        return
    for name, cat, unit, price, cost, tax, stock, low in DEMO_ITEMS:
        store.save_product({"name": name, "category": cat, "unit": unit, "price": price, "cost": cost,
                            "tax_rate": tax, "stock": stock, "low_stock": low})
    store.save_customer({"name": "Green Fields Farm", "phone": "9811000001"})
    store.save_customer({"name": "Agri Test Customer", "phone": "9811000002"})


class Server(ThreadingHTTPServer):
    request_queue_size = 128  # default backlog is 5, which drops connections when several devices bill at once
    daemon_threads = True


def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))  # no packets are sent; just picks the right interface
        return s.getsockname()[0]
    except OSError:
        return None
    finally:
        s.close()


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=f"{APP_NAME}: inventory and billing (JSON file storage)")
    ap.add_argument("--data", default=os.path.join(here, "stockbill_data.json"), help="path of the JSON data file")
    ap.add_argument("--port", type=int, default=8000)
    ap.add_argument("--host", default="0.0.0.0", help="0.0.0.0 = reachable from phones on your Wi-Fi; 127.0.0.1 = this computer only")
    ap.add_argument("--demo", action="store_true", help="add sample items and customers if the data file is empty")
    ap.add_argument("--no-browser", action="store_true", help="don't open a browser window on start")
    ap.add_argument("--tls-cert", help="TLS certificate file (enables HTTPS and mobile camera scanning)")
    ap.add_argument("--tls-key", help="TLS private key file (required with --tls-cert)")
    args = ap.parse_args()
    if bool(args.tls_cert) != bool(args.tls_key):
        ap.error("--tls-cert and --tls-key must be provided together")

    store = Store(args.data)
    if args.demo:
        seed_demo(store)
    ip = lan_ip() if args.host in ("0.0.0.0", "") else None
    scheme = "https" if args.tls_cert else "http"
    store.info = {
        "data_file": store.path,
        "lan_url": f"{scheme}://{ip}:{args.port}" if ip else None,
        "account_email": store.data["security"].get("account_email", ""),
        "mobile_pin_enabled": bool(store.data["security"]["mobile_pin_hash"]),
    }

    try:
        server = Server((args.host, args.port), make_handler(store))
        if args.tls_cert:
            tls = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            tls.load_cert_chain(args.tls_cert, args.tls_key)
            server.socket = tls.wrap_socket(server.socket, server_side=True)
    except ssl.SSLError as e:
        store.log_activity("technical", "HTTPS startup failed", str(e), 500)
        sys.exit(f"Could not configure HTTPS: {e}")
    except OSError as e:
        store.log_activity("technical", "Server startup failed", str(e), 500)
        sys.exit(f"Could not start on port {args.port}: {e}\nTry another port, e.g.  --port 8080")

    store.log_activity("technical", "Server started", f"Listening on {args.host}:{args.port}", 200)
    local = f"{scheme}://localhost:{args.port}"
    print(f"\n{APP_NAME} is running")
    print(f"  This computer : {local}")
    if store.info["lan_url"]:
        print(f"  Phone/tablet  : {store.info['lan_url']}   (same Wi-Fi)")
    print(f"  Data file     : {store.path}")
    if not store.info["account_email"]:
        print("\n  On first open, create an account with your email and password.")
    if store.info["lan_url"]:
        print("  Mobile billing uses its own PIN. Only share the mobile URL/QR on a trusted Wi-Fi network.")
    print("  Support: Chandra: 9182395594")
    print("\n  Press Ctrl+C to stop.\n")
    if not args.no_browser:
        threading.Timer(0.8, lambda: webbrowser.open(local)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped. Your data is saved.")
    except Exception:
        store.log_activity("technical", "Server stopped unexpectedly", traceback.format_exc(), 500)
        raise
    finally:
        store.log_activity("technical", "Server stopped", "HTTP server closed")
        server.server_close()


# --------------------------------------------------------------------------- #
# Front end (one responsive page; talks to the JSON API above)
# --------------------------------------------------------------------------- #
PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#14303A">
<title>StockBill</title>
<link rel="manifest" href="/manifest.json">
<link rel="icon" href="/icon.svg" type="image/svg+xml">
<style>
:root{
  --ink:#14303A; --ink-2:#1F4756; --paper:#F1F4F2; --card:#fff; --line:#D7DFDB; --line-2:#E8EEEB;
  --text:#15262D; --muted:#5B707A; --brand:#0F766E; --brand-d:#0B5A54; --gold:#F2A900; --gold-d:#D99500;
  --warn:#B45309; --warn-bg:#FEF3E2; --danger:#B42318; --danger-bg:#FDECEA; --ok:#15803D; --ok-bg:#E6F4EA;
  --font: ui-sans-serif, system-ui, -apple-system, "Segoe UI", Roboto, "Noto Sans", "Helvetica Neue", Arial, sans-serif;
}
*{box-sizing:border-box}
html,body{margin:0}
body{font:15px/1.5 var(--font);color:var(--text);background:var(--paper);-webkit-text-size-adjust:100%;touch-action:manipulation}
h1,h2,h3,h4,p{margin:0}
h1{font-size:26px;letter-spacing:-.02em;line-height:1.15}
h2{font-size:16px;letter-spacing:-.005em}
button,input,select,textarea{font:inherit;color:inherit}
.num,.num *{font-variant-numeric:tabular-nums}
.muted{color:var(--muted)}
.ic{width:20px;height:20px;flex:none}
:focus-visible{outline:3px solid #7CC4BB;outline-offset:2px}

/* layout */
#app{display:grid;grid-template-columns:232px minmax(0,1fr);min-height:100vh}
#nav{background:var(--ink);color:#D5E3E0;padding:18px 12px;position:sticky;top:0;height:100vh;display:flex;flex-direction:column;gap:3px;overflow:auto}
.brand{color:#fff;font-weight:800;font-size:19px;letter-spacing:-.02em;padding:4px 10px 18px;line-height:1.2;overflow-wrap:anywhere}
.brand small{display:block;margin-top:2px;font-weight:500;font-size:12px;letter-spacing:0;color:#8FB0AA}
#nav>button{all:unset;box-sizing:border-box;display:flex;align-items:center;gap:12px;padding:11px 12px;border-radius:9px;cursor:pointer;font-weight:600;position:relative}
#nav>button:hover{background:rgba(255,255,255,.07)}
#nav>button.active{background:var(--gold);color:#2A1E00}
#nav>button:focus-visible{outline:3px solid #7CC4BB}
.dot{font-style:normal;background:var(--gold);color:#2A1E00;border-radius:99px;min-width:20px;padding:0 6px;font-size:12px;font-weight:800;text-align:center;line-height:20px;margin-left:auto}
#nav>button.active .dot{background:var(--ink);color:#fff}
main{padding:28px 32px 48px;max-width:1240px;width:100%}
main.transaction-main{max-width:none;padding:18px 24px 40px}
.page-head{display:flex;align-items:flex-end;justify-content:space-between;gap:12px;margin-bottom:20px;flex-wrap:wrap}
.page-head p{margin-top:4px}

/* buttons + inputs */
.btn{display:inline-flex;align-items:center;justify-content:center;gap:8px;border:1px solid transparent;border-radius:9px;padding:10px 16px;font-weight:700;cursor:pointer;text-decoration:none;background:var(--brand);color:#fff;min-height:42px;white-space:nowrap}
.btn:hover{background:var(--brand-d)}
.btn.gold{background:var(--gold);color:#2A1E00}.btn.gold:hover{background:var(--gold-d)}
.btn.ghost{background:#fff;color:var(--text);border-color:var(--line)}.btn.ghost:hover{background:var(--line-2)}
.btn.danger{background:#fff;color:var(--danger);border-color:#EBC3BF}.btn.danger:hover{background:var(--danger-bg)}
.btn.sm{padding:6px 12px;min-height:34px;font-size:14px}
.btn.lg{min-height:52px;font-size:17px}
.btn.block{width:100%}
.btn[disabled]{opacity:.55;cursor:not-allowed}
.btn[hidden]{display:none}
.link{all:unset;color:var(--brand);font-weight:700;cursor:pointer;text-decoration:underline;text-underline-offset:3px}
.icon-btn{all:unset;box-sizing:border-box;width:34px;height:34px;border-radius:8px;display:inline-grid;place-items:center;cursor:pointer;color:var(--muted);flex:none}
.icon-btn:hover{background:var(--line-2);color:var(--text)}
.icon-btn:focus-visible{outline:3px solid #7CC4BB}
input,select,textarea{width:100%;border:1px solid var(--line);border-radius:9px;padding:10px 12px;background:#fff;min-height:42px;font-size:16px}
input:focus,select:focus,textarea:focus{outline:3px solid #B5DDD7;border-color:var(--brand)}
label.f{display:flex;flex-direction:column;gap:5px;font-size:13.5px;font-weight:600;color:var(--muted)}
label.f input,label.f select,label.f textarea{font-weight:400;color:var(--text)}
label.check{display:flex;align-items:center;gap:10px;font-weight:600}
label.check input{width:20px;height:20px;min-height:0;accent-color:var(--brand)}
.stack{display:flex;flex-direction:column;gap:14px}
.two{display:grid;grid-template-columns:1fr 1fr;gap:12px}
.chips{display:flex;gap:8px;flex-wrap:wrap}
.chip{all:unset;box-sizing:border-box;cursor:pointer;padding:7px 14px;border-radius:99px;border:1px solid var(--line);background:#fff;font-weight:600;font-size:14px}
.chip:hover{background:var(--line-2)}
.chip.on{background:var(--ink);color:#fff;border-color:var(--ink)}
.chip:focus-visible{outline:3px solid #7CC4BB}
.search{position:relative;flex:1;min-width:180px}
.search .ic{position:absolute;left:12px;top:11px;color:var(--muted)}
.search input{padding-left:40px}
.toolbar{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-bottom:14px}
.badge{display:inline-block;border-radius:99px;padding:2px 10px;font-size:13px;font-weight:700;background:var(--line-2);color:var(--muted);white-space:nowrap}
.badge.ok{background:var(--ok-bg);color:var(--ok)}.badge.warn{background:var(--warn-bg);color:var(--warn)}.badge.bad{background:var(--danger-bg);color:var(--danger)}

/* cards + lists */
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:18px}
.card h2{margin-bottom:12px}
.tiles{display:grid;grid-template-columns:repeat(4,1fr);gap:12px;margin-bottom:16px}
.tile{background:#fff;border:1px solid var(--line);border-radius:12px;padding:14px 16px;display:flex;flex-direction:column;gap:2px}
.tile b{font-size:24px;letter-spacing:-.02em;line-height:1.2}
.grid2{display:grid;grid-template-columns:1fr 1fr;gap:16px}
.list{background:#fff;border:1px solid var(--line);border-radius:12px;overflow:hidden}
.row{display:grid;align-items:center;gap:6px 14px;padding:12px 16px;border-bottom:1px solid var(--line-2);width:100%;text-align:left;background:none;border-left:0;border-right:0;border-top:0}
.row:last-child{border-bottom:0}
button.row{cursor:pointer}button.row:hover{background:#F7FAF8}
.r-main{display:flex;flex-direction:column;min-width:0}.r-main b{overflow-wrap:anywhere}
.r-main span{font-size:13.5px}
.r-right{text-align:right}
.archived{opacity:.6}
.prod{grid-template-columns:minmax(0,1fr) 150px 130px 150px}
.cust{grid-template-columns:minmax(0,1fr) 150px 160px}
.credit-row{grid-template-columns:minmax(0,1fr) minmax(260px,1fr) auto 90px}
.invr{grid-template-columns:130px minmax(0,1fr) 150px 110px 90px}
.expense-row{grid-template-columns:minmax(0,1fr) 170px 90px 130px}
.expense-row{grid-template-columns:minmax(0,1fr) 170px 90px 130px}
.expense-date{text-align:right}.expense-amount{text-align:right}
.expense-note{grid-column:1/-1;font-size:13.5px}
.upi-qr{display:flex;align-items:center;gap:16px;padding:14px;border:1px solid var(--line);border-radius:12px;background:#fff}
.upi-qr img{width:148px;height:148px;flex:0 0 148px;background:#fff}
.upi-qr img[hidden]{display:none}
.upi-qr-copy{min-width:0}
.upi-qr-copy p{margin-top:4px}
.r-act{display:flex;gap:6px;justify-content:flex-end}
.empty{padding:26px 16px;text-align:center;color:var(--muted)}
.empty .btn{margin-top:12px}
.mini{display:flex;justify-content:space-between;gap:10px;padding:9px 0;border-bottom:1px solid var(--line-2);align-items:center}
.mini:last-child{border-bottom:0}
.shortcut-hint{margin-left:auto;flex:none;padding:2px 6px;border:1px solid currentColor;border-radius:5px;font:600 10px/1.4 var(--font);letter-spacing:.01em;opacity:.78;white-space:nowrap}
.search>.shortcut-hint{position:absolute;right:10px;top:9px;z-index:1;background:#fff}
.search input{padding-right:46px}
.icon-btn[data-act="close"]{width:auto;display:flex;align-items:center;gap:4px;padding:0 4px}
button.mini{all:unset;box-sizing:border-box;display:flex;justify-content:space-between;gap:10px;padding:9px 0;border-bottom:1px solid var(--line-2);align-items:center;width:100%;cursor:pointer}
.bars{display:flex;align-items:flex-end;gap:10px;height:170px}
.bar{flex:1;display:flex;flex-direction:column;justify-content:flex-end;align-items:center;height:100%;gap:4px;font-size:12.5px;color:var(--muted)}
.bar i{display:block;width:100%;background:var(--brand);border-radius:6px 6px 2px 2px;min-height:3px}
.bar.today i{background:var(--gold)}
.bar em{font-style:normal;font-size:12px;color:var(--text);font-weight:600}

/* billing screen */
.pos{display:flex;flex-direction:column;gap:14px;align-items:stretch}
.pos-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:8px;margin-top:10px}
.pcard{all:unset;box-sizing:border-box;cursor:pointer;background:#fff;border:1px solid var(--line);border-radius:10px;padding:9px;display:flex;flex-direction:column;gap:2px;min-height:76px}
.pcard:hover{border-color:var(--brand)}
.pcard:focus-visible{outline:3px solid #7CC4BB}
.pcard b{font-size:14.5px;line-height:1.3;overflow-wrap:anywhere}
.pcard .pr{font-weight:800;margin-top:auto}
.pcard small{color:var(--muted)}
.pcard.out{opacity:.5}
.pos-bill{width:100%}
.receipt{background:#fff;border-radius:6px 6px 0 0;padding:18px 18px 22px;position:relative;border:1px solid var(--line);border-bottom:0;margin-bottom:12px}
.receipt::after{content:"";position:absolute;left:-1px;right:-1px;bottom:-11px;height:11px;
  background:linear-gradient(135deg,#fff 50%,transparent 50%) 0 0/16px 11px repeat-x,linear-gradient(225deg,#fff 50%,transparent 50%) 0 0/16px 11px repeat-x;
  filter:drop-shadow(0 1px 0 var(--line))}
.rc-head{display:flex;justify-content:space-between;align-items:center;margin-bottom:12px}
.custbar{display:flex;gap:8px;margin-bottom:8px}
.lines{display:flex;flex-direction:column}
.line{padding:12px 0;border-top:1px dashed var(--line);display:flex;flex-direction:column;gap:8px}
.l-top{display:flex;justify-content:space-between;align-items:flex-start;gap:8px}
.l-mid{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.stepper{display:flex;align-items:center;border:1px solid var(--line);border-radius:9px;overflow:hidden}
.stepper button{all:unset;box-sizing:border-box;width:34px;height:38px;text-align:center;cursor:pointer;font-weight:800;font-size:18px;background:var(--line-2)}
.stepper button:hover{background:var(--line)}
.stepper input{border:0;border-radius:0;width:58px;text-align:center;min-height:38px;padding:4px}
.l-mid .price{width:84px}
.l-total{margin-left:auto;font-weight:800}
.l-sub{font-size:13px}
.totals{margin:6px 0 0;padding-top:10px;border-top:1px dashed var(--line);display:flex;flex-direction:column;gap:5px}
.totals div{display:flex;justify-content:space-between}
.totals dt{color:var(--muted)}.totals dd{margin:0}
.totals .grand{font-size:22px;font-weight:800;padding-top:8px;border-top:2px solid var(--ink);margin-top:6px}
.totals .grand dt{color:var(--text)}
.pay{display:flex;flex-direction:column;gap:10px;margin:14px 0}
.settings-layout{display:grid;grid-template-columns:220px minmax(0,1fr);gap:18px;align-items:start}
.settings-menu{display:flex;flex-direction:column;gap:5px;padding:8px;background:#fff;border:1px solid var(--line);border-radius:12px;position:sticky;top:16px}
.settings-menu button{all:unset;box-sizing:border-box;display:flex;align-items:center;gap:10px;min-height:44px;padding:9px 12px;border-radius:8px;cursor:pointer;font-weight:650;color:var(--muted)}
.settings-menu button:hover{background:var(--line-2);color:var(--text)}
.settings-menu button.active{background:var(--ink);color:#fff}
.settings-menu button:focus-visible{outline:3px solid #7CC4BB}
.settings-content{min-width:0}
.settings-content>.settings-pane>.card{max-width:900px}
.settings-pane[hidden]{display:none}
#mobile-access-qr{max-width:100%;border:1px solid var(--line);background:#fff;padding:8px}

/* dialog */
dialog{border:0;border-radius:14px;padding:0;width:min(520px,94vw);max-height:92vh;box-shadow:0 24px 70px rgba(10,30,36,.4);color:var(--text);background:#fff}
dialog.wide{width:min(760px,96vw)}
dialog[open]{display:flex;flex-direction:column}
dialog::backdrop{background:rgba(10,30,36,.55)}
.dlg-head{display:flex;justify-content:space-between;align-items:center;padding:16px 18px 10px;gap:10px}
.dlg-head h2{margin:0;font-size:18px;overflow-wrap:anywhere}
.dlg-body{padding:4px 18px 18px;overflow:auto}
.dlg-actions{display:flex;gap:8px;flex-wrap:wrap;margin-top:16px;padding-top:14px;border-top:1px solid var(--line-2)}
.dlg-actions .push{margin-left:auto}

/* invoice */
.inv{font-size:14.5px}
.inv-top{display:flex;justify-content:space-between;gap:16px;flex-wrap:wrap;padding-bottom:14px;border-bottom:2px solid var(--ink)}
.inv-top h3{font-size:20px;letter-spacing:-.01em}
.inv-top p{color:var(--muted);font-size:13.5px}
.inv-meta{text-align:right}
.inv-meta b{font-size:17px}
.inv-to{padding:12px 0;display:flex;justify-content:space-between;gap:12px;flex-wrap:wrap}
.inv-to p{font-size:13.5px;color:var(--muted)}
.tbl-wrap{overflow-x:auto}
.inv table{width:100%;border-collapse:collapse}
.inv th{font-size:13px;text-align:right;color:var(--muted);font-weight:700;padding:8px 6px;border-bottom:1px solid var(--line)}
.inv td{padding:9px 6px;border-bottom:1px solid var(--line-2);text-align:right;vertical-align:top}
.inv th:first-child,.inv td:first-child{text-align:left}
.inv td small{display:block;color:var(--muted)}
.inv-sum{margin-left:auto;width:min(300px,100%);padding-top:10px}
.inv-sum div{display:flex;justify-content:space-between;padding:3px 0}
.inv-sum .g{font-size:18px;font-weight:800;border-top:2px solid var(--ink);margin-top:6px;padding-top:8px}
.inv-pay{margin-top:12px;font-size:13.5px;color:var(--muted)}
.inv-foot{margin-top:16px;text-align:center;color:var(--muted);font-size:13.5px}
.void-mark{color:var(--danger);font-weight:800;border:2px solid var(--danger);border-radius:6px;padding:0 8px;display:inline-block;margin-top:4px}

.fy-bar{display:flex;align-items:center;justify-content:flex-end;gap:8px;margin-bottom:16px;color:var(--muted);font-weight:700}
.fy-bar select{width:auto;min-width:150px;padding:7px 10px;min-height:38px}
.custbar{align-items:flex-end}
.custbar .f{flex:1}
.keyboard-help{padding:9px 12px;background:var(--card);border:1px solid var(--line);border-radius:9px}
.pay .chip{align-self:flex-start}
.login-screen{position:fixed;inset:0;z-index:200;background:var(--paper);display:grid;place-items:center;padding:20px}
.login-card{width:min(420px,100%);background:var(--card);padding:30px;border:1px solid var(--line);border-radius:16px;box-shadow:0 16px 50px rgba(10,30,36,.14)}
.login-card h1{margin-bottom:8px}
.login-card .btn{width:100%}
.login-error{min-height:1.5em;color:var(--danger);font-weight:600}
#login-screen[hidden],#app[hidden]{display:none}
.toast-host{position:fixed;left:0;right:0;bottom:calc(84px + env(safe-area-inset-bottom));display:flex;flex-direction:column;align-items:center;gap:8px;pointer-events:none;z-index:99}
.toast{background:var(--ink);color:#fff;padding:11px 16px;border-radius:10px;box-shadow:0 8px 24px rgba(0,0,0,.25);max-width:min(92vw,460px);font-weight:600}
.toast.err{background:var(--danger)}.toast.ok{background:var(--brand-d)}
#print-area{display:none}

@media (max-width:1000px){
  .tiles{grid-template-columns:1fr 1fr}
  .grid2{grid-template-columns:1fr}
}
@media (max-width:860px){
  #app{grid-template-columns:1fr}
  #nav{position:fixed;top:auto;bottom:0;left:0;right:0;height:auto;flex-direction:row;padding:6px 4px calc(6px + env(safe-area-inset-bottom));gap:0;z-index:30;box-shadow:0 -4px 20px rgba(10,30,36,.25);overflow:visible}
  .brand{display:none}
  #nav>button{flex:1;flex-direction:column;gap:2px;padding:6px 2px;font-size:11px;justify-content:center;text-align:center;min-width:0}
  #nav>button span{max-width:100%;overflow:hidden;text-overflow:ellipsis}
  #nav>button .shortcut-hint{padding:0 3px;font-size:9px}
  #nav>button .dot{position:absolute;top:0;right:8px;margin:0;min-width:18px;line-height:18px;font-size:11px}
  main{padding:18px 14px calc(96px + env(safe-area-inset-bottom))}
  h1{font-size:23px}
  .prod{grid-template-columns:minmax(0,1fr) auto;grid-template-areas:"m s" "p a"}
  .prod .r-main{grid-area:m}.prod .r-price{grid-area:p}.prod .r-stock{grid-area:s;justify-self:end}.prod .r-act{grid-area:a}
  .cust{grid-template-columns:minmax(0,1fr) auto}
  .cust .r-act{grid-column:1/-1;justify-content:flex-start}
  .credit-row{grid-template-columns:minmax(0,1fr) auto;grid-template-areas:"customer total" "detail detail" "actions actions"}
  .credit-row .credit-customer{grid-area:customer}.credit-row .credit-detail{grid-area:detail}
  .credit-row .credit-total{grid-area:total}.credit-row .r-act{grid-area:actions}
  .invr{grid-template-columns:minmax(0,1fr) auto;grid-template-areas:"n t" "c s" "d d"}
  .invr .a{grid-area:n}.invr .b{grid-area:c}.invr .c{grid-area:d}.invr .d{grid-area:t;text-align:right}.invr .e{grid-area:s;justify-self:end}
    .expense-row{grid-template-columns:minmax(0,1fr) auto;grid-template-areas:"main date" "method amount" "note note"}
    .expense-row .r-main{grid-area:main}.expense-row .expense-date{grid-area:date}.expense-row .expense-method{grid-area:method}.expense-row .expense-amount{grid-area:amount}.expense-row .expense-note{grid-area:note}
  dialog{margin:auto 0 0;width:100%;max-width:100%;border-radius:16px 16px 0 0;max-height:94vh}
  dialog.wide{width:100%}
  .two{grid-template-columns:1fr 1fr}
  .tile b{font-size:21px}
  main.transaction-main{padding:14px 10px calc(96px + env(safe-area-inset-bottom))}
  .settings-layout{grid-template-columns:1fr;gap:12px}
  .settings-menu{position:static;flex-direction:row;overflow-x:auto;gap:4px;padding:5px;scrollbar-width:thin}
  .settings-menu button{flex:0 0 auto;min-height:40px;padding:8px 11px;white-space:nowrap}
  .settings-content>.settings-pane>.card{max-width:none}
  .pos-grid{grid-template-columns:repeat(auto-fill,minmax(132px,1fr));gap:7px}
  .upi-qr{align-items:flex-start;gap:10px;padding:10px}
  .upi-qr img{width:116px;height:116px;flex-basis:116px}
}
@media (prefers-reduced-motion:no-preference){
  dialog[open]{animation:pop .16s ease-out}
  @keyframes pop{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:none}}
}
@media print{
  body{background:#fff}
  #app,.toast-host,dialog{display:none !important}
  #print-area{display:block}
  @page{margin:12mm}
}
</style>
</head>
<body>
<section id="login-screen" class="login-screen" aria-labelledby="login-title">
  <form id="login-form" class="login-card stack">
    <div class="brand" style="color:var(--ink);padding:0">StockBill<small style="color:var(--muted)">Secure shop access</small></div>
    <div><h1 id="login-title">Sign in</h1><p id="login-message" class="muted">Sign in with your account email and password.</p></div>
    <label class="f"><span>Email</span><input id="login-email" type="email" name="email" autocomplete="username" maxlength="254" required></label>
    <label class="f"><span>Password</span><input id="login-password" type="password" name="password" autocomplete="current-password" minlength="8" maxlength="256" required></label>
    <label id="login-confirm-wrap" class="f" hidden><span>Confirm password</span><input id="login-confirm-password" type="password" name="confirm_password" autocomplete="new-password" minlength="8" maxlength="256"></label>
    <p id="login-error" class="login-error" role="alert"></p>
    <button id="login-submit" class="btn">Sign in</button>
  </form>
</section>
<div id="app" hidden>
  <nav id="nav" aria-label="Main"></nav>
  <main id="main" tabindex="-1"></main>
</div>
<dialog id="dlg" aria-modal="true"></dialog>
<div id="toasts" class="toast-host" role="status" aria-live="polite"></div>
<div id="print-area"></div>

<script>
(() => {
'use strict';
const $ = (s, el = document) => el.querySelector(s);
const $$ = (s, el = document) => [...el.querySelectorAll(s)];
const esc = v => String(v ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const r2 = x => Math.round((x + Number.EPSILON) * 100) / 100;
const num = v => { const n = parseFloat(v); return Number.isFinite(n) ? n : 0; };

const ICONS = {
  home:'<path d="M3 11l9-8 9 8"/><path d="M5 10v10h14V10"/>',
  bill:'<path d="M6 3h12v18l-3-2-3 2-3-2-3 2z"/><path d="M9 8h6M9 12h6"/>',
  box:'<path d="M3 7l9-4 9 4v10l-9 4-9-4z"/><path d="M3 7l9 4 9-4M12 11v10"/>',
  users:'<circle cx="9" cy="8" r="3.5"/><path d="M2.5 20c0-3.6 2.9-6 6.5-6s6.5 2.4 6.5 6"/><path d="M16 4.5a3.5 3.5 0 010 7M18 14.3c2 .7 3.5 2.6 3.5 5.7"/>',
  list:'<path d="M8 6h13M8 12h13M8 18h13"/><circle cx="3.5" cy="6" r="1"/><circle cx="3.5" cy="12" r="1"/><circle cx="3.5" cy="18" r="1"/>',
  gear:'<path d="M4 6h10M18 6h2M4 12h4M12 12h8M4 18h12M20 18h0"/><circle cx="16" cy="6" r="2"/><circle cx="10" cy="12" r="2"/><circle cx="18" cy="18" r="2"/>',
  plus:'<path d="M12 5v14M5 12h14"/>',
  search:'<circle cx="11" cy="11" r="6.5"/><path d="M20 20l-4.2-4.2"/>',
  x:'<path d="M6 6l12 12M18 6L6 18"/>',
  print:'<path d="M6 9V3h12v6M6 18H4v-7h16v7h-2"/><path d="M7 14h10v7H7z"/>'
  ,book:'<path d="M4 5.5A2.5 2.5 0 016.5 3H20v17H6.5A2.5 2.5 0 014 17.5z"/><path d="M4 6h12M8 8v5l2-1 2 1V8M6.5 20A2.5 2.5 0 014 17.5"/>'
};
const ic = n => `<svg class="ic" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${ICONS[n]}</svg>`;

/* ---------- state ---------- */
const S = {
  settings: {}, info: {}, products: [], customers: [], invoices: [], view: 'dashboard',
  cart: [], cartCustomer: '', pay: {mode: 'full', amount: '', method: 'Cash', notes: ''},
  posQuery: '', q: {products: '', customers: '', invoices: '', expenses: ''}, lowOnly: false, archived: false,
  invStatus: 'all', invCustomer: '', current: null, focusPos: false,
  financialYear: '', financialYears: [], settingsSection: 'shop'
};
try {
  S.cart = JSON.parse(localStorage.getItem('sb_cart') || '[]');
  S.cart.forEach(line => { delete line.disc; });
} catch (_) { S.cart = []; }
const saveCart = () => { try { localStorage.setItem('sb_cart', JSON.stringify(S.cart)); } catch (_) {} };

/* ---------- formatting ---------- */
const fmtMoney = n => (S.settings.currency || '\u20b9') + Number(n || 0).toLocaleString('en-IN', {minimumFractionDigits: 2, maximumFractionDigits: 2});
const fmtQty = n => (Math.round(Number(n || 0) * 1000) / 1000).toLocaleString('en-IN', {maximumFractionDigits: 3});
const fmtDate = s => {
  const d = new Date(String(s).replace(' ', 'T'));
  return d.toLocaleDateString('en-IN', {day: '2-digit', month: 'short', year: 'numeric'}) + ', ' +
         d.toLocaleTimeString('en-IN', {hour: '2-digit', minute: '2-digit'});
};
const fmtDay = s => new Date(String(s).replace(' ', 'T')).toLocaleDateString('en-IN', {day: '2-digit', month: 'short'});
const statusBadge = s => ({paid: '<span class="badge ok">Paid</span>', partial: '<span class="badge warn">Part paid</span>',
  unpaid: '<span class="badge bad">Unpaid</span>', void: '<span class="badge">Void</span>'}[s] || '');
const stockBadge = p => {
  const cls = p.stock <= 0 ? 'bad' : (p.stock <= p.low_stock ? 'warn' : 'ok');
  const label = p.stock <= 0 ? 'Out of stock' : `${fmtQty(p.stock)} ${esc(p.unit)}`;
  return `<span class="badge ${cls}">${label}</span>`;
};
const matches = (p, q) => !q || `${p.name} ${p.sku} ${p.category}`.toLowerCase().includes(q.toLowerCase());

/* ---------- api ---------- */
let sessionToken = '', accountConfigured = false, sessionActive = false;
let upiQrUrl = '', upiQrRequest = 0;
let mobileAccessQrUrl = '';
try { localStorage.removeItem('sb_pin'); } catch (_) {}
function showLogin(hasAccount, message = '') {
  sessionToken = '';
  sessionActive = false;
  clearUpiQr();
  clearMobileAccessQr();
  accountConfigured = hasAccount;
  $('#login-password').value = '';
  $('#login-confirm-password').value = '';
  $('#app').hidden = true;
  $('#login-screen').hidden = false;
  $('#login-confirm-wrap').hidden = hasAccount;
  $('#login-confirm-password').required = !hasAccount;
  $('#login-password').autocomplete = hasAccount ? 'current-password' : 'new-password';
  $('#login-title').textContent = hasAccount ? 'Sign in' : 'Create your account';
  $('#login-message').textContent = hasAccount
    ? 'Sign in with your account email and password.'
    : 'Create the email and password you will use to sign in. Passwords need at least 8 characters.';
  $('#login-submit').textContent = hasAccount ? 'Sign in' : 'Create account';
  $('#login-error').textContent = message;
  $('#login-email').focus();
}
async function api(path, opts = {}) {
  const headers = {};
  if (opts.body !== undefined) headers['Content-Type'] = 'application/json';
  if (sessionToken) headers['X-Session-Token'] = sessionToken;
  let res;
  try {
    res = await fetch('/api' + path, {method: opts.method || 'GET', headers, body: opts.body !== undefined ? JSON.stringify(opts.body) : undefined});
  } catch (_) { throw new Error("Can't reach the server. Is StockBill still running?"); }
  if (res.status === 401) {
    showLogin(true, 'Your session expired. Sign in again.');
    throw new Error('Your session expired. Sign in again.');
  }
  const data = await res.json().catch(() => ({}));
  if (!res.ok) throw new Error(data.error || 'Something went wrong');
  return data;
}
function reportClientError(message, stack = '') {
  if (!sessionActive) return;
  const headers = {'Content-Type': 'application/json'};
  if (sessionToken) headers['X-Session-Token'] = sessionToken;
  fetch('/api/client-errors', {
    method: 'POST', headers,
    body: JSON.stringify({message: String(message).slice(0, 500), stack: String(stack).slice(0, 1200)})
  }).then(response => {
    if (!response.ok) console.error('Could not save the browser error in the activity log.');
  }).catch(error => console.error('Could not send the browser error to StockBill.', error));
}
window.addEventListener('error', event => {
  reportClientError(event.message || 'Uncaught browser error', event.error && event.error.stack);
});
window.addEventListener('unhandledrejection', event => {
  const reason = event.reason;
  reportClientError(reason && reason.message ? reason.message : String(reason), reason && reason.stack);
});
async function download(path, name) {
  const headers = {}; if (sessionToken) headers['X-Session-Token'] = sessionToken;
  const r = await fetch('/api' + path, {headers});
  if (r.status === 401) {
    showLogin(true, 'Your session expired. Sign in again.');
    throw new Error('Your session expired. Sign in again.');
  }
  if (!r.ok) throw new Error('Download failed');
  const a = document.createElement('a');
  a.href = URL.createObjectURL(await r.blob()); a.download = name;
  document.body.append(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 1500);
}
function clearUpiQr() {
  upiQrRequest++;
  if (upiQrUrl) URL.revokeObjectURL(upiQrUrl);
  upiQrUrl = '';
}
function clearMobileAccessQr() {
  if (mobileAccessQrUrl) URL.revokeObjectURL(mobileAccessQrUrl);
  mobileAccessQrUrl = '';
}
async function loadMobileAccessQr() {
  const image = $('#mobile-access-qr'), message = $('#mobile-access-qr-error');
  if (!image || !message) return;
  message.textContent = 'Generating mobile access QR...';
  image.hidden = true;
  try {
    const headers = {};
    if (sessionToken) headers['X-Session-Token'] = sessionToken;
    const response = await fetch('/api/mobile-access-qr', {headers});
    if (response.status === 401) {
      showLogin(true, 'Your session expired. Sign in again.');
      return;
    }
    if (!response.ok) {
      const result = await response.json().catch(() => ({}));
      throw new Error(result.error || 'Could not generate the mobile access QR.');
    }
    const objectUrl = URL.createObjectURL(await response.blob());
    clearMobileAccessQr();
    mobileAccessQrUrl = objectUrl;
    image.src = objectUrl;
    image.hidden = false;
    message.textContent = '';
  } catch (error) {
    message.textContent = `Could not generate the mobile access QR: ${error.message}`;
  }
}
async function refreshUpiQr(amount) {
  const image = $('#upi-qr-image'), message = $('#upi-qr-message');
  const request = ++upiQrRequest;
  if (upiQrUrl) URL.revokeObjectURL(upiQrUrl);
  upiQrUrl = '';
  if (!image || !message) return;
  image.hidden = true;
  image.removeAttribute('src');
  const amountLabel = $('.upi-qr-copy b');
  if (amountLabel) {
    amountLabel.textContent = amount > 0
      ? `Scan to pay ${fmtMoney(amount)}`
      : 'Enter the part-payment amount';
  }
  image.alt = `UPI payment QR for ${fmtMoney(amount)}`;
  if (!S.settings.upi_id) {
    message.textContent = 'Add your UPI ID in Settings to generate a payment QR.';
    return;
  }
  if (!(amount > 0)) {
    message.textContent = 'Enter a part-payment amount to generate its QR.';
    return;
  }
  message.textContent = 'Generating payment QR...';
  try {
    const headers = {};
    if (sessionToken) headers['X-Session-Token'] = sessionToken;
    const response = await fetch(`/api/upi-qr?amount=${encodeURIComponent(amount.toFixed(2))}`, {headers});
    if (response.status === 401) {
      showLogin(true, 'Your session expired. Sign in again.');
      return;
    }
    if (!response.ok) {
      const result = await response.json().catch(() => ({}));
      throw new Error(result.error || 'Could not generate the payment QR.');
    }
    const objectUrl = URL.createObjectURL(await response.blob());
    if (request !== upiQrRequest) {
      URL.revokeObjectURL(objectUrl);
      return;
    }
    upiQrUrl = objectUrl;
    image.src = objectUrl;
    image.hidden = false;
    message.textContent = '';
  } catch (error) {
    if (request !== upiQrRequest) return;
    message.textContent = `Could not generate the payment QR: ${error.message}`;
    reportClientError(error.message, error.stack);
  }
}

/* ---------- ui helpers ---------- */
function toast(msg, kind = '') {
  const t = document.createElement('div'); t.className = 'toast ' + kind; t.textContent = msg;
  const d = $('#dlg'); (d.open ? d : $('#toasts')).append(t);
  if (d.open) { t.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);bottom:24px;z-index:100'; }
  setTimeout(() => t.remove(), 3400);
}
function openModal(title, body, opts = {}) {
  const d = $('#dlg'); d.dataset.locked = opts.locked ? '1' : ''; d.classList.toggle('wide', !!opts.wide);
  d.innerHTML = `<div class="dlg-head"><h2>${esc(title)}</h2>${opts.locked ? '' : `<button class="icon-btn" data-act="close" aria-label="Close">${ic('x')}</button>`}</div><div class="dlg-body">${body}</div>`;
  if (!d.open) d.showModal();
  return d;
}
const closeModal = () => { const d = $('#dlg'); if (d.open) d.close(); };
$('#dlg').addEventListener('cancel', e => { if ($('#dlg').dataset.locked) e.preventDefault(); });
$('#dlg').addEventListener('click', e => { const d = $('#dlg'); if (e.target === d && !d.dataset.locked) d.close(); });
const field = (label, name, val = '', attrs = '') => `<label class="f"><span>${label}</span><input name="${name}" value="${esc(val)}" ${attrs}></label>`;

/* ---------- event wiring ---------- */
const actions = {}, forms = {}, inputs = {}, changes = {};
const guard = p => Promise.resolve(p).catch(err => toast(err.message || String(err), 'err'));
$('#login-form').addEventListener('submit', async e => {
  e.preventDefault();
  const button = $('#login-submit');
  button.disabled = true;
  $('#login-error').textContent = '';
  const email = $('#login-email').value.trim();
  const password = $('#login-password').value;
  const confirmPassword = $('#login-confirm-password').value;
  try {
    const response = await fetch('/api/login', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({
        email, password,
        ...(accountConfigured ? {} : {confirm_password: confirmPassword})
      })
    });
    const result = await response.json().catch(() => ({}));
    if (!response.ok) {
      $('#login-error').textContent = result.error || 'Sign in failed.';
      return;
    }
    sessionToken = result.session_token;
    accountConfigured = true;
    sessionActive = true;
    $('#login-screen').hidden = true;
    $('#app').hidden = false;
    await startApp();
  } catch (err) {
    $('#login-error').textContent = err.message || 'Could not sign in.';
  } finally {
    button.disabled = false;
  }
});
document.addEventListener('click', e => {
  const el = e.target.closest('[data-act]'); if (!el || !actions[el.dataset.act]) return;
  e.preventDefault(); guard(actions[el.dataset.act](el, e));
});
document.addEventListener('submit', e => {
  const f = e.target.closest('form[data-form]'); if (!f) return;
  e.preventDefault(); if (forms[f.dataset.form]) guard(forms[f.dataset.form](f));
});
document.addEventListener('input', e => { const k = e.target.dataset && e.target.dataset.in; if (k && inputs[k]) inputs[k](e.target, e); });
document.addEventListener('change', e => { const k = e.target.dataset && e.target.dataset.ch; if (k && changes[k]) changes[k](e.target, e); });
const debounce = (fn, ms = 250) => { let t; return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); }; };

/* ---------- data ---------- */
const refreshProducts = async () => { S.products = await api('/products'); };
const refreshCustomers = async () => { S.customers = await api('/customers'); };
async function loadAll() {
  [S.settings, S.info, S.products, S.customers, S.financialYears] = await Promise.all([
    api('/settings'), api('/info'), api('/products'), api('/customers'), api('/financial-years')
  ]);
  let savedYear = '';
  try { savedYear = localStorage.getItem('sb_financial_year') || ''; } catch (_) {}
  const validYears = S.financialYears.years.map(year => year.start);
  S.financialYear = savedYear === 'all' || validYears.includes(savedYear)
    ? savedYear : S.financialYears.current;
  document.title = S.settings.business_name + ' | StockBill';
  // Keep pending cart prices and stock aligned with the item catalog.
  S.cart = S.cart.filter(l => S.products.some(p => p.id === l.product_id && p.active))
    .map(line => {
      const product = S.products.find(item => item.id === line.product_id);
      return {...line, name: product.name, sku: product.sku, unit: product.unit,
        price: product.price, tax_rate: product.tax_rate, stock: product.stock};
    });
  saveCart();
}

/* ---------- navigation ---------- */
const VIEWS = {
  dashboard: {label: 'Home', icon: 'home'},
  products: {label: 'Items', icon: 'box'}, customers: {label: 'Customers', icon: 'users'},
  invoices: {label: 'Invoices', icon: 'list'}, accounts: {label: 'Accounts', icon: 'book'}, settings: {label: 'Settings', icon: 'gear'}
};
const NAV_SHORTCUTS = Object.fromEntries(Object.keys(VIEWS).map((id, i) => [id, String(i + 1)]));
const financialYearLabel = start => `FY ${start}-${String(Number(start) + 1).slice(-2)}`;
const financialYearQuery = () => `?financial_year=${encodeURIComponent(S.financialYear || 'all')}`;
function financialYearControl() {
  const years = S.financialYears.years || [];
  return `<div class="fy-bar"><label for="financial-year">Financial year</label><select id="financial-year" data-ch="financial-year">
    <option value="all" ${S.financialYear === 'all' ? 'selected' : ''}>All years</option>
    ${years.map(year => `<option value="${year.start}" ${S.financialYear === year.start ? 'selected' : ''}>${esc(year.label)}</option>`).join('')}
  </select></div>`;
}
changes['financial-year'] = el => {
  S.financialYear = el.value;
  try { localStorage.setItem('sb_financial_year', S.financialYear); } catch (_) {}
  render();
};
const ACTION_SHORTCUTS = {
  'new-bill': {label: 'N', key: 'n', global: true},
  'new-product': {label: 'I', key: 'i', global: true},
  'new-customer': {label: 'C', key: 'c', global: true},
  'new-expense': {label: 'E', key: 'e', global: true},
  logout: {label: 'O', key: 'o', global: true},
  'save-bill': {label: 'F2', key: 'f2', allowTyping: true},
  'clear-cart': {label: 'F3', key: 'f3', allowTyping: true, billing: true},
  'pay-cash': {label: 'F5', key: 'f5', allowTyping: true, billing: true, method: 'Cash'},
  'pay-upi': {label: 'F6', key: 'f6', allowTyping: true, billing: true, method: 'UPI'},
  'pay-credit': {label: 'F7', key: 'f7', allowTyping: true, billing: true, method: 'credit'},
  'save-settings': {label: 'F4', key: 'f4', allowTyping: true},
  'print-inv': {label: 'P', key: 'p', dialog: true},
  'pay-inv': {label: 'R', key: 'r', dialog: true},
  'void-inv': {label: 'V', key: 'v', dialog: true},
  'dl-csv': {label: 'X', key: 'x'},
  'dl-expenses': {label: 'X', key: 'x'},
  'dl-backup': {label: 'B', key: 'b'},
  'toggle-low': {label: 'L', key: 'l'},
  'toggle-archived': {label: 'A', key: 'a'}
};
function shortcutFor(el) {
  if (el.dataset.act === 'close') return {label: 'Esc'};
  if (el.dataset.act === 'go') {
    const key = NAV_SHORTCUTS[el.dataset.to];
    return key ? {label: key} : null;
  }
  if (el.closest('form[data-form="settings"]')) return ACTION_SHORTCUTS['save-settings'];
  if (el.dataset.act === 'new-cust') return ACTION_SHORTCUTS['new-customer'];
  if (el.dataset.act === 'transaction-method') {
    return ACTION_SHORTCUTS['pay-' + el.dataset.method.toLowerCase()];
  }
  if (el.dataset.act) return ACTION_SHORTCUTS[el.dataset.act];
  if (['posq', 'pq', 'cq', 'iq', 'eq'].includes(el.dataset.in)) return {label: '/'};
  return null;
}
function addShortcutHints(root = document) {
  const elements = [];
  if (root.nodeType === 1 && root.matches('[data-act], form[data-form="settings"] button, input[data-in]')) elements.push(root);
  elements.push(...$$('[data-act], form[data-form="settings"] button, input[data-in]', root));
  elements.forEach(el => {
    const shortcut = shortcutFor(el);
    if (!shortcut) return;
    const target = el.matches('input[data-in]') ? el.closest('.search') : el;
    if (!target || target.querySelector('.shortcut-hint')) return;
    const hint = document.createElement('kbd');
    hint.className = 'shortcut-hint';
    hint.textContent = shortcut.label;
    target.append(hint);
    el.setAttribute('aria-keyshortcuts', shortcut.label.replace('Esc', 'Escape'));
    el.title = el.title ? `${el.title} (${shortcut.label})` : `Shortcut: ${shortcut.label}`;
  });
}
const shortcutObserver = new MutationObserver(records => {
  records.forEach(record => record.addedNodes.forEach(node => {
    if (node.nodeType === 1) addShortcutHints(node);
  }));
});
shortcutObserver.observe(document.body, {childList: true, subtree: true});
function renderNav() {
  $('#nav').innerHTML = `<div class="brand">${esc(S.settings.business_name || 'StockBill')}<small>StockBill</small></div>` +
    Object.entries(VIEWS).map(([id, v]) =>
      `<button data-act="go" data-to="${id}" ${id === S.view || (S.view === 'billing' && id === 'dashboard') ? 'class="active" aria-current="page"' : ''}>${ic(v.icon)}<span>${v.label}</span></button>`).join('') +
    `<button data-act="logout"><span>Log out</span></button>`;
}
actions.go = el => { closeModal(); location.hash = '#/' + el.dataset.to; };
actions.close = () => closeModal();
actions.logout = () => {
  return api('/logout', {method: 'POST', body: {}}).catch(err => {
    toast(`Could not record sign out: ${err.message}`, 'err');
  }).finally(() => {
  closeModal();
  showLogin(true);
  });
};
actions['new-bill'] = () => {
  closeModal();
  if (S.view === 'billing') {
    $('#pos-q').focus();
    return;
  }
  S.focusPos = true; location.hash = '#/billing';
};
let renderToken = 0;
async function render() {
  const id = (location.hash.match(/^#\/(\w+)/) || [])[1];
  S.view = (VIEWS[id] || id === 'billing') ? id : 'dashboard';
  renderNav();
  $('#main').classList.toggle('transaction-main', S.view === 'billing');
  const token = ++renderToken;
  const fn = {dashboard: vDashboard, billing: vBilling, products: vProducts, customers: vCustomers, invoices: vInvoices, accounts: vAccounts, settings: vSettings}[S.view];
  try {
    const html = await fn();
    if (token !== renderToken) return;
    $('#main').innerHTML = financialYearControl() + html;
    if (S.view === 'settings' && S.settingsSection === 'mobile') loadMobileAccessQr();
    if (S.view === 'billing') { renderPosList(); renderBill(); }
    if (S.view === 'invoices') refreshInvoiceList();
    if (S.focusPos && S.view === 'billing') { S.focusPos = false; $('#pos-q').focus(); }
  } catch (err) { toast(err.message, 'err'); }
}
window.addEventListener('hashchange', () => {
  if (!location.hash.startsWith('#/billing')) clearUpiQr();
  window.scrollTo(0, 0); render();
});

/* ================= DASHBOARD ================= */
async function vDashboard() {
  const d = await api('/dashboard' + financialYearQuery());
  const compact = new Intl.NumberFormat('en-IN', {notation: 'compact', maximumFractionDigits: 1});
  const max = Math.max(1, ...d.week.map(w => w.total));
  const cur = S.settings.currency || '\u20b9';
  const first = S.products.length === 0 ? `<div class="card" style="margin-bottom:16px"><h2>Set up your shop</h2>
      <p class="muted">Add your items with prices and stock, then start billing. In Settings you can add your shop name, address and GSTIN so they print on every invoice.</p>
      <p style="margin-top:12px"><button class="btn" data-act="go" data-to="products">Add your first item</button></p></div>` : '';
  const yearLabel = S.financialYear === 'all' ? 'All years' : financialYearLabel(S.financialYear);
  return `<header class="page-head"><div><h1>${yearLabel}</h1><p class="muted">Sales, invoices, and top items for the selected period</p></div>
      <button class="btn gold" data-act="new-bill">${ic('plus')} New transaction</button></header>${first}
    <section class="tiles">
      <div class="tile"><span class="muted">Sales in ${yearLabel}</span><b class="num">${fmtMoney(d.year_sales)}</b></div>
      <div class="tile"><span class="muted">Invoices in ${yearLabel}</span><b class="num">${d.year_count}</b></div>
      <div class="tile"><span class="muted">To collect in ${yearLabel}</span><b class="num">${fmtMoney(d.outstanding)}</b></div>
      <div class="tile"><span class="muted">Stock at cost</span><b class="num">${fmtMoney(d.stock_cost)}</b><span class="muted">${d.item_count} items, sells for ${cur}${compact.format(d.stock_retail)}</span></div>
    </section>
    <section class="grid2">
      <div class="card"><h2>Last 7 days</h2><div class="bars num">${d.week.map((w, i) =>
        `<div class="bar ${i === 6 ? 'today' : ''}" title="${esc(w.date)}: ${esc(fmtMoney(w.total))}"><em>${w.total ? compact.format(w.total) : ''}</em><i style="height:${Math.max(2, w.total / max * 100 * 0.78)}%"></i>${w.label}</div>`).join('')}</div></div>
      <div class="card"><h2>Running low</h2>${d.low_stock.length ? d.low_stock.map(p =>
        `<button class="mini" data-act="stock" data-id="${p.id}"><span>${esc(p.name)}</span><span class="badge ${p.stock <= 0 ? 'bad' : 'warn'}">${p.stock <= 0 ? 'Out of stock' : fmtQty(p.stock) + ' ' + esc(p.unit) + ' left'}</span></button>`).join('')
        : '<p class="muted">Nothing is running low.</p>'}</div>
      <div class="card"><h2>Recent bills</h2>${d.recent.length ? d.recent.map(i =>
        `<button class="mini" data-act="open-inv" data-id="${i.id}"><span><b>${esc(i.number)}</b> <span class="muted">${esc(i.customer.name)}</span></span><span class="num">${fmtMoney(i.grand_total)} ${statusBadge(i.status)}</span></button>`).join('')
        : '<p class="muted">No bills yet. Your first bill will show up here.</p>'}</div>
      <div class="card"><h2>Best sellers in ${yearLabel}</h2>${d.top.length ? d.top.map(t =>
        `<div class="mini"><span>${esc(t.name)} <span class="muted">${fmtQty(t.qty)} ${esc(t.unit)}</span></span><b class="num">${fmtMoney(t.revenue)}</b></div>`).join('')
        : '<p class="muted">Sales will be ranked here once you start billing.</p>'}</div>
    </section>`;
}

/* ================= BILLING ================= */
async function vBilling() {
  return `<header class="page-head"><h1>New transaction</h1></header>
    <p class="muted keyboard-help">Shortcuts: F2 confirm bill · F3 clear all · F5 cash · F6 UPI · F7 credit. Search items and press Enter to add an exact SKU match.</p>
    <div class="pos">
      <section id="bill" class="pos-bill"></section>
      <section class="pos-items">
        <div class="search">${ic('search')}<input id="pos-q" data-in="posq" placeholder="Search by name or SKU, press Enter to add" autocomplete="off" value="${esc(S.posQuery)}" aria-label="Search items"></div>
        <div id="pos-list" class="pos-grid"></div>
      </section>
    </div>`;
}
function renderPosList() {
  const el = $('#pos-list'); if (!el) return;
  const list = S.products.filter(p => p.active && matches(p, S.posQuery));
  el.innerHTML = list.length ? list.map(p => {
    const out = !S.settings.allow_negative_stock && p.stock <= 0;
    return `<button class="pcard ${out ? 'out' : ''}" data-act="add" data-id="${p.id}"><b>${esc(p.name)}</b><small>${esc(p.category || p.sku)}</small>
      <span class="pr num">${fmtMoney(p.price)}</span><small>${out ? 'Out of stock' : fmtQty(p.stock) + ' ' + esc(p.unit) + ' in stock'}</small></button>`;
  }).join('') : `<div class="empty" style="grid-column:1/-1">${S.products.length ? 'No items match your search.' : 'No items yet. Add items first, then come back to bill them.'}
      ${S.products.length ? '' : `<br><button class="btn" data-act="go" data-to="products">Add items</button>`}</div>`;
}
inputs.posq = el => { S.posQuery = el.value; renderPosList(); };
document.addEventListener('keydown', e => {
  const typing = e.target.matches('input, textarea, select, [contenteditable="true"]');
  const modified = e.ctrlKey || e.metaKey || e.altKey || e.shiftKey;
  if (e.key === 'Escape' && $('#dlg').open && !$('#dlg').dataset.locked) {
    e.preventDefault(); closeModal(); return;
  }
  if (!typing && !modified && !$('#dlg').open && /^[1-6]$/.test(e.key)) {
    e.preventDefault(); location.hash = '#/' + Object.keys(VIEWS)[Number(e.key) - 1]; return;
  }
  if (!typing && !modified && !$('#dlg').open && e.key === '/') {
    const selectors = {products: '[data-in="pq"]', customers: '[data-in="cq"]', invoices: '[data-in="iq"]', accounts: '[data-in="eq"]'};
    const search = S.view === 'billing' ? $('#pos-q') : selectors[S.view] ? $(selectors[S.view]) : null;
    if (search) { e.preventDefault(); search.focus(); search.select(); }
    return;
  }
  for (const [action, shortcut] of Object.entries(ACTION_SHORTCUTS)) {
    const keyMatches = e.key.toLowerCase() === shortcut.key;
    if (e.repeat || !keyMatches || modified || (typing && !shortcut.allowTyping)) continue;
    if (shortcut.dialog && !$('#dlg').open) continue;
    if (shortcut.billing && (S.view !== 'billing' || $('#dlg').open)) continue;
    if (shortcut.global && $('#dlg').open) continue;
    const targetAction = action === 'new-customer' && S.view === 'billing' ? 'new-cust' : action;
    const candidates = action === 'save-settings'
      ? $$('form[data-form="settings"] button:not([type="button"])')
      : shortcut.method
        ? $$(`[data-act="transaction-method"][data-method="${shortcut.method}"]`)
      : $$(`[data-act="${targetAction}"]`);
    const button = candidates.find(el => !el.disabled && !el.hidden && el.getClientRects().length);
    if (!button && !shortcut.global) continue;
    e.preventDefault();
    if (button) button.click();
    else guard(actions[action]());
    return;
  }
  if (e.key !== 'Enter' || e.target.id !== 'pos-q') return;
  const q = e.target.value.trim().toLowerCase(); if (!q) return;
  const act = S.products.filter(p => p.active);
  const exact = act.find(p => p.sku.toLowerCase() === q);
  const list = exact ? [exact] : act.filter(p => matches(p, q));
  if (list.length === 1) { addToCart(list[0].id); e.target.value = ''; S.posQuery = ''; renderPosList(); }
  else toast(list.length ? 'Several items match. Tap the one you want.' : 'No item found for that search.', 'err');
});
function addToCart(pid) {
  const p = S.products.find(x => x.id === pid); if (!p || !p.active) return;
  const line = S.cart.find(l => l.product_id === pid);
  const inCart = line ? line.qty : 0;
  let add = 1;
  if (!S.settings.allow_negative_stock) {
    const left = p.stock - inCart;
    if (left <= 0) return toast(`${p.name} is out of stock`, 'err');
    add = Math.min(1, left);
  }
  if (line) line.qty = Math.round((line.qty + add) * 1000) / 1000;
  else S.cart.push({product_id: p.id, name: p.name, sku: p.sku, unit: p.unit, qty: add, price: p.price, tax_rate: p.tax_rate, stock: p.stock});
  saveCart(); renderBill(); renderNav();
  if (window.matchMedia('(max-width:1000px)').matches) toast(`Added ${p.name}`, 'ok');
}
actions.add = el => addToCart(+el.dataset.id);
actions.inc = el => { const l = S.cart[+el.dataset.i]; if (!l) return; l.qty = Math.round((l.qty + 1) * 1000) / 1000; clampQty(l); saveCart(); renderBill(); };
actions.dec = el => { const l = S.cart[+el.dataset.i]; if (!l) return; l.qty = Math.max(0, Math.round((l.qty - 1) * 1000) / 1000); if (l.qty <= 0) S.cart.splice(+el.dataset.i, 1); saveCart(); renderBill(); renderNav(); };
actions['rm-line'] = el => { S.cart.splice(+el.dataset.i, 1); saveCart(); renderBill(); renderNav(); };
actions['clear-cart'] = () => { if (!confirm('Remove all items from this bill?')) return; S.cart = []; saveCart(); renderBill(); renderNav(); };
function clampQty(l) {
  if (!S.settings.allow_negative_stock && l.qty > l.stock) { l.qty = l.stock; toast(`Only ${fmtQty(l.stock)} ${l.unit} of ${l.name} in stock`, 'err'); }
}
function calcCart() {
  let gross = 0, taxable = 0, tax = 0;
  const lines = S.cart.map(l => {
    const g = r2(l.qty * l.price), t = r2(g * l.tax_rate / 100);
    gross += g; taxable += g; tax += t; return r2(g + t);
  });
  const raw = r2(taxable + tax);
  const grand = S.settings.round_off ? Math.round(raw) : raw;
  return {lines, gross: r2(gross), tax: r2(tax), round: r2(grand - raw), grand};
}
function renderBill() {
  const el = $('#bill'); if (!el) return;
  const c = calcCart(), cur = S.pay;
  const custOpts = '<option value="">Walk-in customer (no saved customer)</option>' + S.customers.map(x =>
    `<option value="${x.id}" ${String(x.id) === String(S.cartCustomer) ? 'selected' : ''}>${esc(x.name)}${x.phone ? ' (' + esc(x.phone) + ')' : ''}</option>`).join('');
  const lines = S.cart.map((l, i) => `<div class="line">
      <div class="l-top"><b>${esc(l.name)}</b><button class="icon-btn" data-act="rm-line" data-i="${i}" aria-label="Remove ${esc(l.name)}">${ic('x')}</button></div>
      <div class="l-mid">
        <div class="stepper"><button data-act="dec" data-i="${i}" aria-label="Less">&minus;</button>
          <input class="num" inputmode="decimal" data-in="qty" data-i="${i}" value="${l.qty}" aria-label="Quantity"><button data-act="inc" data-i="${i}" aria-label="More">+</button></div>
        <span class="muted">at</span>
        <b class="price num" aria-label="Price per ${esc(l.unit)}">${fmtMoney(l.price)}</b>
        <b class="l-total num" id="lt-${i}">${fmtMoney(c.lines[i])}</b></div>
      <div class="l-sub muted">per ${esc(l.unit)}, tax ${l.tax_rate}% added</div></div>`).join('');
  el.innerHTML = `<div class="receipt">
    <div class="rc-head"><h2>Current bill</h2>${S.cart.length ? '<button class="link" data-act="clear-cart">Clear all</button>' : ''}</div>
    <div class="custbar"><label class="f"><span>Customer (optional for walk-in sales)</span>
      <select data-ch="cust" aria-label="Customer">${custOpts}</select></label>
      <button class="btn ghost sm" data-act="new-cust">${ic('plus')} New</button></div>
    <div class="lines">${S.cart.length ? lines : '<p class="empty">Tap an item to add it to the bill.</p>'}</div>
    ${S.cart.length ? `<dl class="totals num">
      <div><dt>Subtotal</dt><dd id="t-gross">${fmtMoney(c.gross)}</dd></div>
      <div><dt>Tax</dt><dd id="t-tax">${fmtMoney(c.tax)}</dd></div>
      ${S.settings.round_off ? `<div><dt>Round off</dt><dd id="t-round">${fmtMoney(c.round)}</dd></div>` : ''}
      <div class="grand"><dt>Total</dt><dd id="t-grand">${fmtMoney(c.grand)}</dd></div></dl>
    <div class="pay">
      <div class="chips" role="group" aria-label="Payment method">
        ${[['Cash', 'Cash'], ['UPI', 'UPI'], ['credit', 'Credit']].map(([m, t]) =>
          `<button class="chip ${(m === 'credit' ? cur.mode === 'credit' : cur.mode !== 'credit' && cur.method === m) ? 'on' : ''}" data-act="transaction-method" data-method="${m}">${t}</button>`).join('')}</div>
      ${cur.method === 'UPI' && cur.mode !== 'credit' ? `<div class="upi-qr" aria-live="polite">
        <img id="upi-qr-image" alt="UPI payment QR for ${esc(fmtMoney(cur.mode === 'part' ? num(cur.amount) : c.grand))}" hidden>
        <div class="upi-qr-copy"><b>Scan to pay ${fmtMoney(cur.mode === 'part' ? num(cur.amount) : c.grand)}</b>
          <p class="muted">${esc(S.settings.upi_id || 'UPI ID not set')}</p><p class="muted" id="upi-qr-message"></p></div>
      </div>` : ''}
      ${cur.mode !== 'credit' ? `<button class="chip ${cur.mode === 'part' ? 'on' : ''}" data-act="part-payment">${cur.mode === 'part' ? 'Part payment on' : 'Record part payment'}</button>` : '<p class="muted">Credit bills require a saved customer and will be added to their pending bills.</p>'}
      ${cur.mode === 'part' ? `<label class="f"><span>Amount received by ${esc(cur.method)}</span><input inputmode="decimal" data-in="paid" value="${esc(cur.amount)}" placeholder="0.00" required></label>` : ''}
      <label class="f"><span>Note</span><input data-in="notes" maxlength="200" placeholder="Optional" value="${esc(cur.notes)}"></label>
    </div>
    <button class="btn gold lg block" id="save-btn" data-act="save-bill">Confirm bill for ${fmtMoney(c.grand)}</button>` : ''}
  </div>`;
  if (S.cart.length && cur.method === 'UPI' && cur.mode !== 'credit') {
    refreshUpiQr(cur.mode === 'part' ? num(cur.amount) : c.grand);
  } else {
    clearUpiQr();
  }
}
function refreshTotals() {
  const c = calcCart(), set = (id, v) => { const e = $('#' + id); if (e) e.textContent = v; };
  c.lines.forEach((v, i) => set('lt-' + i, fmtMoney(v)));
  set('t-gross', fmtMoney(c.gross)); set('t-tax', fmtMoney(c.tax));
  set('t-round', fmtMoney(c.round)); set('t-grand', fmtMoney(c.grand)); set('save-btn', 'Confirm bill for ' + fmtMoney(c.grand));
  if (S.pay.method === 'UPI' && S.pay.mode !== 'credit') {
    refreshUpiQr(S.pay.mode === 'part' ? num(S.pay.amount) : c.grand);
    const label = $('#upi-qr-image');
    if (label) label.alt = `UPI payment QR for ${fmtMoney(S.pay.mode === 'part' ? num(S.pay.amount) : c.grand)}`;
    const amount = $('.upi-qr-copy b');
    if (amount) amount.textContent = `Scan to pay ${fmtMoney(S.pay.mode === 'part' ? num(S.pay.amount) : c.grand)}`;
  }
}
const lineInput = key => (el, e) => { const l = S.cart[+el.dataset.i]; if (!l) return; l[key] = Math.max(0, num(el.value)); saveCart(); refreshTotals(); };
inputs.qty = (el, e) => { const l = S.cart[+el.dataset.i]; if (!l) return; l.qty = Math.max(0, num(el.value)); clampQty(l); saveCart(); refreshTotals(); };
inputs.paid = el => { S.pay.amount = el.value; refreshUpiQr(num(S.pay.amount)); };
inputs.notes = el => { S.pay.notes = el.value; };
changes.cust = el => { S.cartCustomer = el.value; };
changes.method = el => { S.pay.method = el.value; };
actions['transaction-method'] = el => {
  if (el.dataset.method === 'credit') {
    S.pay.mode = 'credit';
  } else {
    S.pay.method = el.dataset.method;
    if (S.pay.mode === 'credit') S.pay.mode = 'full';
  }
  renderBill();
};
actions['part-payment'] = () => { S.pay.mode = S.pay.mode === 'part' ? 'full' : 'part'; renderBill(); };
actions['new-cust'] = () => customerForm(null, true);
actions['save-bill'] = async el => {
  if (!S.cart.length) return toast('Add at least one item', 'err');
  if (S.cart.some(l => !(l.qty > 0))) return toast('Every item needs a quantity above zero', 'err');
  const customer = S.customers.find(c => String(c.id) === String(S.cartCustomer));
  if (S.pay.mode === 'credit' && !customer) {
    toast('Choose a saved customer for a credit transaction', 'err');
    $('[data-ch="cust"]')?.focus();
    return;
  }
  if (customer && !customer.phone) {
    toast('Add a phone number to the selected customer before billing', 'err');
    $('[data-ch="cust"]')?.focus();
    return;
  }
  const c = calcCart();
  const paid = S.pay.mode === 'full' ? c.grand : (S.pay.mode === 'credit' ? 0 : num(S.pay.amount));
  el.disabled = true;
  try {
    const inv = await api('/invoices', {method: 'POST', body: {
      customer_id: S.cartCustomer || null, paid,
      payment_method: S.pay.mode === 'credit' ? 'Credit' : S.pay.method, notes: S.pay.notes,
      items: S.cart.map(l => ({product_id: l.product_id, qty: l.qty}))}});
    S.cart = []; S.cartCustomer = ''; S.pay = {mode: 'full', amount: '', method: 'Cash', notes: ''}; saveCart();
    await Promise.all([refreshProducts(), refreshCustomers()]);
    toast(`Saved ${inv.number}`, 'ok');
    await render(); showInvoice(inv);
  } finally { el.disabled = false; }
};

/* ================= ITEMS ================= */
async function vProducts() {
  return `<header class="page-head"><div><h1>Items</h1><p class="muted">${S.products.filter(p => p.active).length} active items</p></div>
      <button class="btn" data-act="new-product">${ic('plus')} Add item</button></header>
    <div class="toolbar"><div class="search">${ic('search')}<input data-in="pq" value="${esc(S.q.products)}" placeholder="Search by name, SKU or category" aria-label="Search items"></div>
      <button class="chip ${S.lowOnly ? 'on' : ''}" data-act="toggle-low">Low stock only</button>
      <button class="chip ${S.archived ? 'on' : ''}" data-act="toggle-archived">Archived</button></div>
    <div class="list" id="prod-list">${productRows()}</div>`;
}
function productRows() {
  const rows = S.products.filter(p => p.active === !S.archived && matches(p, S.q.products) && (!S.lowOnly || p.stock <= p.low_stock));
  if (!rows.length) return `<div class="empty">${S.products.length ? 'No items match.' : 'No items yet. Add your first item to start billing.'}${S.products.length ? '' : '<br><button class="btn" data-act="new-product">Add item</button>'}</div>`;
  return rows.map(p => `<div class="row prod ${p.active ? '' : 'archived'}">
    <div class="r-main"><b>${esc(p.name)}</b><span class="muted">${esc(p.sku)}${p.category ? ', ' + esc(p.category) : ''}</span></div>
    <div class="r-price num"><b>${fmtMoney(p.price)}</b> <span class="muted">+${p.tax_rate}% tax</span></div>
    <div class="r-stock">${stockBadge(p)}</div>
    <div class="r-act">${p.active ? `<button class="btn ghost sm" data-act="stock" data-id="${p.id}">Stock</button>` : `<button class="btn ghost sm" data-act="restore-product" data-id="${p.id}">Restore</button>`}
      <button class="btn ghost sm" data-act="edit-product" data-id="${p.id}">Edit</button></div></div>`).join('');
}
const refreshProdList = () => { const el = $('#prod-list'); if (el) el.innerHTML = productRows(); };
inputs.pq = el => { S.q.products = el.value; refreshProdList(); };
actions['toggle-low'] = el => { S.lowOnly = !S.lowOnly; el.classList.toggle('on', S.lowOnly); refreshProdList(); };
actions['toggle-archived'] = el => { S.archived = !S.archived; el.classList.toggle('on', S.archived); refreshProdList(); };
actions['new-product'] = () => productForm();
actions['edit-product'] = el => productForm(S.products.find(p => p.id === +el.dataset.id));
actions['restore-product'] = async el => { await api(`/products/${el.dataset.id}/restore`, {method: 'POST', body: {}}); await refreshProducts(); toast('Item restored', 'ok'); render(); };
function productForm(p) {
  const isNew = !p; p = p || {name: '', sku: '', category: '', unit: 'pcs', price: '', cost: '', tax_rate: 0, low_stock: 0};
  openModal(isNew ? 'Add item' : 'Edit item', `<form data-form="product" class="stack"><input type="hidden" name="id" value="${p.id || ''}">
    ${field('Name', 'name', p.name, 'required autofocus maxlength="120"')}
    <div class="two">${field('SKU or barcode', 'sku', isNew ? '' : p.sku, 'placeholder="Auto if blank"')}${field('Category', 'category', p.category, 'list="cats"')}</div>
    <datalist id="cats">${[...new Set(S.products.map(x => x.category).filter(Boolean))].map(c => `<option value="${esc(c)}">`).join('')}</datalist>
    <div class="two">${field('Selling price', 'price', p.price, 'required inputmode="decimal"')}${field('Cost price', 'cost', p.cost, 'inputmode="decimal"')}</div>
    <div class="two">${field('Tax rate (%)', 'tax_rate', p.tax_rate, 'inputmode="decimal"')}${field('Unit', 'unit', p.unit, 'list="units" maxlength="12"')}</div>
    <datalist id="units">${['pcs', 'kg', 'g', 'L', 'ml', 'pack', 'box', 'dozen', 'm'].map(u => `<option value="${u}">`).join('')}</datalist>
    <div class="two">${field('Alert when stock is at or below', 'low_stock', p.low_stock, 'inputmode="decimal"')}${isNew ? field('Opening stock', 'stock', '', 'inputmode="decimal" placeholder="0"') : ''}</div>
    <div class="dlg-actions"><button class="btn">Save item</button><button type="button" class="btn ghost" data-act="close">Cancel</button>
      ${isNew ? '' : `<button type="button" class="btn danger push" data-act="del-product" data-id="${p.id}">Delete</button>`}</div></form>`);
}
forms.product = async f => {
  const d = Object.fromEntries(new FormData(f)); const id = d.id; delete d.id;
  await api(id ? '/products/' + id : '/products', {method: id ? 'PUT' : 'POST', body: d});
  closeModal(); await refreshProducts(); toast(id ? 'Item saved' : 'Item added', 'ok'); render();
};
actions['del-product'] = async el => {
  if (!confirm('Delete this item? If it appears on past bills it will be archived instead.')) return;
  const r = await api('/products/' + el.dataset.id, {method: 'DELETE'});
  S.cart = S.cart.filter(l => l.product_id !== +el.dataset.id); saveCart();
  closeModal(); await refreshProducts(); toast(r.archived ? 'Item archived because it is on past bills' : 'Item deleted', 'ok'); render();
};
actions.stock = async el => {
  const p = S.products.find(x => x.id === +el.dataset.id); if (!p) return;
  const hist = await api(`/stock?product_id=${p.id}&limit=8`);
  openModal('Stock: ' + p.name, `<p style="margin-bottom:12px">In stock now: <b class="num">${fmtQty(p.stock)} ${esc(p.unit)}</b></p>
    <form data-form="stock" class="stack"><input type="hidden" name="product_id" value="${p.id}">
      <div class="chips" role="group" aria-label="Direction"><button type="button" class="chip on" data-act="stock-dir" data-dir="1">Add stock</button><button type="button" class="chip" data-act="stock-dir" data-dir="-1">Remove stock</button></div>
      <input type="hidden" name="dir" value="1">
      <div class="two">${field('Quantity', 'qty', '', 'required inputmode="decimal" autofocus')}
        <label class="f"><span>Reason</span><select name="reason"><option>Purchase or restock</option><option>Customer return</option><option>Damaged or expired</option><option>Stock count correction</option><option>Other</option></select></label></div>
      <button class="btn">Update stock</button></form>
    <h2 style="margin:18px 0 6px">Recent changes</h2>${hist.length ? hist.map(h => `<div class="mini"><span>${esc(h.reason)} <span class="muted">${fmtDay(h.date)}${h.ref ? ', ' + esc(h.ref) : ''}</span></span><b class="num" style="color:${h.change < 0 ? 'var(--danger)' : 'var(--ok)'}">${h.change > 0 ? '+' : ''}${fmtQty(h.change)}</b></div>`).join('') : '<p class="muted">No stock changes yet.</p>'}`);
};
actions['stock-dir'] = el => {
  const f = el.closest('form'); f.elements.dir.value = el.dataset.dir;
  $$('[data-act="stock-dir"]', f).forEach(b => b.classList.toggle('on', b === el));
};
forms.stock = async f => {
  const d = Object.fromEntries(new FormData(f)); const q = num(d.qty);
  if (!(q > 0)) throw new Error('Enter a quantity above zero');
  await api('/stock', {method: 'POST', body: {product_id: d.product_id, change: q * (+d.dir), reason: d.reason}});
  closeModal(); await refreshProducts(); toast('Stock updated', 'ok'); render();
};

/* ================= CUSTOMERS ================= */
async function vCustomers() {
  await refreshCustomers();
  return `<header class="page-head"><div><h1>Customers</h1><p class="muted">${S.customers.length} saved</p></div>
      <button class="btn" data-act="new-customer">${ic('plus')} Add customer</button></header>
    <div class="toolbar"><div class="search">${ic('search')}<input data-in="cq" value="${esc(S.q.customers)}" placeholder="Search by name or phone" aria-label="Search customers"></div></div>
    <div class="list" id="cust-list">${customerRows()}</div>`;
}
function customerRows() {
  const q = S.q.customers.toLowerCase();
  const rows = S.customers.filter(c => !q || `${c.name} ${c.phone}`.toLowerCase().includes(q));
  if (!rows.length) return `<div class="empty">${S.customers.length ? 'No customers match.' : 'No customers yet. Save regulars here to track what they owe.'}</div>`;
  return rows.map(c => `<div class="row cust"><div class="r-main"><b>${esc(c.name)}</b><span class="muted">${esc(c.phone || 'No phone')}${c.address ? ', ' + esc(c.address) : ''}</span></div>
    <div class="num">${c.due > 0
      ? `<span class="badge bad">${fmtMoney(c.due)} total due</span><br><span class="muted">${fmtMoney(c.principal_due)} principal · ${fmtMoney(c.interest_due)} accrued interest</span><br><span class="muted">${Number(c.credit_interest_monthly || 0)}% monthly simple interest on unpaid principal</span>`
      : `<span class="muted">${c.bills} ${c.bills === 1 ? 'bill' : 'bills'}</span>${Number(c.credit_interest_monthly || 0) > 0 ? `<br><span class="muted">${Number(c.credit_interest_monthly)}% monthly simple interest when due</span>` : ''}`}</div>
    <div class="r-act"><button class="btn ghost sm" data-act="cust-bills" data-id="${c.id}">Bills</button>${c.due > 0 && c.phone ? `<a class="btn ghost sm" href="${whatsappWebLink(c.phone, customerReminder(c))}" target="_blank" rel="noopener noreferrer">Remind on WhatsApp</a>` : ''}<button class="btn ghost sm" data-act="edit-customer" data-id="${c.id}">Edit</button></div></div>`).join('');
}
inputs.cq = el => { S.q.customers = el.value; $('#cust-list').innerHTML = customerRows(); };
actions['new-customer'] = () => customerForm();
actions['edit-customer'] = el => customerForm(S.customers.find(c => c.id === +el.dataset.id));
actions['cust-bills'] = el => { S.invCustomer = el.dataset.id; S.invStatus = 'all'; S.q.invoices = ''; location.hash = '#/invoices'; };
function customerForm(c, fromBill = false) {
  const isNew = !c; c = c || {name: '', phone: '', email: '', address: '', gstin: ''};
  openModal(isNew ? 'Add customer' : 'Edit customer', `<form data-form="customer" class="stack"><input type="hidden" name="id" value="${c.id || ''}"><input type="hidden" name="from_bill" value="${fromBill ? '1' : ''}">
    ${field('Name', 'name', c.name, 'required autofocus maxlength="120"')}
    <div class="two">    ${field('Phone', 'phone', c.phone, 'required type="tel" inputmode="tel"')}${field('Email', 'email', c.email, 'type="email"')}</div>
    ${field('Address', 'address', c.address)}${field('GSTIN (optional)', 'gstin', c.gstin, 'maxlength="20"')}
    <div class="dlg-actions"><button class="btn">Save customer</button><button type="button" class="btn ghost" data-act="close">Cancel</button>
      ${isNew ? '' : `<button type="button" class="btn danger push" data-act="del-customer" data-id="${c.id}">Delete</button>`}</div></form>`);
}
forms.customer = async f => {
  const d = Object.fromEntries(new FormData(f)); const id = d.id, fromBill = d.from_bill; delete d.id; delete d.from_bill;
  const saved = await api(id ? '/customers/' + id : '/customers', {method: id ? 'PUT' : 'POST', body: d});
  closeModal(); await refreshCustomers();
  if (fromBill) { S.cartCustomer = String(saved.id); renderBill(); }
  toast('Customer saved', 'ok'); if (S.view === 'customers') render();
};
actions['del-customer'] = async el => {
  if (!confirm('Delete this customer?')) return;
  await api('/customers/' + el.dataset.id, {method: 'DELETE'}); closeModal(); await refreshCustomers(); toast('Customer deleted', 'ok'); render();
};

/* ================= INVOICES ================= */
async function vInvoices() {
  const cust = S.customers.find(c => String(c.id) === String(S.invCustomer));
  const yearLabel = S.financialYear === 'all' ? 'All years' : financialYearLabel(S.financialYear);
  return `<header class="page-head"><h1>Invoices</h1><button class="btn ghost" data-act="dl-csv">Download ${yearLabel} CSV</button></header>
    <div class="toolbar"><div class="search">${ic('search')}<input data-in="iq" value="${esc(S.q.invoices)}" placeholder="Search by invoice number or customer" aria-label="Search invoices"></div></div>
    <div class="toolbar chips" id="inv-chips">${[['all', 'All'], ['due', 'Money due'], ['paid', 'Paid'], ['void', 'Void']].map(([k, t]) => `<button class="chip ${S.invStatus === k ? 'on' : ''}" data-act="inv-status" data-s="${k}">${t}</button>`).join('')}
      ${cust ? `<button class="chip on" data-act="inv-clear-cust">Customer: ${esc(cust.name)} &times;</button>` : ''}</div>
    <div class="list" id="inv-list"><div class="empty">Loading&hellip;</div></div>`;
}
async function refreshInvoiceList() {
  const el = $('#inv-list'); if (!el) return;
  const p = new URLSearchParams({q: S.q.invoices, status: S.invStatus, customer_id: S.invCustomer,
    financial_year: S.financialYear});
  S.invoices = await api('/invoices?' + p);
  el.innerHTML = S.invoices.length ? S.invoices.map(i => `<button class="row invr" data-act="open-inv" data-id="${i.id}">
    <b class="a">${esc(i.number)}</b><span class="b">${esc(i.customer.name)}</span><span class="muted c">${fmtDate(i.date)}</span>
    <b class="num d">${fmtMoney(i.grand_total)}${i.status !== 'void' && i.total_due > 0 ? `<br><span class="muted" style="font-weight:500">${fmtMoney(i.total_due)} due</span>` : ''}</b><span class="e">${statusBadge(i.status)}</span></button>`).join('')
    : '<div class="empty">No invoices found.</div>';
}
inputs.iq = debounce(el => { S.q.invoices = el.value; refreshInvoiceList(); });
actions['inv-status'] = el => { S.invStatus = el.dataset.s; $$('#inv-chips [data-s]').forEach(b => b.classList.toggle('on', b === el)); refreshInvoiceList(); };
actions['inv-clear-cust'] = () => { S.invCustomer = ''; render(); };
actions['dl-csv'] = () => download('/export/invoices.csv' + financialYearQuery(), 'invoices.csv');
actions['open-inv'] = async el => showInvoice(await api('/invoices/' + el.dataset.id));

function invoiceHTML(inv) {
  const s = S.settings, c = inv.customer;
  return `<article class="inv">
    <div class="inv-top"><div><h3>${esc(s.business_name)}</h3>${s.address ? `<p>${esc(s.address)}</p>` : ''}${s.phone ? `<p>Phone ${esc(s.phone)}</p>` : ''}${s.gstin ? `<p>GSTIN ${esc(s.gstin)}</p>` : ''}</div>
      <div class="inv-meta"><p>Invoice</p><b>${esc(inv.number)}</b><p>${fmtDate(inv.date)}</p>${inv.status === 'void' ? '<span class="void-mark">VOID</span>' : ''}</div></div>
    <div class="inv-to"><div><p>Billed to</p><b>${esc(c.name)}</b>${c.phone ? `<p>${esc(c.phone)}</p>` : ''}${c.address ? `<p>${esc(c.address)}</p>` : ''}${c.gstin ? `<p>GSTIN ${esc(c.gstin)}</p>` : ''}</div></div>
    <div class="tbl-wrap"><table class="num"><thead><tr><th>Item</th><th>Qty</th><th>Rate</th><th>Tax</th><th>Amount</th></tr></thead><tbody>
      ${inv.items.map(l => `<tr><td>${esc(l.name)}${l.discount_pct ? `<small>${l.discount_pct}% off</small>` : ''}</td><td>${fmtQty(l.qty)} ${esc(l.unit)}</td><td>${fmtMoney(l.price)}</td><td>${l.tax_rate}%</td><td>${fmtMoney(l.total)}</td></tr>`).join('')}
    </tbody></table></div>
    <div class="inv-sum num"><div><span>Subtotal</span><span>${fmtMoney(inv.subtotal)}</span></div>
      ${inv.discount_total ? `<div><span>Discount</span><span>&minus;${fmtMoney(inv.discount_total)}</span></div>` : ''}
      <div><span>Tax</span><span>${fmtMoney(inv.tax_total)}</span></div>
      ${inv.round_off ? `<div><span>Round off</span><span>${fmtMoney(inv.round_off)}</span></div>` : ''}
      <div class="g"><span>Total</span><span>${fmtMoney(inv.grand_total)}</span></div>
      <div><span>Paid</span><span>${fmtMoney(inv.paid)}</span></div>
      ${inv.interest_accrued > 0 ? `<div><span>Credit interest accrued (${S.settings.credit_interest_monthly}% monthly, simple)</span><span>${fmtMoney(inv.interest_accrued)}</span></div>
      <div><span>Interest paid</span><span>${fmtMoney(inv.interest_paid)}</span></div>` : ''}
      ${inv.status !== 'void' && inv.interest_balance > 0 ? `<div><span>Interest outstanding</span><span>${fmtMoney(inv.interest_balance)}</span></div>` : ''}
      ${inv.status !== 'void' && inv.total_due > 0 ? `<div><b>Balance due</b><b>${fmtMoney(inv.total_due)}</b></div>` : ''}</div>
    ${inv.payments.length ? `<p class="inv-pay">Payments: ${inv.payments.map(p => `${fmtMoney(p.amount)} by ${esc(p.method)} on ${fmtDay(p.date)}`).join('; ')}</p>` : ''}
    ${inv.notes ? `<p class="inv-pay">Note: ${esc(inv.notes)}</p>` : ''}
    ${s.footer_note ? `<p class="inv-foot">${esc(s.footer_note)}</p>` : ''}</article>`;
}
function whatsappPhone(phone) {
  let number = String(phone || '').replace(/\D/g, '');
  if (number.length === 10 && S.settings.country_code) number = S.settings.country_code + number;
  return number;
}
function whatsappWebLink(phone, message) {
  const number = whatsappPhone(phone);
  return number ? `https://wa.me/${encodeURIComponent(number)}?text=${encodeURIComponent(message)}` : '';
}
function customerReminder(customer) {
  return `Hello ${customer.name}, a friendly payment reminder from ${S.settings.business_name}. ` +
    `Your pending bill balance is ${fmtMoney(customer.due)} (${fmtMoney(customer.principal_due)} principal and ${fmtMoney(customer.interest_due)} accrued interest)` +
    (Number(customer.credit_interest_monthly) > 0
      ? `. Interest is calculated at ${Number(customer.credit_interest_monthly)}% monthly simple interest on unpaid principal`
      : '') +
    `. Please let us know if you have already paid. Thank you.`;
}
function whatsappLink(inv) {
  const lines = inv.items.map(line =>
    `${line.name} × ${fmtQty(line.qty)} ${line.unit} — ${fmtMoney(line.total)}`).join('\n');
  const due = inv.status !== 'void' && inv.total_due > 0;
  const message = `Hello ${inv.customer.name},\n${S.settings.business_name} — ${inv.status === 'void' ? 'VOID invoice ' : 'invoice '}${inv.number} (${fmtDay(inv.date)})\n` +
    `${lines}\nTotal: ${fmtMoney(inv.grand_total)}\nPaid: ${fmtMoney(inv.paid)}\n` +
    (due ? `Balance due: ${fmtMoney(inv.total_due)}\n` : '') +
    (inv.interest_accrued > 0 ? `Interest accrued: ${fmtMoney(inv.interest_accrued)}\n` : '') +
    `${S.settings.footer_note || 'Thank you for your business!'}`;
  return whatsappWebLink(inv.customer.phone, message);
}
function showInvoice(inv) {
  S.current = inv;
  const wa = whatsappLink(inv), due = inv.status !== 'void' && inv.total_due > 0;
  openModal('Invoice ' + inv.number, invoiceHTML(inv) + `<div class="dlg-actions">
    <button class="btn" data-act="print-inv">${ic('print')} Print</button>
    ${wa ? `<a class="btn ghost" href="${wa}" target="_blank" rel="noopener noreferrer">Send invoice via WhatsApp</a>` : ''}
    ${due ? '<button class="btn ghost" data-act="pay-inv">Record payment</button>' : ''}
    ${inv.status !== 'void' ? '<button class="btn danger push" data-act="void-inv">Void bill</button>' : ''}</div>`, {wide: true});
}
actions['print-inv'] = () => { $('#print-area').innerHTML = invoiceHTML(S.current); window.print(); };
actions['pay-inv'] = () => {
  const inv = S.current;
  openModal('Record payment', `<form data-form="pay" class="stack"><p class="muted">${esc(inv.number)}, total due <b class="num">${fmtMoney(inv.total_due)}</b> (bill principal ${fmtMoney(inv.balance)}, interest ${fmtMoney(inv.interest_balance)})</p>
    <p class="muted">Payments reduce bill principal first, then accrued interest.</p>
    ${field('Amount received', 'amount', inv.total_due, 'required inputmode="decimal" autofocus')}
    <label class="f"><span>Paid by</span><select name="method">${['Cash', 'UPI'].map(m => `<option>${m}</option>`).join('')}</select></label>
    <button class="btn">Save payment</button></form>`);
};
forms.pay = async f => {
  const inv = await api(`/invoices/${S.current.id}/payments`, {method: 'POST', body: Object.fromEntries(new FormData(f))});
  await refreshCustomers(); toast('Payment saved', 'ok'); showInvoice(inv); if (S.view === 'invoices') refreshInvoiceList(); else if (S.view === 'customers') render();
};
actions['void-inv'] = async () => {
  if (!confirm(`Void ${S.current.number}? The items go back into stock and the bill stops counting in your sales.`)) return;
  const inv = await api(`/invoices/${S.current.id}/void`, {method: 'POST', body: {}});
  await Promise.all([refreshProducts(), refreshCustomers()]); toast('Bill voided', 'ok'); showInvoice(inv); render();
};

/* ================= SETTINGS ================= */
async function vSettings() {
  const s = S.settings, i = S.info;
  const sections = [
    ['shop', 'Shop details'],
    ['billing', 'Billing & tax'],
    ['security', 'Account & security'],
    ['mobile', 'Mobile access'],
    ['data', 'Data & integrations'],
    ['help', 'Help & support']
  ];
  return `<header class="page-head"><h1>Settings</h1></header>
    <div class="settings-layout">
      <nav class="settings-menu" aria-label="Settings sections">
        ${sections.map(([id, label]) => `<button type="button" data-act="settings-section" data-settings="${id}" ${S.settingsSection === id ? 'class="active" aria-current="page"' : ''}>${label}</button>`).join('')}
      </nav>
      <div class="settings-content">
    <section class="settings-pane" data-settings-pane="shop" ${S.settingsSection !== 'shop' ? 'hidden' : ''}>
    <form class="card stack" data-form="settings"><h2>Shop details</h2>
      ${field('Shop name', 'business_name', s.business_name, 'required')}
      ${field('Address', 'address', s.address)}
      ${field('Phone', 'phone', s.phone, 'type="tel"')}
      ${field('GSTIN', 'gstin', s.gstin)}
      <div class="two">${field('Currency symbol', 'currency', s.currency, 'maxlength="4"')}${field('Invoice number prefix', 'invoice_prefix', s.invoice_prefix, 'maxlength="12"')}</div>
      ${field('Country code for WhatsApp', 'country_code', s.country_code, 'inputmode="numeric" maxlength="4"')}
      ${field('Message at the bottom of invoices', 'footer_note', s.footer_note)}
      <button class="btn">Save shop details</button></form>
    </section>
    <section class="settings-pane" data-settings-pane="billing" ${S.settingsSection !== 'billing' ? 'hidden' : ''}>
    <form class="card stack" data-form="settings"><h2>Billing & tax</h2>
      ${field('UPI ID', 'upi_id', s.upi_id || '', 'maxlength="164" placeholder="name@bank"')}
      ${field('Credit interest (% per month)', 'credit_interest_monthly', s.credit_interest_monthly || 0, 'type="number" inputmode="decimal" min="0" max="100" step="0.01" required')}
      <p class="muted">Simple interest is added monthly on unpaid bill principal. Payments reduce principal first; interest does not compound. This rate applies to existing unpaid credit bills from their invoice dates as well as new credit bills.</p>
      <label class="check"><input type="checkbox" name="round_off" ${s.round_off ? 'checked' : ''}> Round bill totals to the nearest whole amount</label>
      <label class="check"><input type="checkbox" name="allow_negative_stock" ${s.allow_negative_stock ? 'checked' : ''}> Allow billing items that are out of stock</label>
      <button class="btn">Save billing settings</button></form>
    </section>
    <section class="settings-pane stack" data-settings-pane="security" ${S.settingsSection !== 'security' ? 'hidden' : ''}>
    <div class="card stack"><h2>Account sign-in</h2>
      <p class="muted">Desktop sign-in uses an email and password. Passwords must be 8 to 256 characters. Leave the new password fields empty to change only your email.</p>
      <form class="stack" data-form="account">
        ${field('Account email', 'email', i.account_email || '', 'type="email" maxlength="254" autocomplete="username" required')}
        ${field('Current password', 'current_password', '', 'type="password" autocomplete="current-password" required')}
        ${field('New password (optional)', 'new_password', '', 'type="password" minlength="8" maxlength="256" autocomplete="new-password"')}
        ${field('Confirm new password', 'confirm_password', '', 'type="password" minlength="8" maxlength="256" autocomplete="new-password"')}
        <button class="btn">Save account</button>
      </form></div>
    </section>
    <section class="settings-pane stack" data-settings-pane="mobile" ${S.settingsSection !== 'mobile' ? 'hidden' : ''}>
    <div class="card stack"><h2>Mobile billing access</h2>
      <p class="muted">${i.mobile_pin_enabled ? 'Mobile billing is protected by its own PIN.' : 'Set a PIN to enable the billing-only mobile page.'} Use 4 to 12 digits.</p>
      <form class="stack" data-form="mobile-pin">
        ${field(i.mobile_pin_enabled ? 'New mobile PIN' : 'Mobile PIN', 'new_pin', '', 'type="password" inputmode="numeric" autocomplete="new-password" minlength="4" maxlength="12" pattern="[0-9]{4,12}" required')}
        ${field('Confirm mobile PIN', 'confirm_pin', '', 'type="password" inputmode="numeric" autocomplete="new-password" minlength="4" maxlength="12" pattern="[0-9]{4,12}" required')}
        <button class="btn">Save mobile PIN</button>
      </form>
      ${i.mobile_pin_enabled ? '<button class="btn danger" data-act="disable-mobile-billing">Disable mobile billing</button>' : ''}
      ${i.lan_url ? `<p>On the same Wi-Fi, open <b style="overflow-wrap:anywhere">${esc(i.lan_url)}/mobile</b> on the phone.</p>` : '<p class="muted">Start StockBill on your Wi-Fi interface to access the mobile page from another device.</p>'}
      ${i.lan_url ? '<div class="stack"><b>Scan to open mobile billing</b><img id="mobile-access-qr" alt="QR code for the StockBill mobile access URL" width="220" height="220" hidden><p id="mobile-access-qr-error" class="muted" role="status"></p></div>' : ''}
      <p class="muted">This page only supports billing; its PIN cannot access the main app APIs. Use only on a trusted private Wi-Fi network: HTTP does not encrypt the PIN, account credentials, or transaction data. Camera scanning requires HTTPS, so on this HTTP page use search, type a SKU/barcode, or connect a keyboard-style scanner.</p></div>
    <div class="card stack"><h2>Use on your phone</h2>
      ${i.lan_url ? `<p>On the same Wi-Fi, open <b style="overflow-wrap:anywhere">${esc(i.lan_url)}</b> in your phone's browser, then use "Add to Home screen".</p>` : '<p class="muted">The server was started for this computer only. Restart without <code>--host 127.0.0.1</code> to use it on a phone.</p>'}
      <p class="muted">The desktop app requires your account email and password. The mobile billing page accepts only its separate mobile PIN.</p></div>
    </section>
    <section class="settings-pane stack" data-settings-pane="data" ${S.settingsSection !== 'data' ? 'hidden' : ''}>
    <div class="card stack"><h2>Your data</h2>
      <p class="muted">Everything is stored in one JSON file on the computer running StockBill. A copy is also kept each day in a backups folder next to it.</p>
      <p style="overflow-wrap:anywhere"><b>Data file:</b> ${esc(i.data_file || '')}</p>
      <div class="chips"><button class="btn ghost" data-act="dl-backup">Download backup</button><button class="btn ghost" data-act="dl-csv">Download invoices CSV</button></div></div>
    <div class="card stack"><h2>WhatsApp Web</h2>
      <p class="muted">Link this browser using WhatsApp's official QR code. Open WhatsApp Web, scan the QR code with WhatsApp on your phone, then use the reminder links on customer and invoice bills. Messages open as drafts for you to review and send.</p>
      <p><a class="btn ghost" href="https://web.whatsapp.com/" target="_blank" rel="noopener noreferrer">Open WhatsApp Web to scan QR</a></p></div>
    </section>
    <section class="settings-pane stack" data-settings-pane="help" ${S.settingsSection !== 'help' ? 'hidden' : ''}>
    <div class="card stack"><h2>Help</h2>
      <h3>Desktop sign-in</h3><p class="muted">Use the email and password created the first time StockBill was opened. Update them in Account &amp; security. There is no in-app password reset, so keep your credentials safe and make regular data backups.</p>
      <h3>Mobile billing</h3><p class="muted">Connect the phone to the same Wi-Fi as this computer, scan the QR code in Mobile access, then sign in with the mobile PIN. The phone page is limited to creating bills and cannot open shop settings or reports.</p>
      <h3>Connection and scanning</h3><p class="muted">Keep StockBill running while using another device. If the QR link does not connect, confirm both devices are on the same trusted Wi-Fi and that the computer firewall allows StockBill's port. HTTP does not encrypt passwords, PINs, or business data; use HTTPS on networks you do not trust. Camera scanning requires HTTPS and a supported browser; SKU search and keyboard-style scanners also work without camera access.</p></div>
    <div class="card stack"><h2>Support</h2>
      <p class="muted">Contact Chandra for StockBill support.</p>
      <p><a class="btn ghost" href="tel:+9182395594">Call 9182395594</a> <a class="btn ghost" href="https://wa.me/9182395594" target="_blank" rel="noopener noreferrer">Message on WhatsApp</a></p></div>
    </section>
      </div>
    </div>`;
}
actions['settings-section'] = el => {
  S.settingsSection = el.dataset.settings;
  $$('.settings-menu button').forEach(button => {
    const active = button.dataset.settings === S.settingsSection;
    button.classList.toggle('active', active);
    if (active) button.setAttribute('aria-current', 'page');
    else button.removeAttribute('aria-current');
  });
  $$('.settings-pane').forEach(pane => {
    pane.hidden = pane.dataset.settingsPane !== S.settingsSection;
  });
  if (S.settingsSection === 'mobile') loadMobileAccessQr();
};
forms.settings = async f => {
  const fd = new FormData(f), d = Object.fromEntries(fd);
  if (f.elements.namedItem('round_off')) d.round_off = fd.has('round_off');
  if (f.elements.namedItem('allow_negative_stock')) d.allow_negative_stock = fd.has('allow_negative_stock');
  S.settings = await api('/settings', {method: 'PUT', body: d});
  document.title = S.settings.business_name + ' | StockBill'; renderNav(); toast('Settings saved', 'ok');
};
forms.account = async f => {
  const data = Object.fromEntries(new FormData(f));
  if (!!data.new_password !== !!data.confirm_password) {
    throw new Error('Enter and confirm the new password');
  }
  if (data.new_password && data.new_password !== data.confirm_password) {
    throw new Error('New password and confirmation do not match');
  }
  if (!data.new_password) {
    delete data.new_password;
    delete data.confirm_password;
  }
  const result = await api('/account', {method: 'POST', body: data});
  S.info.account_email = result.account_email;
  sessionToken = result.session_token;
  toast('Account updated', 'ok');
  render();
};
forms['mobile-pin'] = async f => {
  const data = Object.fromEntries(new FormData(f));
  if (data.new_pin !== data.confirm_pin) throw new Error('Mobile PIN and confirmation do not match');
  await api('/mobile-pin', {method: 'POST', body: {new_pin: data.new_pin}});
  S.info.mobile_pin_enabled = true;
  toast('Mobile billing PIN saved', 'ok');
  render();
};
actions['disable-mobile-billing'] = async () => {
  if (!confirm('Disable access to the mobile billing page?')) return;
  await api('/mobile-pin', {method: 'POST', body: {disable: true}});
  S.info.mobile_pin_enabled = false;
  toast('Mobile billing access disabled', 'ok');
  render();
};
actions['dl-backup'] = () => download('/export/backup.json', `stockbill-backup-${new Date().toISOString().slice(0, 10)}.json`);
/* ================= ACCOUNTS ================= */
async function vAccounts() {
  const [summary, expenses] = await Promise.all([
    api('/accounts' + financialYearQuery()), api('/expenses' + financialYearQuery())
  ]);
  S.expenses = expenses;
  const yearLabel = S.financialYear === 'all' ? 'all years' : financialYearLabel(S.financialYear);
  const flowRows = (values, empty) => Object.entries(values).length
    ? Object.entries(values).sort((a, b) => b[1] - a[1]).map(([method, amount]) =>
      `<div class="mini"><span>${esc(method)}</span><b class="num">${fmtMoney(amount)}</b></div>`).join('')
    : `<p class="muted">${empty}</p>`;
  const creditRows = summary.credit_customers.length
    ? summary.credit_customers.map(customer => `<div class="row credit-row">
      <div class="r-main credit-customer"><b>${esc(customer.name)}</b><span class="muted">${esc(customer.phone || 'No phone')}</span></div>
      <div class="muted credit-detail">Principal ${fmtMoney(customer.principal_due)} · Interest ${fmtMoney(customer.interest_due)} · ${Number(customer.credit_interest_monthly || 0)}% monthly</div>
      <b class="num r-right credit-total">${fmtMoney(customer.total_due)}</b>
      <div class="r-act"><button class="btn ghost sm" data-act="cust-bills" data-id="${customer.id}">Bills</button></div>
    </div>`).join('')
    : '<div class="empty">No outstanding customer credit.</div>';
  return `<header class="page-head"><div><h1>Accounts</h1><p class="muted">Financial summary and expenses for ${yearLabel}</p></div>
      <div class="chips"><button class="btn ghost" data-act="prepare-wa-reminders">Prepare WhatsApp reminders</button><button class="btn ghost" data-act="dl-expenses">Export expenses</button><button class="btn" data-act="new-expense">Record expense</button></div></header>
    <section class="tiles">
      <div class="tile"><span class="muted">Cash collected</span><b class="num">${fmtMoney(summary.year_collected)}</b><span class="muted">Payments received during ${yearLabel}</span></div>
      <div class="tile"><span class="muted">Expenses</span><b class="num">${fmtMoney(summary.year_expenses)}</b><span class="muted">${summary.year_expense_count} recorded</span></div>
      <div class="tile"><span class="muted">Net cash movement</span><b class="num">${fmtMoney(summary.year_net_cash)}</b><span class="muted">Collections less recorded expenses</span></div>
      <div class="tile"><span class="muted">Receivables</span><b class="num">${fmtMoney(summary.receivables)}</b><span class="muted">Unpaid balances on invoices in this period</span></div>
      <div class="tile"><span class="muted">Tax billed</span><b class="num">${fmtMoney(summary.year_tax_billed)}</b><span class="muted">Not a filed tax return</span></div>
    </section>
    <section class="grid2">
      <div class="card stack"><div><h2>Income statement</h2><p class="muted">Sales and recorded costs for ${yearLabel}; excludes tax collected.</p></div>
        <div class="mini"><span>Net sales</span><b class="num">${fmtMoney(summary.net_sales)}</b></div>
        <div class="mini"><span>Cost of goods sold</span><b class="num">${fmtMoney(summary.cost_of_goods_sold)}</b></div>
        <div class="mini"><span>Gross profit (recorded costs)</span><b class="num">${fmtMoney(summary.gross_profit)}</b></div>
        <div class="mini"><span>Operating expenses</span><b class="num">${fmtMoney(summary.income_statement_expenses)}</b></div>
        <div class="mini"><b>Net operating profit (recorded costs)</b><b class="num">${fmtMoney(summary.net_operating_profit)}</b></div>
        ${summary.uncosted_sales > 0 ? `<p class="muted">Cost snapshots are missing for older invoice lines representing ${fmtMoney(summary.uncosted_sales)} in sales. Profit shown excludes those unknown costs.</p>` : ''}
        <p class="muted">COGS uses each item's saved cost at sale time for new invoices.</p>
      </div>
      <div class="card stack"><div><h2>Cash flow statement</h2><p class="muted">${yearLabel}: actual payments received and expenses recorded.</p></div>
        <div><h3>Cash received by method</h3>${flowRows(summary.cash_in_by_method, 'No payments received in this period.')}</div>
        <div><h3>Cash paid by method</h3>${flowRows(summary.cash_out_by_method, 'No expenses recorded in this period.')}</div>
        <div class="mini"><b>Net cash movement</b><b class="num">${fmtMoney(summary.year_net_cash)}</b></div>
      </div>
    </section>
    <header class="page-head"><div><h2>Outstanding credit by customer</h2><p class="muted">Current balances across open credit bills (all invoice dates).</p></div></header>
    <div class="list">${creditRows}</div>
    <header class="page-head"><div><h2>Expense register</h2><p class="muted">Most recent expenses</p></div></header>
    <div class="toolbar"><div class="search">${ic('search')}<input data-in="eq" value="${esc(S.q.expenses)}" placeholder="Search category, party, reference or note" aria-label="Search expenses"></div></div>
    <div class="list" id="expense-list">${expenseRows()}</div>`;
}
actions['prepare-wa-reminders'] = async () => {
  const customers = await api('/customers');
  const owing = customers.filter(customer => customer.due > 0);
  const reachable = owing.filter(customer => whatsappPhone(customer.phone));
  const totalDue = owing.reduce((total, customer) => total + customer.due, 0);
  const rows = reachable.map(customer => `<div class="row">
    <div class="r-main"><b>${esc(customer.name)}</b><span class="muted">${esc(customer.phone)}</span></div>
    <div class="num r-right"><b>${fmtMoney(customer.due)} due</b>${customer.interest_due > 0 ? `<span class="muted">${fmtMoney(customer.interest_due)} interest</span>` : ''}</div>
    <div class="r-act"><a class="btn ghost sm" href="${whatsappWebLink(customer.phone, customerReminder(customer))}" target="_blank" rel="noopener noreferrer">Open reminder draft</a></div></div>`).join('');
  const unavailable = owing.length - reachable.length;
  openModal('WhatsApp payment reminders', `<p class="muted">Outstanding total: <b class="num">${fmtMoney(totalDue)}</b> across ${owing.length} ${owing.length === 1 ? 'customer' : 'customers'}. Select a draft to open it in WhatsApp, review it, and send it yourself. Nothing is sent automatically.</p>
    ${rows ? `<div class="list">${rows}</div>` : '<div class="empty">No customers with a phone number and a pending balance are ready for a reminder.</div>'}
    ${unavailable ? `<p class="muted" style="margin-top:12px">${unavailable} ${unavailable === 1 ? 'customer has' : 'customers have'} a pending balance but no usable phone number; add a phone number in Customers to prepare a reminder.</p>` : ''}`);
};
function expenseRows() {
  const q = S.q.expenses.toLowerCase();
  const rows = (S.expenses || []).filter(expense => !q ||
    `${expense.category} ${expense.party} ${expense.reference} ${expense.notes}`.toLowerCase().includes(q));
  if (!rows.length) return `<div class="empty">${S.expenses && S.expenses.length ? 'No expenses match.' : 'No expenses recorded yet.'}</div>`;
  return rows.map(expense => `<div class="row expense-row">
    <div class="r-main"><b>${esc(expense.category)}</b><span class="muted">${esc(expense.party || 'No payee')}${expense.reference ? ' · ' + esc(expense.reference) : ''}</span></div>
    <span class="muted expense-date">${fmtDate(expense.date)}</span><span class="expense-method">${esc(expense.method)}</span>
    <b class="num expense-amount">${fmtMoney(expense.amount)}</b>
    ${expense.notes ? `<span class="muted expense-note">${esc(expense.notes)}</span>` : ''}</div>`).join('');
}
inputs.eq = el => { S.q.expenses = el.value; const list = $('#expense-list'); if (list) list.innerHTML = expenseRows(); };
actions['new-expense'] = () => openModal('Record expense', `<form data-form="expense" class="stack">
    <div class="two">${field('Amount', 'amount', '', 'required inputmode="decimal" autofocus')}
      <label class="f"><span>Category</span><select name="category">${['Rent', 'Utilities', 'Salaries', 'Transport', 'Supplies', 'Marketing', 'Repairs', 'Taxes & fees', 'Other'].map(c => `<option>${c}</option>`).join('')}</select></label></div>
    <div class="two">${field('Paid to', 'party', '', 'maxlength="120"')}${field('Reference', 'reference', '', 'maxlength="60" placeholder="Receipt or transaction ID"')}</div>
    <label class="f"><span>Paid by</span><select name="method">${['Cash', 'UPI', 'Card', 'Bank', 'Other'].map(method => `<option>${method}</option>`).join('')}</select></label>
    ${field('Note', 'notes', '', 'maxlength="240"')}
    <div class="dlg-actions"><button class="btn">Save expense</button><button type="button" class="btn ghost" data-act="close">Cancel</button></div></form>`);
forms.expense = async f => {
  await api('/expenses', {method: 'POST', body: Object.fromEntries(new FormData(f))});
  closeModal(); toast('Expense recorded', 'ok');
  if (S.view === 'accounts') render();
};
actions['dl-expenses'] = () => download('/export/expenses.csv' + financialYearQuery(), 'expenses.csv');

/* ---------- start ---------- */
async function startApp() {
  try {
    await loadAll();
    if (!location.hash) location.hash = '#/dashboard';
    render();
  } catch (err) {
    if ($('#login-screen').hidden) toast(err.message, 'err');
    else $('#login-error').textContent = err.message;
  }
}
(async function init() {
  try {
    const response = await fetch('/api/login');
    if (!response.ok) throw new Error('Could not check login settings.');
    const info = await response.json();
    accountConfigured = !!info.account_configured;
    showLogin(accountConfigured);
  } catch (err) {
    showLogin(false, err.message || "Can't reach the server.");
  }
})();
})();
</script>
</body>
</html>
"""

MOBILE_PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#14303A"><title>StockBill mobile billing</title>
<style>
:root{font-family:system-ui,-apple-system,"Segoe UI",sans-serif;color:#18343b;background:#f1f4f2;font-size:16px}
*{box-sizing:border-box}body{margin:0}button,input,select,textarea{font:inherit}button{min-height:44px;border:0;border-radius:9px;padding:10px 14px;background:#14303a;color:white;font-weight:700}
input,select,textarea{width:100%;min-height:44px;border:1px solid #d4dedb;border-radius:8px;padding:10px;background:#fff;color:inherit}
main{max-width:720px;margin:auto;padding:14px;padding-bottom:40px}.card{background:white;border:1px solid #dce4e1;border-radius:12px;padding:16px;margin-bottom:12px}
h1{font-size:21px;margin:0}h2{font-size:17px;margin:0 0 10px}.muted{color:#687b7f;font-size:14px}.stack{display:grid;gap:10px}
.head{display:flex;justify-content:space-between;align-items:center;margin-bottom:12px}.brand small{display:block;color:#687b7f;font-weight:500}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:8px}.product,.line{border:1px solid #e0e7e4;border-radius:9px;padding:11px;background:white;color:inherit;text-align:left}
.product{display:flex;flex-direction:column;gap:4px;min-height:92px}.product:disabled{opacity:.5}.product small,.line small{color:#687b7f}
.line{display:grid;grid-template-columns:1fr auto;gap:7px;margin-bottom:8px}.steps{display:flex;align-items:center;gap:8px}.steps button{min-width:42px;padding:6px}.steps b{min-width:26px;text-align:center}
.chips{display:flex;gap:8px}.chips button{flex:1;background:#eef3f1;color:#18343b;border:1px solid #d4dedb}.chips button.on{background:#14303a;color:white}
.total{display:flex;justify-content:space-between;padding:10px 0;font-weight:800;font-size:18px;border-top:1px solid #e0e7e4}
.primary{width:100%;background:#f2a900;color:#18343b}.notice{padding:10px;background:#fff1d6;border-radius:8px}.error{color:#a52828}.qr{display:flex;align-items:center;gap:12px}.qr img{width:120px;height:120px}
[hidden]{display:none!important}
.scanner{width:100%;max-height:55vh;background:#102329;border-radius:9px}
</style></head>
<body><main>
  <section id="login" class="card stack">
    <div class="brand"><h1>StockBill</h1><small>Mobile billing</small></div>
    <p id="login-help" class="muted">Enter the mobile billing PIN.</p>
    <form id="login-form" class="stack"><input id="pin" type="password" inputmode="numeric" autocomplete="one-time-code" minlength="4" maxlength="12" placeholder="Mobile PIN" aria-label="Mobile PIN" required><button>Sign in</button></form>
    <p id="login-error" class="error" role="alert"></p>
    <p class="muted">The mobile PIN only grants access to billing. Use only on a trusted private Wi-Fi network. Camera scanning requires HTTPS, a supported browser, and a product QR/barcode containing its SKU.</p>
  </section>
  <section id="app" hidden>
    <header class="head"><div class="brand"><h1 id="shop-name">StockBill</h1><small>New transaction</small></div><button id="logout" type="button">Log out</button></header>
    <section class="card stack">
      <h2>Find items</h2>
      <input id="search" autocomplete="off" placeholder="Search item or enter SKU/barcode" aria-label="Search item or enter SKU/barcode">
      <p class="muted">A keyboard-style barcode reader can type into this field and press Enter.</p>
      <button id="scan-toggle" type="button">Scan barcode / QR code</button>
      <video id="scanner" class="scanner" playsinline hidden aria-label="Camera preview"></video>
      <p id="scan-help" class="muted" role="status"></p>
      <div id="products" class="grid"></div>
    </section>
    <section class="card stack">
      <h2>Current bill</h2>
      <label class="stack"><span>Customer (optional for walk-in sales)</span><select id="customer"></select></label>
      <div id="cart"></div>
      <div class="total"><span>Total</span><span id="total"></span></div>
      <div class="chips" role="group" aria-label="Payment method">
        <button type="button" data-pay="Cash">Cash</button>
        <button type="button" data-pay="UPI">UPI</button>
        <button type="button" data-pay="Credit">Credit</button>
      </div>
      <button id="part-toggle" class="chips" type="button">Record part payment</button>
      <label id="part-amount-wrap" class="stack" hidden><span>Amount received</span><input id="part-amount" type="number" min="0" step="0.01" inputmode="decimal"></label>
      <p id="credit-note" class="muted" hidden>The full bill amount will be added to this customer's pending balance.</p>
      <div id="qr-wrap" class="qr notice" hidden><img id="qr" alt="UPI payment QR"><span id="qr-label"></span></div>
      <label class="stack"><span>Note</span><input id="note" maxlength="200" placeholder="Optional"></label>
      <button id="save" class="primary" type="button">Confirm bill</button>
      <p id="status" role="status"></p>
    </section>
  </section>
</main>
<script>
(() => {
  const $ = selector => document.querySelector(selector);
  const state = {pin:'',products:[],customers:[],settings:{},cart:[],customer:'',method:'Cash',part:false,qrUrl:'',qrRequest:0,scanStream:null,scanFrame:0,scanner:null,scanning:false};
  const esc = value => String(value ?? '').replace(/[&<>"']/g, ch => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[ch]));
  const money = value => `${state.settings.currency || '₹'}${Number(value || 0).toLocaleString('en-IN',{minimumFractionDigits:2,maximumFractionDigits:2})}`;
  async function request(path, options={}) {
    const headers = {};
    if (options.body !== undefined) headers['Content-Type'] = 'application/json';
    if (state.pin) headers['X-Mobile-Pin'] = state.pin;
    const response = await fetch(`/api/mobile${path}`, {
      method: options.method || 'GET', headers,
      body: options.body === undefined ? undefined : JSON.stringify(options.body)
    });
    const contentType = response.headers.get('Content-Type') || '';
    if (!response.ok) {
      const detail = contentType.includes('application/json') ? await response.json() : {};
      if (response.status === 401 && state.pin) logout(detail.error || 'Mobile session expired. Sign in again.');
      throw new Error(detail.error || 'Request failed.');
    }
    return contentType.includes('image/') ? response.blob() : response.json();
  }
  function message(text, error=false) { $('#status').textContent = text; $('#status').className = error ? 'error' : 'muted'; }
  function logout(text='') {
    stopScanner();
    state.qrRequest += 1;
    if (state.qrUrl) URL.revokeObjectURL(state.qrUrl);
    state.qrUrl = ''; state.pin = ''; $('#pin').value = '';
    $('#app').hidden = true; $('#login').hidden = false; $('#login-error').textContent = text;
  }
  function total() {
    const raw = state.cart.reduce((sum, item) => {
      const gross = Math.round(item.qty * item.price * 100) / 100;
      const taxable = gross;
      const tax = Math.round(taxable * item.tax_rate) / 100;
      return sum + taxable + tax;
    }, 0);
    const cents = Math.round(raw * 100) / 100;
    return state.settings.round_off ? Math.round(cents) : cents;
  }
  function paidNow() {
    if (state.method === 'Credit') return 0;
    if (state.part) return Math.round(Number($('#part-amount').value || 0) * 100) / 100;
    return total();
  }
  function renderProducts() {
    const query = $('#search').value.trim().toLowerCase();
    const rows = state.products.filter(item => !query || `${item.name} ${item.sku} ${item.category}`.toLowerCase().includes(query)).slice(0, 60);
    $('#products').innerHTML = rows.map(item => `<button type="button" class="product" data-item="${item.id}" ${!state.settings.allow_negative_stock && item.stock <= 0 ? 'disabled' : ''}>
      <b>${esc(item.name)}</b><small>${esc(item.sku)} · ${money(item.price)}</small><small>${Number(item.stock).toLocaleString()} ${esc(item.unit)} in stock</small></button>`).join('') || '<p class="muted">No matching items.</p>';
  }
  async function renderQr() {
    const wrap = $('#qr-wrap');
    const amount = state.part ? paidNow() : total();
    const requestId = ++state.qrRequest;
    if (state.method !== 'UPI' || !state.settings.upi_id || amount <= 0) {
      wrap.hidden = true;
      if (state.qrUrl) URL.revokeObjectURL(state.qrUrl);
      state.qrUrl = '';
      return;
    }
    try {
      const blob = await request(`/upi-qr?amount=${encodeURIComponent(amount.toFixed(2))}`);
      if (requestId !== state.qrRequest) return;
      if (state.qrUrl) URL.revokeObjectURL(state.qrUrl);
      state.qrUrl = URL.createObjectURL(blob); $('#qr').src = state.qrUrl;
      $('#qr-label').textContent = `Scan to pay ${money(amount)} to ${state.settings.upi_id}`;
      wrap.hidden = false;
    } catch (error) { message(error.message, true); }
  }
  function renderCart() {
    $('#cart').innerHTML = state.cart.length ? state.cart.map((item,index) => `<div class="line">
      <div><b>${esc(item.name)}</b><br><small>${money(item.price)} each</small></div>
      <div class="steps"><button type="button" data-qty="minus" data-index="${index}" aria-label="Decrease ${esc(item.name)}">−</button>
      <b>${item.qty}</b><button type="button" data-qty="plus" data-index="${index}" aria-label="Increase ${esc(item.name)}">+</button></div>
      </div>`).join('') : '<p class="muted">Add an item to start a bill.</p>';
    $('#total').textContent = money(total());
    $('#part-toggle').hidden = state.method === 'Credit';
    $('#part-toggle').classList.toggle('on', state.part);
    $('#part-toggle').textContent = state.part ? 'Part payment on' : 'Record part payment';
    $('#part-amount-wrap').hidden = !state.part;
    $('#customer').required = false;
    $('#credit-note').hidden = state.method !== 'Credit' && !state.part;
    $('#credit-note').textContent = state.method === 'Credit'
      ? "The full bill amount will be added to this customer's pending balance."
      : 'The unpaid balance will be added to this customer.';
    $('#save').textContent = state.part && state.method !== 'Credit'
      ? `Confirm bill (${money(paidNow())} received)` : `Confirm bill for ${money(total())}`;
    document.querySelectorAll('[data-pay]').forEach(button => button.classList.toggle('on', button.dataset.pay === state.method));
    renderQr();
  }
  function addItem(item) {
    const line = state.cart.find(row => row.id === item.id);
    if (line) line.qty += 1;
    else state.cart.push({id:item.id,product_id:item.id,name:item.name,sku:item.sku,unit:item.unit,qty:1,price:item.price,tax_rate:item.tax_rate,stock:item.stock});
    $('#search').value = ''; renderProducts(); renderCart(); message('');
    $('#search').focus();
  }
  function stopScanner() {
    state.scanning = false;
    if (state.scanFrame) cancelAnimationFrame(state.scanFrame);
    state.scanFrame = 0;
    if (state.scanStream) state.scanStream.getTracks().forEach(track => track.stop());
    state.scanStream = null;
    $('#scanner').srcObject = null;
    $('#scanner').hidden = true;
    $('#scan-toggle').textContent = 'Scan barcode / QR code';
  }
  async function scanFrame() {
    if (!state.scanning) return;
    const video = $('#scanner');
    if (video.readyState >= HTMLMediaElement.HAVE_CURRENT_DATA) {
      try {
        const codes = await state.scanner.detect(video);
        const value = codes.find(code => code.rawValue)?.rawValue.trim();
        if (value) {
          const matches = state.products.filter(item => item.active && item.sku.trim().toLowerCase() === value.toLowerCase());
          if (matches.length === 1) {
            stopScanner();
            addItem(matches[0]);
            return;
          }
          $('#scan-help').textContent = matches.length
            ? 'This code matches multiple items; update the SKUs so each item is unique.'
            : `No item found for code "${value}". Item codes must contain the exact SKU.`;
          $('#scan-help').className = 'error';
        }
      } catch (error) {
        stopScanner();
        message(`Could not scan the camera image: ${error.message}`, true);
        return;
      }
    }
    if (state.scanning) state.scanFrame = requestAnimationFrame(scanFrame);
  }
  async function startScanner() {
    if (!window.isSecureContext) {
      $('#scan-help').textContent = 'Camera scanning needs HTTPS. Restart StockBill with --tls-cert and --tls-key, then open its HTTPS address on your phone.';
      $('#scan-help').className = 'error';
      return;
    }
    if (!navigator.mediaDevices?.getUserMedia || !('BarcodeDetector' in window)) {
      $('#scan-help').textContent = 'This browser does not support camera barcode scanning. Use a supported browser or enter the SKU/barcode above.';
      $('#scan-help').className = 'error';
      return;
    }
    try {
      const supported = await BarcodeDetector.getSupportedFormats();
      const formats = ['qr_code','ean_13','ean_8','upc_a','upc_e','code_128','code_39','itf','codabar']
        .filter(format => supported.includes(format));
      if (!formats.length) throw new Error('No supported QR or barcode formats are available.');
      state.scanner = new BarcodeDetector({formats});
      state.scanStream = await navigator.mediaDevices.getUserMedia({video:{facingMode:{ideal:'environment'}},audio:false});
      const video = $('#scanner');
      video.srcObject = state.scanStream;
      video.hidden = false;
      await video.play();
      state.scanning = true;
      $('#scan-help').textContent = 'Point the rear camera at an item QR code or barcode containing its SKU.';
      $('#scan-help').className = 'muted';
      $('#scan-toggle').textContent = 'Stop scanning';
      state.scanFrame = requestAnimationFrame(scanFrame);
    } catch (error) {
      stopScanner();
      $('#scan-help').textContent = error.name === 'NotAllowedError'
        ? 'Camera access was denied. Allow camera access in your browser settings and try again.'
        : `Could not start the camera scanner: ${error.message}`;
      $('#scan-help').className = 'error';
    }
  }
  async function load() {
    const [settings,products,customers] = await Promise.all([request('/settings'),request('/products'),request('/customers')]);
    state.settings = settings; state.products = products; state.customers = customers;
    $('#shop-name').textContent = settings.business_name || 'StockBill';
    $('#customer').innerHTML = '<option value="">Walk-in customer (no saved customer)</option>' + customers.map(customer =>
      `<option value="${customer.id}">${esc(customer.name)}${customer.phone ? ` (${esc(customer.phone)})` : ''}</option>`).join('');
    $('#customer').value = state.customer;
    $('#app').hidden = false; $('#login').hidden = true;
    renderProducts(); renderCart();
  }
  $('#login-form').addEventListener('submit', async event => {
    event.preventDefault();
    $('#login-error').textContent = '';
    try {
      const response = await fetch('/api/mobile/login',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({pin:$('#pin').value})});
      const data = await response.json().catch(() => ({}));
      if (!response.ok) throw new Error(data.error || 'Sign-in failed.');
      state.pin = $('#pin').value; await load();
    } catch (error) { state.pin = ''; $('#login-error').textContent = error.message; }
  });
  $('#search').addEventListener('input', renderProducts);
  $('#scan-toggle').addEventListener('click', () => {
    if (state.scanning) stopScanner();
    else startScanner();
  });
  $('#search').addEventListener('keydown', event => {
    if (event.key !== 'Enter') return;
    event.preventDefault();
    const query = event.currentTarget.value.trim().toLowerCase();
    const matches = state.products.filter(item => item.active && item.sku.toLowerCase() === query);
    if (matches.length === 1) addItem(matches[0]);
    else message(matches.length ? 'Several items match; select the correct item.' : 'No exact SKU/barcode found.', true);
  });
  $('#products').addEventListener('click', event => {
    const button = event.target.closest('[data-item]');
    const item = state.products.find(row => row.id === Number(button && button.dataset.item));
    if (item) addItem(item);
  });
  $('#cart').addEventListener('click', event => {
    const button = event.target.closest('[data-qty]');
    if (!button) return;
    const item = state.cart[Number(button.dataset.index)];
    if (!item) return;
    if (button.dataset.qty === 'plus') {
      if (!state.settings.allow_negative_stock && item.qty >= item.stock) return message(`Only ${item.stock} ${item.unit} of ${item.name} in stock.`, true);
      item.qty += 1;
    } else if (--item.qty <= 0) state.cart.splice(Number(button.dataset.index),1);
    renderCart();
  });
  document.querySelectorAll('[data-pay]').forEach(button => button.addEventListener('click', () => {
    state.method = button.dataset.pay;
    if (state.method === 'Credit') state.part = false;
    renderCart();
  }));
  $('#part-toggle').addEventListener('click', () => {
    state.part = !state.part;
    if (state.part) $('#part-amount').value = total().toFixed(2);
    renderCart();
  });
  $('#part-amount').addEventListener('input', () => {
    $('#save').textContent = `Confirm bill (${money(paidNow())} received)`;
    renderQr();
  });
  $('#customer').addEventListener('change', event => { state.customer = event.target.value; });
  $('#logout').addEventListener('click', () => logout());
  $('#save').addEventListener('click', async event => {
    if (!state.cart.length) return message('Add at least one item.', true);
    const customer = state.customers.find(row => String(row.id) === String(state.customer));
    if (state.method === 'Credit' && !customer) {
      $('#customer').focus(); return message('Select a saved customer for a credit transaction.', true);
    }
    if (customer && !customer.phone) {
      $('#customer').focus(); return message('Add a phone number to the selected customer before billing.', true);
    }
    if (state.part && !(paidNow() > 0 && paidNow() <= total())) return message('Enter an amount above zero and no more than the bill total.', true);
    const button = event.currentTarget; button.disabled = true;
    try {
      const amount = total();
      const invoice = await request('/invoices',{method:'POST',body:{
        customer_id:state.customer || null, paid:state.method === 'Credit' ? 0 : paidNow(),
        payment_method:state.method, notes:$('#note').value,
        items:state.cart.map(item => ({product_id:item.product_id,qty:item.qty}))
      }});
      state.cart = []; state.customer = ''; state.part = false; $('#part-amount').value = ''; $('#note').value = ''; $('#customer').value = '';
      await load(); message(`Saved ${invoice.number} for ${money(invoice.grand_total)}.`);
    } catch (error) { message(error.message, true); }
    finally { button.disabled = false; }
  });
  fetch('/api/mobile/login').then(response => response.json()).then(info => {
    if (!info.pin_enabled) {
      $('#login-help').textContent = 'Mobile billing is disabled. Set a separate mobile PIN in the main app Settings.';
      $('#login-form').hidden = true;
    } else $('#pin').focus();
  }).catch(() => { $('#login-error').textContent = "Can't reach StockBill. Check the server and Wi-Fi connection."; });
})();
</script></body></html>"""

if __name__ == "__main__":
    main()
