# -*- coding: utf-8 -*-
"""
Telegram-бот Legend Mine: персонал сервера + сайт-панель.

Команды бота:
  /staff       - список персонала (кто в игре, должности, предупреждения)
  /staff web   - одноразовая ссылка для входа на сайт

Сайт-панель: просмотр персонала, добавление, снятие, предупреждения.
Войти на сайт можно только по ссылке из Telegram (/staff web).

Переменные окружения:
  TELEGRAM_TOKEN           - токен бота от @BotFather
  OWNER_TG_IDS             - Telegram-ID владельцев через запятую
  SPREADSHEET_ID           - ID Google Таблицы проекта
  GOOGLE_CREDENTIALS_JSON  - JSON сервисного аккаунта
  WEB_URL                  - адрес сайта (https://legendmine.onrender.com)
  RCON_HOST, RCON_PORT, RCON_PASSWORD - RCON
  PTERO_URL, PTERO_API_KEY, PTERO_SERVER_ID - Pterodactyl API
"""

import asyncio
import base64
import hashlib
import hmac
import html
import json
import os
import random
import re
import secrets
import socket
import struct
import sys
import threading
import time
import urllib.error
import urllib.request
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Optional
from urllib.parse import parse_qs, urlparse

import gspread
from google.oauth2.service_account import Credentials
from telegram import LinkPreviewOptions, Update
from telegram.constants import ParseMode
from telegram.ext import Application, CommandHandler, ContextTypes

NO_PREVIEW = LinkPreviewOptions(is_disabled=True)

# ============================================================
# НАСТРОЙКИ
# ============================================================
PROJECT_NAME = os.getenv("PROJECT_NAME", "Legend Mine")
TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN", "")


def _ids(name: str) -> set:
    out = set()
    for x in os.getenv(name, "").replace(" ", "").split(","):
        if x.lstrip("-").isdigit():
            out.add(int(x))
    return out


def _int(name: str, default: int = 0) -> int:
    v = os.getenv(name, "")
    return int(v) if v.lstrip("-").isdigit() else default


OWNER_TG_IDS = _ids("OWNER_TG_IDS")
ADMIN_TG_IDS = _ids("ADMIN_TG_IDS")
ALLOWED_CHAT_IDS = _ids("ALLOWED_CHAT_IDS")

RCON_HOST = os.getenv("RCON_HOST", "")
RCON_PORT = _int("RCON_PORT", 25575)
RCON_PASSWORD = os.getenv("RCON_PASSWORD", "")
QUERY_HOST = os.getenv("QUERY_HOST", RCON_HOST)
QUERY_PORT = _int("QUERY_PORT", 25565)

PTERO_URL = os.getenv("PTERO_URL", "")
PTERO_API_KEY = os.getenv("PTERO_API_KEY", "")
PTERO_SERVER_ID = os.getenv("PTERO_SERVER_ID", "")

SPREADSHEET_ID = os.getenv("SPREADSHEET_ID", "")
WORKSHEET_NAME = "Учет предупреждений"
STAFF_SHEET_NAME = os.getenv("STAFF_SHEET_NAME", "Списки")
CREDENTIALS_FILE = "credentials.json"

HEALTH_PORT = _int("PORT", 8080)
WEB_URL = os.getenv("WEB_URL", "https://legendmine.onrender.com") or os.getenv("RENDER_EXTERNAL_URL", "")
WEB_SESSION_HOURS = _int("WEB_SESSION_HOURS", 12)
WEB_LINK_MINUTES = _int("WEB_LINK_MINUTES", 15)
WEB_ADMINS = {
    x.strip().lstrip("@").lower()
    for x in os.getenv("WEB_ADMINS", "HumanLegendary,borekkst").split(",")
    if x.strip()
}
WEB_ADMIN_IDS = _ids("WEB_ADMIN_IDS")

WARNS_FOR_DEMOTION = _int("WARNS_FOR_DEMOTION", 4)
PROTECTED_FROM_DEMOTION = {"Владелец проекта", "Со-Владелец"}

# ============================================================
# ШТАТ
# ============================================================
ROLE_TO_GROUP = {
    "Владелец проекта": "owner",
    "Со-Владелец": "coowner",
    "Куратор": "curator",
    "Ст.Админстратор": "stadmin",
    "Администратор": "admin",
    "Ст.Модератор": "stmoder",
    "Модератор": "moderator",
    "Хелпер": "helper",
}

try:
    ROLE_TO_GROUP.update(json.loads(os.getenv("ROLE_GROUPS_JSON", "{}") or "{}"))
except ValueError:
    print("[config] ROLE_GROUPS_JSON не является корректным JSON, использую группы по умолчанию")

ROLE_LIST = list(ROLE_TO_GROUP.keys())
STAFF_ROLES = {role: {"users": []} for role in ROLE_LIST}
state = {"app": None, "loop": None}


def find_staff_role(nick: str):
    low = nick.lower()
    for role, data in STAFF_ROLES.items():
        if any(u.lower() == low for u in data["users"]):
            return role
    return None


def canon_nick(low: str) -> str:
    for d in STAFF_ROLES.values():
        for u in d["users"]:
            if u.lower() == low:
                return u
    return low


def valid_nick(nick: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z0-9_.\-]{2,32}", nick))


def h(text) -> str:
    return html.escape(str(text), quote=False)


def chunk_text(lines, limit=3800):
    chunks, cur = [], ""
    for line in lines:
        if len(cur) + len(line) + 1 > limit:
            chunks.append(cur)
            cur = ""
        cur += line + "\n"
    if cur:
        chunks.append(cur)
    return chunks


# ============================================================
# СВЯЗЬ С СЕРВЕРОМ: RCON, Query, API панели
# ============================================================
class RconError(Exception):
    pass


def _recv_exact(sock: socket.socket, n: int) -> bytes:
    buf = b""
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            raise RconError("Соединение закрыто сервером")
        buf += chunk
    return buf


def _send_packet(sock: socket.socket, req_id: int, ptype: int, body: str):
    payload = struct.pack("<ii", req_id, ptype) + body.encode("utf-8") + b"\x00\x00"
    sock.sendall(struct.pack("<i", len(payload)) + payload)


def _read_packet(sock: socket.socket):
    length = struct.unpack("<i", _recv_exact(sock, 4))[0]
    data = _recv_exact(sock, length)
    req_id, ptype = struct.unpack("<ii", data[:8])
    return req_id, ptype, data[8:-2].decode("utf-8", errors="replace")


def _rcon_sync(command: str) -> str:
    if not RCON_HOST or not RCON_PASSWORD:
        raise RconError("сервер пока не подключен")
    try:
        with socket.create_connection((RCON_HOST, RCON_PORT), timeout=8) as sock:
            sock.settimeout(8)
            _send_packet(sock, 1, 3, RCON_PASSWORD)
            req_id, _, _ = _read_packet(sock)
            if req_id == -1:
                raise RconError("Неверный пароль RCON")
            _send_packet(sock, 2, 2, command)
            _, _, body = _read_packet(sock)
            return body
    except RconError:
        raise
    except (OSError, struct.error) as e:
        raise RconError(f"Нет соединения с сервером: {e}")


COLOR_CODES = re.compile(r"§.")


async def rcon(command: str) -> str:
    return COLOR_CODES.sub("", await asyncio.to_thread(_rcon_sync, command)).strip()


def parse_online_names(list_response: str):
    if ":" not in list_response:
        return []
    return [n.strip() for n in list_response.split(":", 1)[1].split(",") if n.strip()]


def _query_sync():
    if not QUERY_HOST:
        raise RuntimeError("Query не настроен (QUERY_HOST)")
    sid = random.randint(1, 0x7FFFFFFF) & 0x0F0F0F0F
    addr = (QUERY_HOST, QUERY_PORT)
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
        sock.settimeout(5)
        sock.sendto(b"\xfe\xfd\x09" + struct.pack(">i", sid), addr)
        data, _ = sock.recvfrom(2048)
        token = int(data[5:].split(b"\x00", 1)[0])
        sock.sendto(b"\xfe\xfd\x00" + struct.pack(">ii", sid, token) + b"\x00\x00\x00\x00", addr)
        data, _ = sock.recvfrom(16384)
    body = data[5:]
    marker = b"\x01player_\x00\x00"
    idx = body.find(marker)
    if idx == -1:
        raise RuntimeError("неожиданный ответ Query")
    return [p.decode("utf-8", errors="replace") for p in body[idx + len(marker):].split(b"\x00") if p]


async def fetch_online():
    try:
        return parse_online_names(await rcon("list")), "rcon"
    except RconError:
        pass
    try:
        return await asyncio.to_thread(_query_sync), "query"
    except Exception:
        return None, None


def panel_configured() -> bool:
    return bool(PTERO_URL and PTERO_API_KEY and PTERO_SERVER_ID)


def _ptero_sync(command: str):
    url = f"{PTERO_URL.rstrip('/')}/api/client/servers/{PTERO_SERVER_ID}/command"
    req = urllib.request.Request(
        url,
        data=json.dumps({"command": command}).encode("utf-8"),
        method="POST",
        headers={
            "Authorization": f"Bearer {PTERO_API_KEY}",
            "Content-Type": "application/json",
            "Accept": "Application/vnd.pterodactyl.v1+json",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            resp.read()
    except urllib.error.HTTPError as e:
        raise RconError(f"панель хостинга вернула ошибку {e.code}")
    except OSError as e:
        raise RconError(f"панель хостинга недоступна: {e}")


async def run_command(command: str):
    try:
        return await rcon(command), "rcon"
    except RconError as e:
        rcon_err = e
    if panel_configured():
        await asyncio.to_thread(_ptero_sync, command)
        return "", "panel"
    raise rcon_err


LP_ERROR_MARKERS = (
    "does not exist", "could not be found", "unknown command", "no such",
    "not found", "unable to", "не существует", "не найден",
)


def lp_failed(resp: str) -> bool:
    low = resp.lower()
    return any(m in low for m in LP_ERROR_MARKERS)


def _self_ping_sync():
    url = os.getenv("RENDER_EXTERNAL_URL") or os.getenv("SELF_PING_URL")
    if not url:
        return
    try:
        with urllib.request.urlopen(url, timeout=15) as resp:
            resp.read(16)
    except Exception as e:
        print(f"[selfping] {e}")


# ============================================================
# GOOGLE ТАБЛИЦЫ
# ============================================================
SCOPES = [
    "https://www.googleapis.com/auth/spreadsheets",
    "https://www.googleapis.com/auth/drive",
]
HEADER = ["Дата", "Ник", "Должность", "Причина", "Выдал", "Номер предупреждения"]
STAFF_HEADER = [
    "Игровой никнейм", "Должность", "Discord", "Telegram / VK", "Дополнительные коментарии", "",
    "Количество приведенных игроков", "Кол-во отыгранных часов", "Предупреждения",
]
WARN_COLUMN = "I"

_spreadsheet = None
_sheets = {}


def _get_credentials() -> Credentials:
    env_json = os.getenv("GOOGLE_CREDENTIALS_JSON")
    if env_json:
        return Credentials.from_service_account_info(json.loads(env_json), scopes=SCOPES)
    if os.path.exists(CREDENTIALS_FILE):
        return Credentials.from_service_account_file(CREDENTIALS_FILE, scopes=SCOPES)
    raise RuntimeError("Не найдены данные Google: задайте GOOGLE_CREDENTIALS_JSON или положите credentials.json")


def _get_spreadsheet():
    global _spreadsheet
    if not SPREADSHEET_ID:
        raise RuntimeError("Не задан SPREADSHEET_ID")
    if _spreadsheet is None:
        _spreadsheet = gspread.authorize(_get_credentials()).open_by_key(SPREADSHEET_ID)
    return _spreadsheet


def _get_sheet(name: str, header):
    if name in _sheets:
        return _sheets[name]
    sh = _get_spreadsheet()
    try:
        ws = sh.worksheet(name)
    except gspread.WorksheetNotFound:
        ws = sh.add_worksheet(title=name, rows=1000, cols=max(len(header), 6))
        ws.append_row(header)
    _sheets[name] = ws
    return ws


def _reset_sheets():
    global _spreadsheet
    _spreadsheet = None
    _sheets.clear()


async def sheets_run(func, *args, retry: bool = True):
    try:
        return await asyncio.to_thread(func, *args)
    except Exception:
        _reset_sheets()
        if not retry:
            raise
        return await asyncio.to_thread(func, *args)


def _add_warn_sync(nick: str, role: str, reason: str, issuer: str) -> int:
    ws = _get_sheet(WORKSHEET_NAME, HEADER)
    rows = ws.get_all_values()
    count = sum(1 for r in rows[1:] if len(r) > 1 and r[1].lower() == nick.lower()) + 1
    ws.append_row([time.strftime("%d.%m.%Y %H:%M", time.gmtime(time.time() + 3 * 3600)), nick, role, reason, issuer, count])
    return count


async def add_warn(nick: str, role: str, reason: str, issuer: str) -> int:
    return await sheets_run(_add_warn_sync, nick, role, reason, issuer, retry=False)


def _warn_counts_sync():
    ws = _get_sheet(WORKSHEET_NAME, HEADER)
    counts = {}
    for r in ws.get_all_values()[1:]:
        if len(r) > 1 and r[1].strip():
            key = r[1].strip().lower()
            counts[key] = counts.get(key, 0) + 1
    return counts


SECTION_OF = {
    "Владелец проекта": "Владельцы", "Со-Владелец": "Владельцы",
    "Куратор": "Кураторы", "Ст.Админстратор": "Администраторы",
    "Администратор": "Администраторы", "Ст.Модератор": "Модераторы",
    "Модератор": "Модераторы", "Хелпер": "Хелперы",
}
SECTION_LOWER = {s.lower(): s for s in SECTION_OF.values()}
SECTION_DEFAULT_ROLE = {
    "Владельцы": "Владелец проекта", "Кураторы": "Куратор",
    "Администраторы": "Администратор", "Модераторы": "Модератор",
    "Хелперы": "Хелпер",
}


def _norm(s: str) -> str:
    return re.sub(r"[\s.]+", " ", str(s).strip().lower()).strip()


ROLE_ALIASES = {_norm(r): r for r in ROLE_LIST}
ROLE_ALIASES.update({
    "владелец": "Владелец проекта",
    "совладелец": "Со-Владелец",
    "со владелец": "Со-Владелец",
    "ст админстратор": "Ст.Админстратор",
    "старший администратор": "Ст.Админстратор",
    "админ": "Администратор",
    "ст модератор": "Ст.Модератор",
    "старший модератор": "Ст.Модератор",
    "модер": "Модератор",
})
STAFF_META = {}
_staff_lock = threading.Lock()


def parse_role(text: str, section: Optional[str]) -> Optional[str]:
    return ROLE_ALIASES.get(_norm(text)) or SECTION_DEFAULT_ROLE.get(section or "")


def _section_of_row(row) -> Optional[str]:
    cells = [c.strip() for c in row if c and c.strip()]
    if len(cells) == 1 and cells[0].lower() in SECTION_LOWER:
        return SECTION_LOWER[cells[0].lower()]
    return None


def _pad(row, n=9):
    row = list(row) + [""] * (n - len(row))
    return [str(c).strip() for c in row[:n]]


def _load_staff_sync():
    return _get_sheet(STAFF_SHEET_NAME, STAFF_HEADER).get_all_values()


def _layout(rows):
    info, cur = {}, None
    for i, r in enumerate(rows, start=1):
        if i == 1:
            continue
        sec = _section_of_row(r)
        if sec:
            cur = sec
            info[sec] = {"header": i, "last_data": None, "blank_after_header": False}
            continue
        if cur is None:
            continue
        if (r[0] if r else "").strip():
            info[cur]["last_data"] = i
        elif not any(c.strip() for c in r) and i == info[cur]["header"] + 1:
            info[cur]["blank_after_header"] = True
    return info


def _find_row(rows, nick: str):
    cur = None
    for i, r in enumerate(rows, start=1):
        if i == 1:
            continue
        sec = _section_of_row(r)
        if sec:
            cur = sec
            continue
        if (r[0] if r else "").strip().lower() == nick.lower():
            return i, _pad(r), cur
    return None


def _insert_staff_row(ws, role: str, values):
    rows = ws.get_all_values()
    sec = SECTION_OF[role]
    info = _layout(rows).get(sec)
    if info is None:
        ws.append_rows([[sec], values], value_input_option="RAW")
    elif info["last_data"]:
        ws.insert_rows([values], row=info["last_data"] + 1, value_input_option="RAW", inherit_from_before=True)
    elif info["blank_after_header"]:
        ws.update(values=[values], range_name=f"A{info['header'] + 1}:I{info['header'] + 1}", raw=True)
    else:
        ws.insert_rows([values], row=info["header"] + 1, value_input_option="RAW", inherit_from_before=False)


def _sheet_add_staff_sync(nick, role, discord, contact, comment):
    with _staff_lock:
        values = [nick, role, discord, contact, comment, "", 0, 0, 0]
        _insert_staff_row(_get_sheet(STAFF_SHEET_NAME, STAFF_HEADER), role, values)


def _sheet_set_warns_sync(nick, count) -> bool:
    with _staff_lock:
        ws = _get_sheet(STAFF_SHEET_NAME, STAFF_HEADER)
        found = _find_row(ws.get_all_values(), nick)
        if not found:
            return False
        ws.update(values=[[count]], range_name=f"{WARN_COLUMN}{found[0]}", raw=True)
        return True


async def sheet_set_warns(nick: str, count: int) -> bool:
    try:
        return bool(await sheets_run(_sheet_set_warns_sync, nick, count, retry=False))
    except Exception as e:
        print(f"[staff] не удалось обновить колонку предупреждений: {e!r}")
        return False


def _sheet_remove_staff_sync(nick) -> bool:
    with _staff_lock:
        ws = _get_sheet(STAFF_SHEET_NAME, STAFF_HEADER)
        found = _find_row(ws.get_all_values(), nick)
        if not found:
            return False
        ws.delete_rows(found[0])
        return True


def _sheet_change_role_sync(nick, new_role) -> bool:
    with _staff_lock:
        ws = _get_sheet(STAFF_SHEET_NAME, STAFF_HEADER)
        found = _find_row(ws.get_all_values(), nick)
        if not found:
            return False
        i, vals, sec = found
        vals[1] = new_role
        if sec == SECTION_OF[new_role]:
            ws.update(values=[[new_role]], range_name=f"B{i}", raw=True)
        else:
            ws.delete_rows(i)
            _insert_staff_row(ws, new_role, vals)
        return True


async def init_staff():
    try:
        rows = await sheets_run(_load_staff_sync)
    except Exception as e:
        print(f"[staff] не удалось прочитать лист «{STAFF_SHEET_NAME}»: {e!r}")
        return
    for data in STAFF_ROLES.values():
        data["users"] = []
    STAFF_META.clear()
    section = None
    for r in rows[1:]:
        sec = _section_of_row(r)
        if sec:
            section = sec
            continue
        vals = _pad(r)
        nick = vals[0]
        if not nick:
            continue
        if not valid_nick(nick):
            print(f"[staff] пропущена строка с некорректным ником: {r}")
            continue
        role = parse_role(vals[1], section)
        if role is None or find_staff_role(nick):
            print(f"[staff] пропущена строка (неизвестная должность или дубль): {r}")
            continue
        STAFF_ROLES[role]["users"].append(nick)
        STAFF_META[nick.lower()] = {"discord": vals[2], "contact": vals[3], "comment": vals[4]}
    print(f"[staff] загружено сотрудников из «{STAFF_SHEET_NAME}»: {sum(len(d['users']) for d in STAFF_ROLES.values())}")


# ============================================================
# ЛОГИКА ШТАТА
# ============================================================
async def unstaff_logic(nick: str):
    role = find_staff_role(nick)
    if role is None:
        return False, f"❌ <code>{h(nick)}</code> не найден в штате."
    note = ""
    try:
        resp, via = await run_command(f"lp user {nick} parent set default")
        if via == "rcon" and lp_failed(resp):
            note = f"\n⚠️ LuckPerms ответил: {h(resp[:200])}"
        elif via == "panel":
            note = "\nℹ️ Команда отправлена через панель хостинга, результат не проверяется."
    except RconError as e:
        note = (
            f"\n⚠️ Роль на сервере не снята ({h(e)}). "
            f"Снимите вручную в консоли: <code>lp user {h(nick)} parent set default</code>"
        )
    low = nick.lower()
    STAFF_ROLES[role]["users"] = [u for u in STAFF_ROLES[role]["users"] if u.lower() != low]
    STAFF_META.pop(low, None)
    try:
        if not await sheets_run(_sheet_remove_staff_sync, nick, retry=False):
            note += f"\n⚠️ В листе «{h(STAFF_SHEET_NAME)}» строка с этим ником не найдена."
    except Exception as e:
        note += f"\n⚠️ Не удалось удалить строку из листа «{h(STAFF_SHEET_NAME)}»: {h(e)}"
    return True, f"🗑 <code>{h(nick)}</code> снят с должности <b>{h(role)}</b>. Группа на сервере: <code>default</code>.{note}"


async def addstaff_logic(nick: str, role: str, discord: str = "", contact: str = "", comment: str = ""):
    existing = find_staff_role(nick)
    if existing:
        return False, f"❌ <code>{h(nick)}</code> уже в штате: <b>{h(existing)}</b>. Сначала снимите его."
    group = ROLE_TO_GROUP[role]
    manual = None
    resp, via = "", None
    try:
        resp, via = await run_command(f"lp user {nick} parent set {group}")
        if via == "panel":
            manual = "ℹ️ Команда отправлена через панель хостинга, результат не проверяется."
    except RconError as e:
        manual = (
            f"⚠️ Сервер недоступен для команд ({h(e)}), группа не выдана. "
            f"Выдайте вручную в консоли: <code>lp user {h(nick)} parent set {h(group)}</code>"
        )
    if via == "rcon" and lp_failed(resp):
        return False, (
            f"❌ LuckPerms не выдал группу <code>{h(group)}</code> игроку <code>{h(nick)}</code>: {h(resp[:300])}\n"
            f"Проверьте, что игрок хотя бы раз заходил на сервер и что группа существует."
        )
    STAFF_ROLES[role]["users"].append(nick)
    STAFF_META[nick.lower()] = {"discord": discord, "contact": contact, "comment": comment}
    saved = True
    try:
        await sheets_run(_sheet_add_staff_sync, nick, role, discord, contact, comment, retry=False)
    except Exception as e:
        saved = False
        print(f"[staff] не удалось добавить строку в лист «{STAFF_SHEET_NAME}»: {e!r}")
    text = (
        f"✅ <b>Сотрудник добавлен</b>\nНик: <code>{h(nick)}</code>\nДолжность: {h(role)}\n"
        f"Раздел в листе «{h(STAFF_SHEET_NAME)}»: {h(SECTION_OF[role])}\n"
        f"Группа LuckPerms: <code>{h(group)}</code>"
    )
    if discord:
        text += f"\nDiscord: {h(discord)}"
    if contact:
        text += f"\nTelegram / VK: {h(contact)}"
    if manual:
        text += f"\n{manual}"
    if not saved:
        text += f"\n⚠️ Не удалось записать строку в лист «{h(STAFF_SHEET_NAME)}», добавьте вручную."
    return True, text


async def apply_warn_consequences(nick: str, count: int):
    if WARNS_FOR_DEMOTION <= 0 or count <= 0 or count % WARNS_FOR_DEMOTION != 0:
        return None
    role = find_staff_role(nick)
    if role is None or role in PROTECTED_FROM_DEMOTION:
        return None
    idx = ROLE_LIST.index(role)
    nick = canon_nick(nick.lower())

    if idx == len(ROLE_LIST) - 1:
        _, msg = await unstaff_logic(nick)
        return f"🚫 <b>{count} предупреждений</b> у <code>{h(nick)}</code> ({h(role)}): понижать некуда, снят со штата.\n{msg}"

    new_role = ROLE_LIST[idx + 1]
    group = ROLE_TO_GROUP[new_role]
    note = ""
    try:
        resp, via = await run_command(f"lp user {nick} parent set {group}")
        if via == "rcon" and lp_failed(resp):
            note = f"\n⚠️ LuckPerms ответил: {h(resp[:200])}"
        elif via == "panel":
            note = "\nℹ️ Команда отправлена через панель хостинга, результат не проверяется."
    except RconError as e:
        note = f"\n⚠️ Группа на сервере не изменена ({h(e)}). Выдайте вручную: <code>lp user {h(nick)} parent set {h(group)}</code>"

    STAFF_ROLES[role]["users"] = [u for u in STAFF_ROLES[role]["users"] if u.lower() != nick.lower()]
    STAFF_ROLES[new_role]["users"].append(nick)
    try:
        if not await sheets_run(_sheet_change_role_sync, nick, new_role, retry=False):
            note += f"\n⚠️ В листе «{h(STAFF_SHEET_NAME)}» строка с этим ником не найдена, обновите должность вручную."
    except Exception as e:
        note += f"\n⚠️ Не удалось обновить должность в листе «{h(STAFF_SHEET_NAME)}»: {h(e)}"
    return (
        f"⬇️ <b>{count} предупреждений</b> у <code>{h(nick)}</code>: понижен с <b>{h(role)}</b> "
        f"до <b>{h(new_role)}</b> (группа <code>{h(group)}</code>).{note}"
    )


# ============================================================
# САЙТ-ПАНЕЛЬ
# ============================================================
_WEB_SECRET = hashlib.sha256(("legend-web|" + TELEGRAM_TOKEN).encode("utf-8")).digest()
_login_fails = {}
_link_tokens = {}
_link_lock = threading.Lock()


def issue_link_token(who: str) -> str:
    now = time.time()
    with _link_lock:
        for t in [t for t, (exp, _w) in _link_tokens.items() if exp < now]:
            _link_tokens.pop(t, None)
        token = secrets.token_urlsafe(24)
        _link_tokens[token] = (now + WEB_LINK_MINUTES * 60, who)
    return token


def peek_link_token(token: str) -> bool:
    with _link_lock:
        item = _link_tokens.get(token)
    return bool(item and item[0] >= time.time())


def consume_link_token(token: str) -> bool:
    with _link_lock:
        item = _link_tokens.pop(token, None)
    return bool(item and item[0] >= time.time())


def _sign(text: str) -> str:
    return hmac.new(_WEB_SECRET, text.encode("utf-8"), hashlib.sha256).hexdigest()


def make_session() -> str:
    exp = int(time.time()) + WEB_SESSION_HOURS * 3600
    return f"{exp}.{_sign('s' + str(exp))}"


def check_session(value: str) -> Optional[int]:
    try:
        exp_s, sig = value.split(".", 1)
        exp = int(exp_s)
    except (ValueError, AttributeError):
        return None
    if exp < time.time() or not hmac.compare_digest(sig, _sign("s" + exp_s)):
        return None
    return exp


def csrf_for(exp: int) -> str:
    return _sign("c" + str(exp))[:32]


def web_run(coro, timeout: int = 90):
    loop = state.get("loop")
    if loop is None:
        coro.close()
        raise RuntimeError("Бот еще запускается, попробуйте через минуту")
    return asyncio.run_coroutine_threadsafe(coro, loop).result(timeout)


def plain(text: str) -> str:
    return html.unescape(re.sub(r"<[^>]+>", "", text)).strip()


WEB_CSS = """
:root{--bg:#f4f5f7;--card:#fff;--text:#1c1f26;--muted:#6b7280;--line:#e3e6eb;--accent:#2f6fed;--ok:#1a8f4d;--bad:#c93636;--okbg:#e6f6ed;--badbg:#fdeaea}
@media(prefers-color-scheme:dark){:root{--bg:#14161b;--card:#1d2027;--text:#e8eaee;--muted:#98a0ae;--line:#2c313b;--accent:#6d9bff;--ok:#4cc27f;--bad:#ff7b7b;--okbg:#17301f;--badbg:#3a1c1c}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font:15px/1.5 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
.wrap{max-width:960px;margin:0 auto;padding:16px}
header{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin:8px 0 16px}
h1{font-size:22px;margin:0}h2{font-size:16px;margin:0 0 12px}
.chip{display:inline-block;padding:2px 10px;border-radius:99px;font-size:13px;border:1px solid var(--line);background:var(--card);color:var(--muted)}
.chip.on{color:var(--ok);border-color:var(--ok)}.chip.off{color:var(--bad);border-color:var(--bad)}
.grid{display:grid;grid-template-columns:1fr 1fr;gap:12px}@media(max-width:700px){.grid{grid-template-columns:1fr}}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:16px;margin-bottom:12px}
label{display:block;font-size:13px;color:var(--muted);margin:8px 0 4px}
input,select{width:100%;padding:9px 10px;border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--text);font:inherit}
button{padding:9px 14px;border:0;border-radius:8px;background:var(--accent);color:#fff;font:inherit;cursor:pointer;margin-top:12px}
button.ghost{background:transparent;color:var(--muted);border:1px solid var(--line);margin:0}
button.danger{background:var(--bad);margin-top:6px}
.flash{padding:10px 14px;border-radius:10px;margin-bottom:12px;border:1px solid;white-space:pre-line}
.flash.ok{background:var(--okbg);color:var(--ok);border-color:var(--ok)}.flash.err{background:var(--badbg);color:var(--bad);border-color:var(--bad)}
.role{margin:14px 0 6px;font-weight:600}.role small{color:var(--muted);font-weight:400}
.row{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:8px 0;border-top:1px solid var(--line)}
.row .name{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
code{font-family:ui-monospace,Menlo,Consolas,monospace;background:var(--bg);padding:1px 6px;border-radius:6px}
details summary{cursor:pointer;color:var(--muted);font-size:13px;list-style:none}details[open] summary{margin-bottom:4px}
.muted{color:var(--muted)}.login{max-width:360px;margin:12vh auto}
"""


def web_page(title: str, body: str) -> bytes:
    return (
        "<!doctype html><html lang='ru'><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width,initial-scale=1'>"
        f"<title>{h(title)}</title><style>{WEB_CSS}</style></head><body><div class='wrap'>{body}</div></body></html>"
    ).encode("utf-8")


def login_html(msg: str = "") -> bytes:
    err = f"<div class='flash err'>{h(msg)}</div>" if msg else ""
    info = (
        "<p>Доступ к панели закрыт. Войти можно только по одноразовой ссылке из Telegram: "
        "откройте личный чат с ботом и отправьте <code>/staff web</code>.</p>"
        "<p class='muted'>Ссылка выдается только администраторам сайта.</p>"
    )
    return web_page(PROJECT_NAME, f"<div class='login card'><h1>{h(PROJECT_NAME)}</h1><p class='muted'>Панель персонала</p>{err}{info}</div>")


def enter_html(token: str) -> bytes:
    return web_page(
        PROJECT_NAME,
        f"<div class='login card'><h1>{h(PROJECT_NAME)}</h1><p class='muted'>Вход в панель персонала</p>"
        f"<form method='post' action='/enter'><input type='hidden' name='t' value='{h(token)}'>"
        "<button type='submit'>Войти</button></form></div>",
    )


def dashboard_html(exp: int, flash: str, kind: str) -> bytes:
    csrf = csrf_for(exp)
    listed, _src = web_run(fetch_online())
    online_lower = {n.lower() for n in (listed or [])}
    try:
        warns = web_run(sheets_run(_warn_counts_sync))
    except Exception:
        warns = None
    snapshot = {role: list(data["users"]) for role, data in STAFF_ROLES.items()}
    total = sum(len(u) for u in snapshot.values())

    chip = (
        f"<span class='chip on'>🟢 онлайн: {len(listed)}</span>" if listed is not None
        else "<span class='chip off'>🔴 сервер недоступен</span>"
    )
    staff_now = [n for r in snapshot.values() for n in r if n.lower() in online_lower]
    flash_html = f"<div class='flash {'ok' if kind == 'ok' else 'err'}'>{h(flash)}</div>" if flash else ""

    role_opts = "".join(f"<option>{h(r)}</option>" for r in ROLE_LIST)
    nick_opts = "".join(f"<option value='{h(n)}'>" for r in snapshot.values() for n in r)
    hidden = f"<input type='hidden' name='csrf' value='{csrf}'>"

    add_form = (
        f"<div class='card'><h2>Добавить сотрудника</h2><form method='post' action='/add'>{hidden}"
        "<label>Ник в Minecraft</label><input name='nick' required minlength='2' maxlength='32' pattern='[A-Za-z0-9_.\\-]+'>"
        f"<label>Должность</label><select name='role'>{role_opts}</select>"
        "<label>Discord (необязательно)</label><input name='discord' maxlength='64'>"
        "<label>Telegram / VK (необязательно)</label><input name='contact' maxlength='64' placeholder='@username или ID'>"
        "<label>Комментарий (необязательно)</label><input name='comment' maxlength='300'>"
        f"<button type='submit'>Добавить</button></form>"
        f"<p class='muted' style='font-size:13px;margin:10px 0 0'>Строка добавится в лист «{h(STAFF_SHEET_NAME)}», в раздел по должности.</p></div>"
    )
    warn_form = (
        f"<div class='card'><h2>Выдать предупреждение</h2><form method='post' action='/warn'>{hidden}"
        f"<label>Сотрудник</label><input name='nick' list='nicks' required><datalist id='nicks'>{nick_opts}</datalist>"
        "<label>Причина</label><input name='reason' required maxlength='300'>"
        f"<button type='submit'>Выдать</button></form>"
        f"<p class='muted' style='font-size:13px;margin:10px 0 0'>Каждые {WARNS_FOR_DEMOTION} предупреждения: понижение на одну должность.</p></div>"
    )

    rows = []
    for role, users in snapshot.items():
        rows.append(f"<div class='role'>{h(role)} <small>({len(users)})</small></div>")
        if not users:
            rows.append("<div class='row'><span class='muted'>— никого</span></div>")
        for nick in users:
            dot = "🟢" if nick.lower() in online_lower else ("⚫" if listed is not None else "·")
            w = warns.get(nick.lower(), 0) if warns else 0
            wtxt = f"<span class='chip'>⚠️ {w}</span>" if w else ""
            rows.append(
                f"<div class='row'><span class='name'>{dot} <code>{h(nick)}</code> {wtxt}</span>"
                f"<details><summary>Снять</summary><form method='post' action='/remove'>{hidden}"
                f"<input type='hidden' name='nick' value='{h(nick)}'><button class='danger' type='submit'>Подтвердить снятие</button></form></details></div>"
            )
    summary = (
        f"Сейчас в игре из персонала: {', '.join(h(n) for n in staff_now)}" if staff_now
        else ("Сейчас никого из персонала в игре нет" if listed is not None else "")
    )
    staff_card = (
        f"<div class='card'><h2>Персонал ({total})</h2><p class='muted'>{summary}</p>{''.join(rows)}"
        + ("<p class='muted'>Штат пуст, добавьте первого сотрудника.</p>" if total == 0 else "")
        + "</div>"
    )
    body = (
        f"<header><div><h1>{h(PROJECT_NAME)}</h1></div><div>{chip} "
        f"<form method='post' action='/logout' style='display:inline'>{hidden}<button class='ghost' type='submit'>Выйти</button></form></div></header>"
        f"{flash_html}<div class='grid'>{add_form}{warn_form}</div>{staff_card}"
    )
    return web_page(f"{PROJECT_NAME} — персонал", body)


class WebHandler(BaseHTTPRequestHandler):
    server_version = "LegendMine"

    def log_message(self, format, *args):
        return

    def _ip(self) -> str:
        fwd = self.headers.get("X-Forwarded-For", "")
        return fwd.split(",")[0].strip() if fwd else self.client_address[0]

    def _cookies(self):
        c = SimpleCookie()
        try:
            c.load(self.headers.get("Cookie", ""))
        except Exception:
            pass
        return c

    def _exp(self) -> Optional[int]:
        morsel = self._cookies().get("sid")
        return check_session(morsel.value) if morsel else None

    def _secure(self) -> str:
        return "; Secure" if self.headers.get("X-Forwarded-Proto", "") == "https" else ""

    def _send(self, code: int, body: bytes, ctype="text/html; charset=utf-8", cookies=(), location=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        self.send_header(
            "Content-Security-Policy",
            "default-src 'none'; style-src 'unsafe-inline'; form-action 'self'; base-uri 'none'; frame-ancestors 'none'",
        )
        if location:
            self.send_header("Location", location)
        for c in cookies:
            self.send_header("Set-Cookie", c)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def _redirect(self, flash: str = "", kind: str = "ok", extra_cookies=()):
        cookies = list(extra_cookies)
        if flash:
            data = base64.urlsafe_b64encode(json.dumps({"m": flash[:400], "k": kind}).encode("utf-8")).decode()
            cookies.append(f"flash={data}; Max-Age=60; Path=/; HttpOnly; SameSite=Strict{self._secure()}")
        self._send(303, b"", cookies=cookies, location="/")

    def do_HEAD(self):
        self._send(200, b"")

    def do_GET(self):
        path = urlparse(self.path).path
        if path in ("/health", "/healthz"):
            self._send(200, b"OK", ctype="text/plain; charset=utf-8")
            return
        if path == "/enter":
            token = parse_qs(urlparse(self.path).query).get("t", [""])[0]
            if self._too_many_fails():
                self._send(429, login_html("Слишком много попыток. Подождите 15 минут."))
            elif peek_link_token(token):
                self._send(200, enter_html(token))
            else:
                self._note_fail()
                self._send(401, login_html("Ссылка недействительна или уже использована. Получите новую: /staff web в боте."))
            return
        if path != "/":
            self._send(404, web_page("404", "<div class='card'><h1>404</h1></div>"))
            return
        exp = self._exp()
        if exp is None:
            self._send(200, login_html())
            return
        flash, kind, clear = "", "ok", []
        morsel = self._cookies().get("flash")
        if morsel:
            try:
                d = json.loads(base64.urlsafe_b64decode(morsel.value.encode()).decode("utf-8"))
                flash, kind = str(d.get("m", "")), str(d.get("k", "ok"))
            except Exception:
                pass
            clear.append(f"flash=; Max-Age=0; Path=/; HttpOnly; SameSite=Strict{self._secure()}")
        try:
            self._send(200, dashboard_html(exp, flash, kind), cookies=clear)
        except Exception as e:
            print(f"[web] ошибка страницы: {e!r}")
            self._send(500, web_page("Ошибка", f"<div class='card'><h1>Ошибка</h1><p>{h(e)}</p></div>"))

    def do_POST(self):
        path = urlparse(self.path).path
        try:
            length = min(int(self.headers.get("Content-Length", "0") or 0), 10000)
        except ValueError:
            length = 0
        form = {k: v[0] for k, v in parse_qs(self.rfile.read(length).decode("utf-8", "replace")).items()}

        if path == "/enter":
            self._enter(form)
            return
        exp = self._exp()
        if exp is None:
            self._send(303, b"", location="/")
            return
        if not hmac.compare_digest(form.get("csrf", ""), csrf_for(exp)):
            self._redirect("Сессия устарела, повторите действие.", "err")
            return
        try:
            if path == "/logout":
                self._redirect(extra_cookies=[f"sid=; Max-Age=0; Path=/; HttpOnly; SameSite=Strict{self._secure()}"])
            elif path == "/add":
                self._add(form)
            elif path == "/remove":
                self._remove(form)
            elif path == "/warn":
                self._warn(form)
            else:
                self._send(404, web_page("404", "<div class='card'><h1>404</h1></div>"))
        except Exception as e:
            print(f"[web] ошибка действия {path}: {e!r}")
            self._redirect(f"Ошибка: {e}", "err")

    def _too_many_fails(self) -> bool:
        now = time.time()
        fails = [t for t in _login_fails.get(self._ip(), []) if now - t < 900]
        _login_fails[self._ip()] = fails
        return len(fails) >= 10

    def _note_fail(self):
        _login_fails.setdefault(self._ip(), []).append(time.time())

    def _enter(self, form):
        if self._too_many_fails():
            self._send(429, login_html("Слишком много попыток. Подождите 15 минут."))
            return
        if consume_link_token(form.get("t", "")):
            cookie = f"sid={make_session()}; Max-Age={WEB_SESSION_HOURS * 3600}; Path=/; HttpOnly; SameSite=Strict{self._secure()}"
            self._redirect(extra_cookies=[cookie])
            return
        self._note_fail()
        self._send(401, login_html("Ссылка недействительна или уже использована. Получите новую: /staff web в боте."))

    def _add(self, form):
        nick, role = form.get("nick", "").strip(), form.get("role", "")
        def clean(name, limit):
            return " ".join(form.get(name, "").split())[:limit]

        discord, contact, comment = clean("discord", 64), clean("contact", 64), clean("comment", 300)
        if not valid_nick(nick):
            self._redirect("Некорректный ник (латиница, цифры, _ . -).", "err")
        elif role not in ROLE_TO_GROUP:
            self._redirect("Неизвестная должность.", "err")
        else:
            ok, text = web_run(addstaff_logic(nick, role, discord, contact, comment))
            self._redirect(plain(text), "ok" if ok else "err")

    def _remove(self, form):
        nick = form.get("nick", "").strip()
        if not valid_nick(nick):
            self._redirect("Некорректный ник.", "err")
            return
        ok, text = web_run(unstaff_logic(nick))
        self._redirect(plain(text), "ok" if ok else "err")

    def _warn(self, form):
        nick, reason = form.get("nick", "").strip(), form.get("reason", "").strip()[:300]
        role = find_staff_role(nick) if valid_nick(nick) else None
        if role is None:
            self._redirect(f"Сотрудник «{nick}» не найден в штате.", "err")
            return
        if not reason:
            self._redirect("Укажите причину.", "err")
            return
        nick = canon_nick(nick.lower())
        count = web_run(add_warn(nick, role, reason, "Сайт"))
        web_run(sheet_set_warns(nick, count))
        text = f"Предупреждение №{count} выдано: {nick} ({role}). Причина: {reason}"
        consequence = web_run(apply_warn_consequences(nick, count))
        if consequence:
            text += "\n" + plain(consequence)
        self._redirect(text, "ok")


def start_web_server():
    def run():
        try:
            server = ThreadingHTTPServer(("0.0.0.0", HEALTH_PORT), WebHandler)
            print(f"[web] сайт и health-check запущены на порту {HEALTH_PORT}")
            server.serve_forever()
        except Exception as e:
            print(f"[web] ошибка: {e}")

    threading.Thread(target=run, daemon=True).start()


# ============================================================
# TELEGRAM: /staff и /staff web
# ============================================================
def is_admin(uid: int) -> bool:
    return uid in OWNER_TG_IDS or uid in ADMIN_TG_IDS


def is_web_admin(user) -> bool:
    return bool(user) and (user.id in WEB_ADMIN_IDS or (user.username or "").lower() in WEB_ADMINS)


def _contact_key(text: str) -> str:
    return text.strip().rstrip("/").split("/")[-1].lstrip("@").lower()


def is_staff_user(user) -> bool:
    uname = (user.username or "").lower()
    for meta in STAFF_META.values():
        key = _contact_key(meta.get("contact", ""))
        if key and (key == str(user.id) or (uname and key == uname)):
            return True
    return False


def can_view(update: Update) -> bool:
    uid = update.effective_user.id
    chat = update.effective_chat
    return (
        is_admin(uid)
        or is_web_admin(update.effective_user)
        or is_staff_user(update.effective_user)
        or (chat is not None and chat.id in ALLOWED_CHAT_IDS)
    )


async def reply(update: Update, text: str):
    chunks = chunk_text(text.split("\n"))
    for chunk in chunks:
        await update.effective_message.reply_text(chunk, parse_mode=ParseMode.HTML, link_preview_options=NO_PREVIEW)


async def cmd_staff(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user is None or update.effective_message is None:
        return
    uid = update.effective_user.id
    if not can_view(update):
        await reply(update, f"❌ Нет доступа. Ваш Telegram ID: <code>{uid}</code>\nПередайте его владельцу, чтобы добавили в доступ.")
        return
    try:
        if context.args and context.args[0].lower() == "web":
            await staff_web(update)
        else:
            await staff_list(update)
    except Exception as e:
        print(f"[error] staff: {e!r}")
        await update.effective_message.reply_text(f"❌ Ошибка: {e}")


async def staff_web(update: Update):
    user = update.effective_user
    if not is_web_admin(user):
        await reply(update, "❌ Доступ к сайту закрыт. Он есть только у администраторов сайта.")
        return
    if update.effective_chat.type != "private":
        await reply(update, "🔒 Ссылка входа выдается только в личном чате с ботом. Откройте чат с ботом и отправьте <code>/staff web</code>.")
        return
    if not WEB_URL:
        await reply(update, "⚠️ Не задан адрес сайта. Добавьте на Render переменную <code>WEB_URL</code> (адрес вашего сервиса, https://….onrender.com).")
        return
    token = issue_link_token(f"@{user.username}" if user.username else str(user.id))
    url = f"{WEB_URL.rstrip('/')}/enter?t={token}"
    await reply(
        update,
        f"🌐 <b>Сайт {h(PROJECT_NAME)}</b>\nОдноразовая ссылка входа (действует {WEB_LINK_MINUTES} мин., работает один раз):\n{h(url)}\n\n"
        f"Никому её не пересылайте. Ваш Telegram ID: <code>{user.id}</code> "
        f"(можно закрепить доступ за ID через переменную WEB_ADMIN_IDS, юзернейм могут сменить).",
    )


async def staff_list(update: Update):
    listed, _src = await fetch_online()
    names = {n.lower() for n in (listed or [])}
    try:
        warns = await sheets_run(_warn_counts_sync)
    except Exception:
        warns = None
    lines = [f"<b>Персонал {h(PROJECT_NAME)}</b>"]
    if listed is not None:
        staff_now = [canon_nick(n.lower()) for n in listed if find_staff_role(n)]
        lines.append(f"Игроков на сервере: <b>{len(listed)}</b>")
        if staff_now:
            lines.append(
                "🟢 <b>Сейчас в игре из персонала:</b> "
                + ", ".join(f"<code>{h(n)}</code> ({h(find_staff_role(n))})" for n in staff_now)
            )
        else:
            lines.append("⚫ Сейчас никого из персонала в игре нет")
    total = 0
    for role, data in STAFF_ROLES.items():
        lines.append(f"\n<b>{h(role)}</b> ({len(data['users'])})")
        if not data["users"]:
            lines.append("— никого")
            continue
        for nick in data["users"]:
            total += 1
            low = nick.lower()
            parts = []
            if listed is not None:
                parts.append("🟢" if low in names else "⚫")
            parts.append(f"<code>{h(nick)}</code>")
            contact = STAFF_META.get(low, {}).get("contact", "").strip()
            if contact and contact != "-":
                parts.append(h(contact[:40]))
            if warns is not None and warns.get(low):
                parts.append(f"⚠️ {warns[low]}")
            lines.append(" ".join(parts))
    lines.append(f"\nВсего сотрудников: {total} · ⚠️ N = количество предупреждений")
    if total == 0:
        lines.append(f"Список пока пуст. Он берется из листа «{h(STAFF_SHEET_NAME)}». Добавить можно на сайте: /staff web")
    if listed is None:
        lines.append("Онлайн не показан: сервер недоступен")
    if warns is None:
        lines.append("Предупреждения не показаны: таблица недоступна")
    await reply(update, "\n".join(lines))


async def keepalive_loop():
    while True:
        await asyncio.sleep(300)
        try:
            await asyncio.to_thread(_self_ping_sync)
        except Exception:
            pass


async def post_init(app: Application):
    state["app"] = app
    state["loop"] = asyncio.get_running_loop()
    await init_staff()
    app.bot_data["tasks"] = [asyncio.create_task(keepalive_loop())]
    print(f"[bot] {PROJECT_NAME}: бот запущен")


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE):
    print(f"[error] {context.error!r}")


def build_app() -> Application:
    app = Application.builder().token(TELEGRAM_TOKEN).post_init(post_init).build()
    app.add_handler(CommandHandler("staff", cmd_staff))
    app.add_error_handler(on_error)
    return app


# ============================================================
# ЗАПУСК
# ============================================================
if __name__ == "__main__":
    if not TELEGRAM_TOKEN:
        sys.exit("Не задана переменная окружения TELEGRAM_TOKEN")
    start_web_server()
    build_app().run_polling(allowed_updates=["message"], drop_pending_updates=True)
