#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Viraj Watermark — production-ready Telegram watermark bot (single file).

Features
--------
* Watermark images (JPG/JPEG/PNG/WEBP), PDFs and videos (FFmpeg overlay).
* Text and logo watermarks: size, color, opacity, rotation, 9 positions +
  custom coordinates, margins, bold/italic, outline stroke, drop shadow,
  badge box, tiled mode with custom spacing.
* Per-user persistent settings (SQLite) with independent settings per media
  category (Video / Image / PDF) plus per-user Global Defaults — the exact
  UI flow shown in the reference screenshots.
* Batch processing with per-file failure isolation and ZIP delivery.
* Admin panel: stats, system monitoring (psutil), broadcast, block/unblock,
  temp cleanup, configurable limits, recent error log.
* Security: size limits, format validation, filename sanitization, path
  traversal protection, per-user temp isolation, rate limiting, concurrency
  locks, safe subprocess usage (no shell), timeouts, automatic cleanup.

Configuration is read from environment variables (see .env.example):
    BOT_TOKEN, ADMIN_IDS, DATABASE_PATH, MAX_FILE_SIZE, TEMP_DIRECTORY,
    plus optional: FONT_PATH, FFMPEG_PATH, ADMIN_CONTACT_URL, LOG_FILE.

Run:  python viraj_watermark_all_in_one.py
"""

from __future__ import annotations

import asyncio
import html
import io
import json
import logging
import os
import re
import shutil
import subprocess
import sqlite3
import sys
import threading
import time
import unicodedata
import uuid
import zipfile
from collections import deque
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Awaitable, Callable, Dict, List, Optional, Tuple

import psutil

try:  # optional convenience: load .env automatically if present
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:  # pragma: no cover
    pass

from PIL import Image, ImageDraw, ImageFilter, ImageFont

try:
    import fitz  # PyMuPDF
except ImportError:  # pragma: no cover
    fitz = None

from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest, RetryAfter, TelegramError, TimedOut
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# --------------------------------------------------------------------------
# Logging (never logs tokens or file contents)
# --------------------------------------------------------------------------
LOG = logging.getLogger("viraj-watermark")


def _setup_logging() -> None:
    fmt = logging.Formatter("%(asctime)s | %(levelname)-7s | %(message)s")
    stream = logging.StreamHandler(sys.stdout)
    stream.setFormatter(fmt)
    LOG.addHandler(stream)
    log_file = os.getenv("LOG_FILE", "")
    if log_file:
        fh = logging.FileHandler(log_file, encoding="utf-8")
        fh.setFormatter(fmt)
        LOG.addHandler(fh)
    LOG.setLevel(logging.INFO)


# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------
@dataclass
class Config:
    bot_token: str
    admin_ids: List[int]
    database_path: str
    max_file_size: int          # bytes, configured maximum; actual Telegram API limits still apply
    temp_directory: str
    font_path: str
    ffmpeg_path: str
    admin_contact_url: str
    video_timeout: int          # seconds
    process_timeout: int        # seconds for image/pdf
    local_api_base_url: str     # optional self-hosted Bot API base URL
    local_api_file_url: str     # optional self-hosted Bot API file URL
    telegram_api_id: int        # used by the separate local Bot API server
    telegram_api_hash: str      # used by the separate local Bot API server
    upload_limit: int           # output upload limit in bytes

    @staticmethod
    def from_env() -> "Config":
        token = os.getenv("BOT_TOKEN", "8893363579:AAHE6JJnoHRgWSZQASC1ih-GJbsP_TiMH_M").strip()
        if not token:
            raise SystemExit(
                "❌ BOT_TOKEN is not set.\n"
                "1) Create a bot with @BotFather and copy the token.\n"
                "2) Set it in the environment or in a .env file:  BOT_TOKEN=123456:ABC...\n"
                "See .env.example and the README for full instructions."
            )
        admin_raw = os.getenv("ADMIN_IDS", "5823149262").strip()
        admins: List[int] = []
        for part in re.split(r"[,\s;]+", admin_raw):
            if part.isdigit():
                admins.append(int(part))
        max_size = int(os.getenv("MAX_FILE_SIZE", str(5 * 1024 * 1024 * 1024)))
        max_size = max(1024 * 1024, max_size)  # 5 GiB default; transport/API limits still apply
        tmp = os.getenv("TEMP_DIRECTORY", "") or str(Path.cwd() / "wm_temp")
        return Config(
            bot_token=token,
            admin_ids=admins,
            database_path=os.getenv("DATABASE_PATH", "") or str(Path.cwd() / "watermark_bot.db"),
            max_file_size=max_size,
            temp_directory=tmp,
            font_path=os.getenv("FONT_PATH", "").strip(),
            ffmpeg_path=os.getenv("FFMPEG_PATH", "").strip(),
            admin_contact_url=os.getenv("ADMIN_CONTACT_URL", "https://t.me/Viraj2727all").strip(),
            video_timeout=int(os.getenv("VIDEO_TIMEOUT", "900")),
            process_timeout=int(os.getenv("PROCESS_TIMEOUT", "240")),
            local_api_base_url=(os.getenv("TELEGRAM_API_BASE_URL", "http://127.0.0.1:8081/bot" if os.getenv("USE_LOCAL_BOT_API", "0") == "1" else "")).strip().rstrip("/"),
            local_api_file_url=(os.getenv("TELEGRAM_API_FILE_URL", "http://127.0.0.1:8081/file/bot" if os.getenv("USE_LOCAL_BOT_API", "0") == "1" else "")).strip().rstrip("/"),
            telegram_api_id=int(os.getenv("TELEGRAM_API_ID", "36421171")),
            telegram_api_hash=os.getenv("TELEGRAM_API_HASH", "069627fa19eb45a775ce87939f1768c5").strip(),
            upload_limit=max(50 * 1024 * 1024, int(os.getenv("MAX_UPLOAD_SIZE", str(5 * 1024 * 1024 * 1024)))),
        )


CFG: Config = None  # type: ignore[assignment]  # set in main()

START_TIME = time.time()

# --------------------------------------------------------------------------
# Constants / defaults (mirror the reference screenshots)
# --------------------------------------------------------------------------
POSITIONS: Dict[str, Tuple[str, str]] = {
    "top_left": ("Top Left", "↖️"),
    "top_center": ("Top Center", "⬆️"),
    "top_right": ("Top Right", "↗️"),
    "center_left": ("Center Left", "⬅️"),
    "center": ("Center", "🎯"),
    "center_right": ("Center Right", "➡️"),
    "bottom_left": ("Bottom Left", "↙️"),
    "bottom_center": ("Bottom Center", "⬇️"),
    "bottom_right": ("Bottom Right", "↘️"),
    "custom": ("Custom Coords", "🎯"),
}

FONT_FAMILIES = ["Roboto", "Arial", "Serif", "Mono", "Comic"]

BADGES = {"plain": "✨ Plain Text", "box": "🧊 Badge Box", "tile": "🔁 Tiled Pattern"}

DEFAULT_SETTINGS: Dict[str, Any] = {
    "enabled": True,
    "mode": "text",            # text | logo | both
    "text": "@VirajWatermark",
    "font": "Roboto",
    "bold": True,
    "italic": False,
    "font_size": 36,
    "color": "#FFFFFF",
    "opacity": 75,
    "position": "bottom_right",
    "custom_x": 20,
    "custom_y": 20,
    "margin": 20,
    "rotation": 0,
    "tiled": False,
    "tile_spacing": 60,
    "stroke": True,
    "stroke_width": 2,
    "stroke_color": "#000000",
    "shadow": True,
    "badge": "plain",
    "logo_scale": 30,          # % of shortest side
    "logo_opacity": 75,
    "logo_rotation": 0,
    "logo_tiled": False,
    "pdf_pages": "all",
    # Video animation settings
    "animation": "none",
    "animation_speed": 1.0,
}

VIDEO_ANIMATIONS = {
    "none": "⏸️ None", "dvd_bounce": "📀 DVD Bounce", "left_right": "↔️ Left ↔ Right",
    "up_down": "↕️ Up ↕ Down", "diagonal": "↗️ Diagonal", "circle": "⭕ Circle",
    "figure8": "♾️ Figure 8", "shake": "📳 Shake", "pulse": "💓 Pulse",
    "zoom": "🔍 Zoom", "spin": "🌀 Spin", "swing": "🎵 Swing",
    "wave": "🌊 Wave", "zigzag": "⚡ Zigzag", "random": "🎲 Random",
    "bounce": "🏀 Bounce", "corner": "🔲 Corners", "spiral": "🌀 Spiral",
    "horizontal_scan": "📡 Horizontal Scan", "vertical_scan": "📡 Vertical Scan",
    "pendulum": "⏳ Pendulum", "orbit": "🪐 Orbit", "drift": "☁️ Drift",
    "strobe": "✨ Strobe", "elastic": "🪀 Elastic", "float": "🎈 Float",
}


MEDIA_LABELS = {
    "global": ("🌐", "Global Default Settings", "Global Defaults"),
    "image": ("🖼️", "Image Watermark Settings", "Image"),
    "pdf": ("📄", "PDF Watermark Settings", "PDF"),
    "video": ("🎥", "Video Watermark Settings", "Video"),
}

IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".webp"}
PDF_EXTS = {".pdf"}
VIDEO_EXTS = {".mp4", ".mkv", ".mov", ".avi", ".webm", ".m4v"}

SUPPORTED_EXTS = IMAGE_EXTS | PDF_EXTS | VIDEO_EXTS


class WatermarkError(Exception):
    """User-facing processing error."""


# --------------------------------------------------------------------------
# Small utilities
# --------------------------------------------------------------------------
def serif_bold(text: str) -> str:
    """Convert ASCII to Mathematical Bold Serif unicode (matches screenshots)."""
    out = []
    for ch in text:
        o = ord(ch)
        if 65 <= o <= 90:
            out.append(chr(0x1D400 + o - 65))
        elif 97 <= o <= 122:
            out.append(chr(0x1D41A + o - 97))
        elif 48 <= o <= 57:
            out.append(chr(0x1D7CE + o - 48))
        else:
            out.append(ch)
    return "".join(out)


def _dw(s: str) -> int:
    return sum(2 if unicodedata.east_asian_width(c) in ("W", "F") else 1 for c in s)


def _pad(s: str, w: int) -> str:
    return s + " " * max(0, w - _dw(s))


def _trunc(s: str, w: int) -> str:
    return s if _dw(s) <= w else s[: max(0, w - 1)] + "…"


def box_table(headers: List[str], rows: List[List[str]]) -> str:
    """Plain-text table with box-drawing grid lines (rendered inside <pre>)."""
    rows = [[str(c) for c in r] for r in rows]
    widths = [_dw(h) for h in headers]
    for r in rows:
        for i, c in enumerate(r):
            widths[i] = max(widths[i], _dw(c))
    bar = lambda l, m, r: l + m.join("─" * (w + 2) for w in widths) + r
    lines = [bar("┌", "┬", "┐")]
    lines.append("│" + "│".join(f" {_pad(h, w)} " for h, w in zip(headers, widths)) + "│")
    lines.append(bar("├", "┼", "┤"))
    for r in rows:
        lines.append("│" + "│".join(f" {_pad(c, w)} " for c, w in zip(r, widths)) + "│")
    lines.append(bar("└", "┴", "┘"))
    return "\n".join(lines)


def esc(s: Any) -> str:
    return html.escape(str(s))


def sanitize_filename(name: Optional[str]) -> str:
    """Prevent path traversal / weird names; keeps a safe basename."""
    name = (name or "").replace("\\", "/").split("/")[-1]
    name = re.sub(r"[^A-Za-z0-9._-]", "_", name).strip("._")
    name = name[:80] or "file"
    return f"{uuid.uuid4().hex[:8]}_{name}"


def human_size(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.1f} {unit}" if unit != "B" else f"{int(n)} B"
        n /= 1024
    return f"{n:.1f} GB"


def human_duration(sec: float) -> str:
    sec = int(sec)
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f"{h}h {m}m {s}s" if h else f"{m}m {s}s"


def hex_to_rgb(color: str) -> Tuple[int, int, int]:
    c = (color or "#FFFFFF").strip().lstrip("#")
    if len(c) == 3:
        c = "".join(ch * 2 for ch in c)
    if len(c) != 6 or any(ch not in "0123456789abcdefABCDEF" for ch in c):
        raise WatermarkError("Invalid color code. Use hex like #FFFFFF.")
    return int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16)


def parse_page_spec(spec: str, total: int) -> List[int]:
    """'all' or '1,3-5' -> zero based page indices."""
    spec = (spec or "").strip().lower()
    if spec in ("", "all"):
        return list(range(total))
    pages: List[int] = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, _, b = part.partition("-")
            if not a.isdigit() or not b.isdigit():
                raise WatermarkError("Invalid page range. Example: 1,3-5")
            lo, hi = int(a), int(b)
            if lo > hi:
                lo, hi = hi, lo
            pages.extend(range(lo, hi + 1))
        elif part.isdigit():
            pages.append(int(part))
        else:
            raise WatermarkError("Invalid page list. Example: 1,3-5 or 'all'.")
    pages = sorted({p for p in pages if 1 <= p <= total})
    if not pages:
        raise WatermarkError("No valid pages selected.")
    return [p - 1 for p in pages]


# --------------------------------------------------------------------------
# Font discovery
# --------------------------------------------------------------------------
_FONT_CACHE: Dict[str, str] = {}
_FONT_DIRS = [
    "/usr/share/fonts",
    "/usr/local/share/fonts",
    "/System/Library/Fonts",
    os.path.expanduser("~/.fonts"),
    os.path.expanduser("~/.local/share/fonts"),
    "C:/Windows/Fonts",
]


def _scan_fonts() -> None:
    if _FONT_CACHE:
        return
    for root in _FONT_DIRS:
        if not os.path.isdir(root):
            continue
        for base, _dirs, files in os.walk(root):
            for fn in files:
                if fn.lower().endswith((".ttf", ".otf")):
                    _FONT_CACHE.setdefault(fn, os.path.join(base, fn))
                if len(_FONT_CACHE) > 4000:
                    return


_FAMILY_CANDIDATES = {
    "Roboto": ["Roboto-Bold.ttf", "Roboto-Regular.ttf", "DejaVuSans-Bold.ttf", "DejaVuSans.ttf"],
    "Arial": ["Arial Bold.ttf", "Arial-Bold.ttf", "Arial.ttf", "DejaVuSans-Bold.ttf", "DejaVuSans.ttf"],
    "Serif": ["DejaVuSerif-Bold.ttf", "DejaVuSerif.ttf", "FreeSerif.ttf", "Georgia.ttf", "Times New Roman.ttf"],
    "Mono": ["DejaVuSansMono-Bold.ttf", "DejaVuSansMono.ttf", "FreeMono.ttf", "Consolas.ttf"],
    "Comic": ["Comic Sans MS.ttf", "ComicSansMS.ttf", "DejaVuSans.ttf"],
}


def get_font(family: str, bold: bool, size: int) -> ImageFont.FreeTypeFont:
    size = max(8, int(size))
    _scan_fonts()
    if CFG and CFG.font_path and os.path.isfile(CFG.font_path):
        try:
            return ImageFont.truetype(CFG.font_path, size)
        except Exception:
            pass
    cands = list(_FAMILY_CANDIDATES.get(family, _FAMILY_CANDIDATES["Roboto"]))
    if bold:
        cands.sort(key=lambda f: 0 if "bold" in f.lower() else 1)
    else:
        cands.sort(key=lambda f: 1 if "bold" in f.lower() else 0)
    for fn in cands:
        path = _FONT_CACHE.get(fn)
        if path:
            try:
                return ImageFont.truetype(path, size)
            except Exception:
                continue
    # any font as last resort
    for path in list(_FONT_CACHE.values())[:50]:
        try:
            return ImageFont.truetype(path, size)
        except Exception:
            continue
    try:
        return ImageFont.load_default(size)
    except TypeError:  # very old Pillow
        return ImageFont.load_default()


# --------------------------------------------------------------------------
# SQLite persistence
# --------------------------------------------------------------------------
class Database:
    def __init__(self, path: str):
        self.path = path
        self._lock = threading.Lock()
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        self._conn = sqlite3.connect(path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._init_schema()

    def _init_schema(self) -> None:
        with self._lock, self._conn:
            self._conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS users (
                    id INTEGER PRIMARY KEY,
                    username TEXT,
                    first_name TEXT,
                    is_blocked INTEGER DEFAULT 0,
                    created_at TEXT,
                    last_activity TEXT
                );
                CREATE TABLE IF NOT EXISTS settings (
                    user_id INTEGER,
                    media TEXT,
                    data TEXT,
                    updated_at TEXT,
                    PRIMARY KEY (user_id, media)
                );
                CREATE TABLE IF NOT EXISTS stats (
                    user_id INTEGER PRIMARY KEY,
                    images INTEGER DEFAULT 0,
                    pdfs INTEGER DEFAULT 0,
                    videos INTEGER DEFAULT 0,
                    batches INTEGER DEFAULT 0,
                    errors INTEGER DEFAULT 0,
                    last_processed TEXT
                );
                CREATE TABLE IF NOT EXISTS kv (
                    key TEXT PRIMARY KEY,
                    value TEXT
                );
                CREATE TABLE IF NOT EXISTS error_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts TEXT,
                    user_id INTEGER,
                    context TEXT,
                    message TEXT
                );
                """
            )

    def q(self, sql: str, params: Tuple = ()) -> List[sqlite3.Row]:
        with self._lock, self._conn:
            cur = self._conn.execute(sql, params)
            return cur.fetchall()

    # -- users -------------------------------------------------------------
    def touch_user(self, uid: int, username: str, first_name: str) -> None:
        now = datetime.now(timezone.utc).isoformat()
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT INTO users(id, username, first_name, created_at, last_activity) "
                "VALUES(?,?,?,?,?) ON CONFLICT(id) DO UPDATE SET username=excluded.username, "
                "first_name=excluded.first_name, last_activity=excluded.last_activity",
                (uid, username, first_name, now, now),
            )
            self._conn.execute(
                "INSERT OR IGNORE INTO stats(user_id) VALUES(?)", (uid,)
            )
            self._conn.execute(
                "INSERT OR IGNORE INTO settings(user_id, media, data, updated_at) VALUES(?,?,?,?)",
                (uid, "global", json.dumps(DEFAULT_SETTINGS), now),
            )

    def is_blocked(self, uid: int) -> bool:
        row = self.q("SELECT is_blocked FROM users WHERE id=?", (uid,))
        return bool(row and row[0]["is_blocked"])

    def set_blocked(self, uid: int, blocked: bool) -> None:
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT INTO users(id, is_blocked, created_at, last_activity) VALUES(?,?,?,?) "
                "ON CONFLICT(id) DO UPDATE SET is_blocked=excluded.is_blocked",
                (uid, int(blocked), datetime.now(timezone.utc).isoformat(),
                 datetime.now(timezone.utc).isoformat()),
            )

    def all_user_ids(self) -> List[int]:
        return [r["id"] for r in self.q("SELECT id FROM users WHERE is_blocked=0")]

    # -- settings ----------------------------------------------------------
    def get_settings(self, uid: int, media: str) -> Dict[str, Any]:
        row = self.q("SELECT data FROM settings WHERE user_id=? AND media=?", (uid, media))
        if row:
            data = json.loads(row[0]["data"])
        elif media == "global":
            data = dict(DEFAULT_SETTINGS)
            self.save_settings(uid, media, data)
        else:
            data = self.get_settings(uid, "global")  # inherit global on first use
            self.save_settings(uid, media, data)
        merged = dict(DEFAULT_SETTINGS)
        merged.update(data)
        return merged

    def save_settings(self, uid: int, media: str, data: Dict[str, Any]) -> None:
        now = datetime.now(timezone.utc).isoformat()
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT INTO settings(user_id, media, data, updated_at) VALUES(?,?,?,?) "
                "ON CONFLICT(user_id, media) DO UPDATE SET data=excluded.data, updated_at=excluded.updated_at",
                (uid, media, json.dumps(data), now),
            )

    def reset_settings(self, uid: int, media: str) -> None:
        self.save_settings(uid, media, dict(DEFAULT_SETTINGS))

    # -- stats ---------------------------------------------------------------
    def bump_stat(self, uid: int, kind: str) -> None:
        col = {"image": "images", "pdf": "pdfs", "video": "videos", "batch": "batches",
               "error": "errors"}.get(kind)
        if not col:
            return
        now = datetime.now(timezone.utc).isoformat()
        with self._lock, self._conn:
            self._conn.execute(
                f"UPDATE stats SET {col}={col}+1, last_processed=? WHERE user_id=?", (now, uid)
            )

    def totals(self) -> Dict[str, int]:
        row = self.q(
            "SELECT COALESCE(SUM(images),0) i, COALESCE(SUM(pdfs),0) p, "
            "COALESCE(SUM(videos),0) v, COALESCE(SUM(batches),0) b FROM stats"
        )[0]
        return {"images": row["i"], "pdfs": row["p"], "videos": row["v"], "batches": row["b"]}

    def user_counts(self) -> Tuple[int, int]:
        total = self.q("SELECT COUNT(*) c FROM users")[0]["c"]
        cutoff = datetime.fromtimestamp(time.time() - 7 * 86400, timezone.utc).isoformat()
        week = self.q("SELECT COUNT(*) c FROM users WHERE last_activity > ?", (cutoff,))[0]["c"]
        return total, week

    # -- kv (limits + runtime admins) ---------------------------------------
    def kv_get(self, key: str, default: str) -> str:
        row = self.q("SELECT value FROM kv WHERE key=?", (key,))
        return row[0]["value"] if row else default

    def kv_set(self, key: str, value: str) -> None:
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT INTO kv(key, value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                (key, value),
            )

    # -- error log -----------------------------------------------------------
    def log_error(self, uid: Optional[int], context: str, message: str) -> None:
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT INTO error_log(ts, user_id, context, message) VALUES(?,?,?,?)",
                (datetime.now(timezone.utc).isoformat(), uid, context, message[:500]),
            )
            self._conn.execute(
                "DELETE FROM error_log WHERE id NOT IN (SELECT id FROM error_log ORDER BY id DESC LIMIT 200)"
            )

    def recent_errors(self, limit: int = 8) -> List[sqlite3.Row]:
        return self.q("SELECT * FROM error_log ORDER BY id DESC LIMIT ?", (limit,))


DB: Database = None  # type: ignore[assignment]

# --------------------------------------------------------------------------
# Runtime limits (kv-backed, admin configurable)
# --------------------------------------------------------------------------


def limit_max_batch() -> int:
    return int(DB.kv_get("max_batch", "10"))


def limit_rate_per_min() -> int:
    return int(DB.kv_get("rate_per_min", "40"))


def is_admin(uid: int) -> bool:
    extra = DB.kv_get("extra_admins", "")
    extras = {int(x) for x in extra.split(",") if x.strip().isdigit()}
    return uid in CFG.admin_ids or uid in extras


# --------------------------------------------------------------------------
# Watermark layer rendering (shared by image / pdf / video engines)
# --------------------------------------------------------------------------
def _apply_opacity(img: Image.Image, opacity: int) -> Image.Image:
    opacity = max(0, min(100, opacity))
    if opacity >= 100:
        return img
    alpha = img.split()[3].point(lambda a: int(a * opacity / 100))
    img.putalpha(alpha)
    return img


def _render_text_tile(s: Dict[str, Any], px_scale: float) -> Image.Image:
    """Render the text watermark (stroke/shadow/badge) on a tight RGBA tile."""
    text = (s.get("text") or "").strip() or "@VirajWatermark"
    size = max(8, int(s["font_size"] * px_scale))
    font = get_font(s["font"], s["bold"], size)
    stroke_w = int(s["stroke_width"] * px_scale) if s["stroke"] else 0
    rgb = hex_to_rgb(s["color"])
    srgb = hex_to_rgb(s["stroke_color"])

    pad = stroke_w + int(6 * px_scale) + (int(10 * px_scale) if s["shadow"] else 0)
    dummy = Image.new("RGBA", (8, 8))
    d = ImageDraw.Draw(dummy)
    bbox = d.textbbox((0, 0), text, font=font, stroke_width=stroke_w)
    tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]

    badge = s.get("badge") == "box"
    extra = int(14 * px_scale) if badge else 0
    w, h = tw + pad * 2 + extra, th + pad * 2 + extra
    tile = Image.new("RGBA", (max(2, w), max(2, h)), (0, 0, 0, 0))
    draw = ImageDraw.Draw(tile)

    if s["shadow"]:
        off = int(3 * px_scale)
        draw.text((pad - bbox[0] + off, pad - bbox[1] + off), text, font=font,
                  fill=(0, 0, 0, 200), stroke_width=stroke_w, stroke_fill=(0, 0, 0, 200))
        tile = tile.filter(ImageFilter.GaussianBlur(max(1, int(1.5 * px_scale))))
        draw = ImageDraw.Draw(tile)

    if badge:
        draw.rounded_rectangle(
            [int(4 * px_scale), int(4 * px_scale), w - int(4 * px_scale), h - int(4 * px_scale)],
            radius=int(10 * px_scale), fill=(20, 20, 25, 170),
            outline=(255, 255, 255, 160), width=max(1, int(1.5 * px_scale)),
        )
    draw.text((pad - bbox[0], pad - bbox[1]), text, font=font, fill=(*rgb, 255),
              stroke_width=stroke_w, stroke_fill=(*srgb, 255))
    return tile


def _render_logo_tile(s: Dict[str, Any], logo_path: str, px_scale: float,
                      base_side: int) -> Image.Image:
    with Image.open(logo_path) as logo:
        logo = logo.convert("RGBA")
        target = max(16, int(base_side * s["logo_scale"] / 100))
        ratio = target / min(logo.width, logo.height)
        logo = logo.resize((max(1, int(logo.width * ratio)), max(1, int(logo.height * ratio))),
                           Image.LANCZOS)
        logo = _apply_opacity(logo, s["logo_opacity"])
        if s["logo_rotation"]:
            logo = logo.rotate(s["logo_rotation"], expand=True, resample=Image.BICUBIC)
        return logo


def _paste_tile(layer: Image.Image, tile: Image.Image, s: Dict[str, Any],
                px_scale: float, rotation: int, tiled: bool, spacing: int) -> None:
    if rotation:
        tile = tile.rotate(rotation, expand=True, resample=Image.BICUBIC)
    W, H = layer.size
    tw, th = tile.size
    margin = int(s["margin"] * px_scale)

    if tiled:
        step_x = tw + int(spacing * px_scale)
        step_y = th + int(spacing * px_scale)
        y = margin
        while y < H:
            x = margin
            while x < W:
                layer.alpha_composite(tile, (int(x), int(y)))
                x += step_x
            y += step_y
        return

    pos = s["position"]
    if pos == "custom":
        x = int(s["custom_x"] * px_scale)
        y = int(s["custom_y"] * px_scale)
    else:
        # position keys are "<vertical>_<horizontal>", e.g. bottom_right
        vy, vx = ("center", "center") if pos == "center" else pos.split("_", 1)
        x = {"left": margin, "center": (W - tw) // 2, "right": W - tw - margin}[vx]
        y = {"top": margin, "center": (H - th) // 2, "bottom": H - th - margin}[vy]
    layer.alpha_composite(tile, (max(0, x), max(0, y)))


def build_watermark_layer(size: Tuple[int, int], s: Dict[str, Any],
                          logo_path: Optional[str], px_scale: float) -> Image.Image:
    """Full-frame transparent RGBA layer with the configured watermark."""
    layer = Image.new("RGBA", size, (0, 0, 0, 0))
    mode = s.get("mode", "text")
    base_side = min(size)

    if mode in ("text", "both") and s.get("enabled", True):
        tile = _render_text_tile(s, px_scale)
        tile = _apply_opacity(tile, s["opacity"])
        _paste_tile(layer, tile, s, px_scale, s["rotation"], s["tiled"], s["tile_spacing"])

    if mode in ("logo", "both") and logo_path and os.path.isfile(logo_path):
        ltile = _render_logo_tile(s, logo_path, px_scale, base_side)
        _paste_tile(layer, ltile, s, px_scale, 0, s["logo_tiled"], s["tile_spacing"])
    return layer


def logo_file_for(uid: int, media: str) -> str:
    base = os.path.dirname(os.path.abspath(DB.path))
    d = os.path.join(base, "logos")
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, f"logo_{uid}_{media}.png")


# --------------------------------------------------------------------------
# IMAGE engine
# --------------------------------------------------------------------------
Image.MAX_IMAGE_PIXELS = 178_956_970  # Pillow default safety threshold


def process_image_file(src: str, dst: str, s: Dict[str, Any], uid: int) -> None:
    try:
        with Image.open(src) as im:
            im.load()
            original_format = im.format or "PNG"
            original_mode = im.mode
            exif = im.info.get("exif")
            base = im.convert("RGBA")
            px_scale = max(base.width, base.height) / 720.0
            layer = build_watermark_layer(base.size, s, logo_file_for(uid, "image")
                                          if s["mode"] != "text" else None, px_scale)
            base.alpha_composite(layer)
    except WatermarkError:
        raise
    except Exception as exc:  # corrupted / unsupported
        raise WatermarkError(f"Could not read this image ({type(exc).__name__}). "
                             "The file may be corrupted or unsupported.") from exc

    out = base
    save_kwargs: Dict[str, Any] = {}
    fmt = original_format.upper()
    if fmt in ("JPEG", "JPG"):
        fmt = "JPEG"
        out = base.convert("RGB")
        save_kwargs = {"quality": 95, "optimize": True}
        if exif:
            save_kwargs["exif"] = exif
    elif fmt == "PNG":
        save_kwargs = {"optimize": True}
        if original_mode == "P":
            out = out.convert("RGBA")
    elif fmt == "WEBP":
        save_kwargs = {"quality": 95}
        if original_mode not in ("RGBA", "LA"):
            out = base.convert("RGB")
    else:
        fmt = "PNG"
    try:
        out.save(dst, format=fmt, **save_kwargs)
    except Exception:
        # safest fallback: PNG (lossless, supports transparency)
        base.convert("RGBA").save(dst, format="PNG")


# --------------------------------------------------------------------------
# PDF engine
# --------------------------------------------------------------------------
def process_pdf_file(src: str, dst: str, s: Dict[str, Any], uid: int,
                     progress: Optional[Callable[[int, int], None]] = None) -> int:
    if fitz is None:
        raise WatermarkError("PDF support is unavailable on this server (PyMuPDF missing).")
    try:
        doc = fitz.open(src)
    except Exception:
        raise WatermarkError("This PDF could not be opened. It may be corrupted or unsupported.")
    try:
        if doc.is_encrypted and not doc.authenticate(""):
            raise WatermarkError("This PDF is password-protected. "
                                 "Please remove the password and try again.")
        pages = parse_page_spec(s.get("pdf_pages", "all"), doc.page_count)
        logo = logo_file_for(uid, "pdf") if s["mode"] != "text" else None
        for n, pno in enumerate(pages):
            page = doc[pno]
            rect = page.rect
            scale = (max(rect.width, rect.height) / 720.0) * 2.0
            layer = build_watermark_layer((int(rect.width * 2), int(rect.height * 2)),
                                          s, logo, scale)
            buf = io.BytesIO()
            layer.save(buf, format="PNG")
            buf.seek(0)
            page.insert_image(rect, stream=buf.read(), overlay=True)
            if progress:
                progress(n + 1, len(pages))
        doc.save(dst, garbage=3, deflate=True)
        return doc.page_count
    finally:
        doc.close()


# --------------------------------------------------------------------------
# VIDEO engine (FFmpeg overlay of a rendered transparent PNG layer)
# --------------------------------------------------------------------------
def find_ffmpeg() -> Optional[str]:
    if CFG.ffmpeg_path and os.path.isfile(CFG.ffmpeg_path):
        return CFG.ffmpeg_path
    path = shutil.which("ffmpeg")
    if path:
        return path
    try:  # pip-bundled static binary fallback (great for Windows/VPS without apt)
        import imageio_ffmpeg
        return imageio_ffmpeg.get_ffmpeg_exe()
    except Exception:
        return None


FFMPEG_SETUP_MSG = (
    "⚠️ <b>FFmpeg is not installed on this server.</b>\n"
    "Video watermarking needs FFmpeg.\n\n"
    "<b>Ubuntu/Debian:</b> <code>sudo apt install ffmpeg</code>\n"
    "<b>Windows:</b> download from ffmpeg.org or <code>pip install imageio-ffmpeg</code>\n"
    "<b>macOS:</b> <code>brew install ffmpeg</code>\n"
    "Or set <code>FFMPEG_PATH</code> in .env to an existing binary."
)


async def _ffprobe_dims(ffmpeg: str, src: str) -> Tuple[int, int, float]:
    exe = ffmpeg.replace("ffmpeg", "ffprobe") if "ffmpeg" in ffmpeg else ""
    args = ([exe] if exe and os.path.isfile(exe) else [ffmpeg, "-i"])
    if exe and os.path.isfile(exe):
        args = [exe, "-v", "error", "-select_streams", "v:0",
                "-show_entries", "stream=width,height:format=duration",
                "-of", "json", src]
    else:
        args = [ffmpeg, "-hide_banner", "-i", src]
    proc = await asyncio.create_subprocess_exec(
        *args, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
    )
    out, err = await asyncio.wait_for(proc.communicate(), timeout=30)
    text = (out or b"").decode(errors="replace") + (err or b"").decode(errors="replace")
    w = h = 0
    dur = 0.0
    m = re.search(r"(\d{2,5})x(\d{2,5})", text)
    if m:
        w, h = int(m.group(1)), int(m.group(2))
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", text)
    if m:
        dur = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    m2 = re.search(r'"duration":\s*"([\d.]+)"', text)
    if m2:
        dur = max(dur, float(m2.group(1)))
    if w == 0 or h == 0:
        raise WatermarkError("Could not read this video (unsupported or corrupted).")
    return w, h, dur


def animation_overlay_xy(name: str) -> Tuple[str, str]:
    """Return FFmpeg overlay x/y expressions. Expressions use main_w/main_h, w/h and t."""
    # Keep expressions conservative and compatible with FFmpeg's expression evaluator.
    table = {
        "none": ("(main_w-w)/2", "(main_h-h)/2"),
        "dvd_bounce": ("abs(mod(120*t,2*(main_w-w))-(main_w-w))", "abs(mod(90*t,2*(main_h-h))-(main_h-h))"),
        "left_right": ("(main_w-w)*(0.5+0.5*sin(1.2*t))", "(main_h-h)/2"),
        "up_down": ("(main_w-w)/2", "(main_h-h)*(0.5+0.5*sin(1.2*t))"),
        "diagonal": ("(main_w-w)*(0.5+0.5*sin(0.8*t))", "(main_h-h)*(0.5+0.5*sin(0.8*t+PI/2))"),
        "circle": ("(main_w-w)/2+(main_w-w)*0.4*cos(t)", "(main_h-h)/2+(main_h-h)*0.4*sin(t)"),
        "figure8": ("(main_w-w)/2+(main_w-w)*0.4*sin(t)", "(main_h-h)/2+(main_h-h)*0.25*sin(2*t)"),
        "shake": ("(main_w-w)/2+12*sin(35*t)", "(main_h-h)/2+8*cos(41*t)"),
        "pulse": ("(main_w-w)/2", "(main_h-h)/2"),
        "zoom": ("(main_w-w)/2", "(main_h-h)/2"),
        "spin": ("(main_w-w)/2", "(main_h-h)/2"),
        "swing": ("(main_w-w)/2+80*sin(1.5*t)", "(main_h-h)/2"),
        "wave": ("(main_w-w)/2+100*sin(1.4*t)", "(main_h-h)/2+35*sin(2.8*t)"),
        "zigzag": ("(main_w-w)*(0.5+0.5*sin(2*t))", "(main_h-h)*(0.5+0.5*sin(4*t))"),
        "random": ("(main_w-w)*(0.5+0.45*sin(7.1*t))", "(main_h-h)*(0.5+0.45*sin(9.3*t))"),
        "bounce": ("(main_w-w)/2+abs(sin(1.8*t))*(main_w-w)*0.35", "(main_h-h)-abs(sin(2.2*t))*(main_h-h)*0.8"),
        "corner": ("if(lt(mod(t,8),2),0,if(lt(mod(t,8),4),main_w-w,if(lt(mod(t,8),6),main_w-w,0)))", "if(lt(mod(t,8),2),0,if(lt(mod(t,8),4),0,if(lt(mod(t,8),6),main_h-h,main_h-h)))"),
        "spiral": ("(main_w-w)/2+(main_w-w)*0.4*sin(t)*sin(0.25*t)", "(main_h-h)/2+(main_h-h)*0.4*cos(t)*sin(0.25*t)"),
        "horizontal_scan": ("(main_w-w)*(0.5+0.5*sin(0.7*t))", "10"),
        "vertical_scan": ("10", "(main_h-h)*(0.5+0.5*sin(0.7*t))"),
        "pendulum": ("(main_w-w)/2+120*sin(0.9*t)", "(main_h-h)/2+35*abs(cos(0.9*t))"),
        "orbit": ("(main_w-w)/2+(main_w-w)*0.35*cos(0.8*t)", "(main_h-h)/2+(main_h-h)*0.35*sin(0.8*t)"),
        "drift": ("(main_w-w)/2+80*sin(0.25*t)", "(main_h-h)/2+40*cos(0.35*t)"),
        "strobe": ("(main_w-w)/2", "(main_h-h)/2"),
        "elastic": ("(main_w-w)/2+100*sin(2*t)*abs(sin(t))", "(main_h-h)/2"),
        "float": ("(main_w-w)/2+40*sin(0.5*t)", "(main_h-h)/2+40*sin(0.8*t)"),
    }
    return table.get(name, table["none"])


def animation_filter(name: str, speed: float = 1.0) -> str:
    """Build the optional FFmpeg filter for animated watermark layers."""
    x, y = animation_overlay_xy(name)
    speed = max(0.1, min(4.0, float(speed or 1.0)))
    # Scale/rotation animations affect the overlay layer itself; movement is done by overlay expressions.
    if name in ("pulse", "zoom"):
        factor = f"(1+0.12*sin({1.6*speed:.3f}*t))" if name == "pulse" else f"(1+0.20*sin({1.1*speed:.3f}*t))"
        return f"[1:v]scale=iw*{factor}:ih*{factor}:eval=frame[wm];[0:v][wm]overlay=x={x}:y={y}:eval=frame:format=auto"
    if name == "spin":
        return f"[1:v]rotate({0.8*speed:.3f}*t:c=none:ow=rotw(iw):oh=roth(ih)[wm];[0:v][wm]overlay=x={x}:y={y}:eval=frame:format=auto"
    if name == "strobe":
        return f"[1:v]format=rgba,colorchannelmixer=aa='if(lt(mod(t,{1.0/max(speed,0.1):.3f}),0.5),1,0.35)'[wm];[0:v][wm]overlay=x={x}:y={y}:eval=frame:format=auto"
    return f"[0:v][1:v]overlay=x={x}:y={y}:eval=frame:format=auto"


async def process_video_file(src: str, dst: str, s: Dict[str, Any], uid: int,
                             ffmpeg: str,
                             progress: Optional[Callable[[float], Awaitable[None]]] = None,
                             ) -> None:
    w, h, dur = await _ffprobe_dims(ffmpeg, src)
    px_scale = max(w, h) / 720.0
    layer = build_watermark_layer((w, h), s,
                                  logo_file_for(uid, "video") if s["mode"] != "text" else None,
                                  px_scale)
    layer_path = dst + ".wm.png"
    layer.save(layer_path, format="PNG")
    args = [
        ffmpeg, "-y", "-v", "warning", "-i", src, "-i", layer_path,
        "-filter_complex", animation_filter(s.get("animation", "none"), s.get("animation_speed", 1.0)),
        "-c:v", "libx264", "-preset", "veryfast", "-crf", "23",
        "-c:a", "copy", "-movflags", "+faststart", dst,
    ]
    proc = await asyncio.create_subprocess_exec(
        *args, stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE
    )
    last_pct = -10.0
    try:
        async def reader():
            nonlocal last_pct
            assert proc.stderr is not None
            while True:
                line = await proc.stderr.readline()
                if not line:
                    break
                m = re.search(r"time=(\d+):(\d+):(\d+\.\d+)", line.decode(errors="replace"))
                if m and dur > 0 and progress:
                    t = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
                    pct = min(99.0, t / dur * 100)
                    if pct - last_pct >= 10:
                        last_pct = pct
                        await progress(pct)
        await asyncio.wait_for(reader(), timeout=CFG.video_timeout)
        await asyncio.wait_for(proc.wait(), timeout=60)
    except asyncio.TimeoutError:
        proc.kill()
        raise WatermarkError("Video processing timed out. Try a shorter video.")
    finally:
        try:
            os.remove(layer_path)
        except OSError:
            pass
    if proc.returncode != 0 or not os.path.isfile(dst) or os.path.getsize(dst) == 0:
        raise WatermarkError("FFmpeg failed to process this video. "
                             "The codec may be unsupported.")


# --------------------------------------------------------------------------
# UI screens & keyboards (compact reference-style Telegram layout)
# --------------------------------------------------------------------------
def kb(rows: List[List[InlineKeyboardButton]]) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(rows)


def btn(text: str, cb: Optional[str] = None, url: Optional[str] = None) -> InlineKeyboardButton:
    return InlineKeyboardButton(text, callback_data=cb, url=url)


CANCEL_BTN = btn("❌ Cancel", "nav:cancel")




def menu_reply_markup():
    """Persistent, non-destructive menu button shown below the chat input."""
    try:
        from telegram import ReplyKeyboardMarkup, KeyboardButton
        return ReplyKeyboardMarkup([[KeyboardButton("☰ Menu")]], resize_keyboard=True, is_persistent=True)
    except Exception:
        return None

def main_menu_kb() -> InlineKeyboardMarkup:
    """Compact reference-style menu with labels that fit narrow screens."""
    return kb([
        [btn("➕ Add Watermark", "nav:add"), btn("⚙️ Settings", "nav:hub")],
        [btn("🖼️ Process Image", "proc:image"), btn("📄 Process PDF", "proc:pdf")],
        [btn("🎥 Process Video", "proc:video"), btn("⚡ Batch", "nav:batch")],
        [btn("📊 My Settings", "nav:myset"), btn("❓ Help", "nav:help")],
        [btn("ℹ️ About", "nav:about"), btn("🧑‍💼 Contact Admin", url=CFG.admin_contact_url)],
        [btn("🏠 Back to Start", "nav:main")],
    ])


def settings_hub_kb() -> InlineKeyboardMarkup:
    return kb([
        [btn("🎥 Video", "cat:video"), btn("🖼️ Image", "cat:image")],
        [btn("📄 PDF", "cat:pdf"), btn("🌐 Global Defaults", "cat:global")],
        [btn("🏠 Back to Main Menu", "nav:main")],
    ])


def my_settings_kb() -> InlineKeyboardMarkup:
    return kb([
        [btn("🎥 Video", "cat:video"), btn("🖼️ Image", "cat:image"), btn("📄 PDF", "cat:pdf")],
        [btn("🏠 Back to Start", "nav:main")],
    ])


def animation_kb(media: str, s: Dict[str, Any]) -> InlineKeyboardMarkup:
    current = s.get("animation", "none")
    rows = []
    items = list(VIDEO_ANIMATIONS.items())
    for i in range(0, len(items), 2):
        rows.append([btn(("✅ " if k == current else "") + v, f"an:{media}:{k}") for k, v in items[i:i+2]])
    rows.append([btn("🐢 Slower", f"as:{media}:-"), btn(f"⚡ Speed {s.get('animation_speed', 1.0):.1f}x", f"cat:{media}"), btn("🐇 Faster", f"as:{media}:+")])
    rows.append([btn("⬅️ Back", f"cat:{media}")])
    return kb(rows)


def category_kb(media: str, s: Dict[str, Any]) -> InlineKeyboardMarkup:
    toggle = ("🔴 Turn OFF" if s["enabled"] else "🟢 Turn ON")
    mode_label = {"text": "✍️ Mode: Text", "logo": "🖼️ Mode: Logo",
                  "both": "🎨 Mode: Both"}[s["mode"]]
    return kb([
        [btn(toggle, f"act:{media}:toggle"), btn("✏️ Text", f"act:{media}:text")],
        [btn("🔤 Font", f"act:{media}:font"), btn("✨ Style", f"act:{media}:style")],
        [btn("📏 Size", f"act:{media}:size"), btn("🎨 Color", f"act:{media}:color")],
        [btn("💧 Opacity", f"act:{media}:opacity"), btn("📍 Position", f"act:{media}:position")],
        [btn("🧊 Badge & Effects", f"act:{media}:badge"), btn("⚙️ Stroke & Shadow", f"act:{media}:stroke")],
        *([[btn(f"🎬 Animation: {VIDEO_ANIMATIONS.get(s.get('animation', 'none'), 'None')}", f"act:{media}:animation")]] if media == "video" else []),
        [btn(mode_label, f"act:{media}:mode"), btn("🖼️ Logo", f"act:{media}:logo")],
    ] + ([[btn(f"📄 Pages: {s['pdf_pages']}", f"act:{media}:pdfpages")]] if media == "pdf" else []) + [
        [btn("🔄 Reset to Default", f"act:{media}:reset"), btn("⬅️ Back", f"nav:catback:{media}")],
    ])


def font_kb(media: str, current: str) -> InlineKeyboardMarkup:
    rows = [[btn(("✅ " if f == current else "") + f, f"f:{media}:{f}")] for f in FONT_FAMILIES]
    rows.append([btn("⬅️ Back", f"cat:{media}")])
    return kb(rows)


def style_kb(media: str, s: Dict[str, Any]) -> InlineKeyboardMarkup:
    return kb([
        [btn(("✅ Bold" if s["bold"] else "Bold"), f"st:{media}:bold"),
         btn(("✅ Italic" if s["italic"] else "Italic"), f"st:{media}:italic")],
        [btn("🔄 0°", f"st:{media}:rot0"), btn("🔄 45°", f"st:{media}:rot45"),
         btn("🔄 90°", f"st:{media}:rot90"), btn("🔄 -45°", f"st:{media}:rotm45")],
        [btn("🎯 Custom Rotation", f"act:{media}:rotc")],
        [btn("⬅️ Back", f"cat:{media}")],
    ])


def size_kb(media: str, s: Dict[str, Any]) -> InlineKeyboardMarkup:
    return kb([
        [btn("➖ Decrease", f"sz:{media}:-"), btn(f"📏 {s['font_size']} px", f"cat:{media}"),
         btn("➕ Increase", f"sz:{media}:+")],
        [btn("24", f"sz:{media}:24"), btn("36", f"sz:{media}:36"), btn("48", f"sz:{media}:48"),
         btn("64", f"sz:{media}:64"), btn("96", f"sz:{media}:96")],
        [btn("⬅️ Back", f"cat:{media}")],
    ])


COLOR_PRESETS = ["#FFFFFF", "#000000", "#FF0000", "#00FF00", "#0000FF", "#FFFF00", "#FF00FF", "#00FFFF"]


def color_kb(media: str, s: Dict[str, Any]) -> InlineKeyboardMarkup:
    rows = [
        [btn(c, f"c:{media}:{c[1:]}") for c in COLOR_PRESETS[:4]],
        [btn(c, f"c:{media}:{c[1:]}") for c in COLOR_PRESETS[4:]],
        [btn("✏️ Custom Hex", f"act:{media}:colorc")],
        [btn("⬅️ Back", f"cat:{media}")],
    ]
    return kb(rows)


def opacity_kb(media: str, s: Dict[str, Any], key: str = "opacity") -> InlineKeyboardMarkup:
    val = s[key]
    return kb([
        [btn("➖ -5%", f"o:{media}:{key}:-"), btn(f"💧 {val}%", f"cat:{media}"),
         btn("➕ +5%", f"o:{media}:{key}:+")],
        [btn("25%", f"o:{media}:{key}:25"), btn("50%", f"o:{media}:{key}:50"),
         btn("75%", f"o:{media}:{key}:75"), btn("100%", f"o:{media}:{key}:100")],
        [btn("⬅️ Back", f"cat:{media}")],
    ])


def position_kb(media: str, s: Dict[str, Any]) -> InlineKeyboardMarkup:
    keys = list(POSITIONS)[:9]
    rows = []
    for i in range(0, 9, 3):
        rows.append([btn(POSITIONS[k][1] + (" ✅" if s["position"] == k else ""), f"p:{media}:{k}")
                     for k in keys[i:i + 3]])
    rows.append([btn("🎯 Custom Coordinates", f"act:{media}:posc"),
                 btn(f"📐 Margin {s['margin']}", f"cat:{media}")])
    rows.append([btn("➖ Margin", f"p:{media}:m-"), btn("➕ Margin", f"p:{media}:m+")])
    rows.append([btn("⬅️ Back", f"cat:{media}")])
    return kb(rows)


def badge_kb(media: str, s: Dict[str, Any]) -> InlineKeyboardMarkup:
    return kb([
        [btn(("✅ " if s["badge"] == "plain" else "") + "✨ Plain Text", f"b:{media}:plain"),
         btn(("✅ " if s["badge"] == "box" else "") + "🧊 Badge Box", f"b:{media}:box")],
        [btn(("✅ " if s["tiled"] else "") + "🔁 Tiled Watermark", f"b:{media}:tile"),
         btn(f"📐 Spacing {s['tile_spacing']}", f"cat:{media}")],
        [btn("➖ Spacing", f"b:{media}:sp-"), btn("➕ Spacing", f"b:{media}:sp+")],
        [btn("⬅️ Back", f"cat:{media}")],
    ])


def stroke_kb(media: str, s: Dict[str, Any]) -> InlineKeyboardMarkup:
    return kb([
        [btn(("🟢" if s["stroke"] else "⚪") + " Outline Stroke", f"k:{media}:stroke"),
         btn(("🟢" if s["shadow"] else "⚪") + " Drop Shadow", f"k:{media}:shadow")],
        [btn("➖ Width", f"k:{media}:w-"), btn(f"✏️ Width {s['stroke_width']}", f"cat:{media}"),
         btn("➕ Width", f"k:{media}:w+")],
        [btn("⬅️ Back", f"cat:{media}")],
    ])


def logo_kb(media: str, s: Dict[str, Any], uid: int) -> InlineKeyboardMarkup:
    has = os.path.isfile(logo_file_for(uid, media))
    return kb([
        [btn(("✅ Logo set" if has else "⬆️ Upload Logo"), f"act:{media}:logoup")],
        [btn("➖ Scale", f"lg:{media}:s-"), btn(f"📏 Scale {s['logo_scale']}%", f"cat:{media}"),
         btn("➕ Scale", f"lg:{media}:s+")],
        [btn("➖ Opacity", f"lg:{media}:o-"), btn(f"💧 {s['logo_opacity']}%", f"cat:{media}"),
         btn("➕ Opacity", f"lg:{media}:o+")],
        [btn("🔄 0°", f"lg:{media}:r0"), btn("🔄 90°", f"lg:{media}:r90"),
         btn(("✅ " if s["logo_tiled"] else "") + "🔁 Tile", f"lg:{media}:tile")],
        [btn("🗑️ Remove Logo", f"lg:{media}:clear")],
        [btn("⬅️ Back", f"cat:{media}")],
    ])


def batch_kb() -> InlineKeyboardMarkup:
    return kb([[btn("✅ Done — Process Batch", "batch:done"),
                btn("❌ Cancel", "batch:cancel")]])


# --------------------------------------------------------------------------
# Screen texts
# --------------------------------------------------------------------------
def main_menu_text() -> str:
    # Telegram clients do not expose arbitrary button background colours to bots.
    # This presentation layer therefore uses a colourful, compact card-like layout
    # while preserving all existing wording and emojis.
    return (
        "<blockquote>"
        f"🎨 <b>{serif_bold('Viraj Watermark')}</b>\n"
        "<i>━━━━━━━━━━━━━━━━━━━━</i>\n\n"
        "Welcome! Add professional watermarks to your Images, PDFs and Videos.\n"
        "Choose an option below to get started.\n\n"
        "<i>━━━━━━━━━━━━━━━━━━━━</i>\n"
        "⚡ <b>Channel Batch Watermarking</b>\n"
        "<blockquote expandable>Channel Batch Watermarking is an automated tool "
        "reserved exclusively for VIP &amp; ranked channels. Contact the admin to upgrade."
        "</blockquote>"
        "</blockquote>"
    )


def settings_hub_text() -> str:
    return (
        "<blockquote>"
        f"🎨 <b>{serif_bold('Watermark Settings Hub')}</b>\n"
        "<i>━━━━━━━━━━━━━━━━━━━━</i>\n\n"
        "Select a media category below to configure watermarks for your files.\n"
        "Each media category maintains independent persistent settings.\n\n"
        "<i>━━━━━━━━━━━━━━━━━━━━</i>"
        "</blockquote>"
    )


def my_settings_text(uid: int) -> str:
    rows = []
    for media in ("video", "image", "pdf"):
        s = DB.get_settings(uid, media)
        emoji, _, label = MEDIA_LABELS[media]
        rows.append([
            f"{emoji} {label}",
            "🟢 ON" if s["enabled"] else "🔴 OFF",
            _trunc(s["text"], 18),
            _trunc(s["font"], 7),
            s["mode"].capitalize(),
        ])
    table = box_table(["Media", "Status", "Text", "Font", "Mode"], rows)
    return (
        "<blockquote>"
        f"📊 <b>{serif_bold('My Watermark Configuration')}</b>\n"
        "<i>━━━━━━━━━━━━━━━━━━━━</i>\n"
        f"<pre>{esc(table)}</pre>\n"
        "<i>━━━━━━━━━━━━━━━━━━━━</i>\n"
        "<blockquote expandable>Video, Image, and PDF maintain isolated settings. "
        "To modify any setting, tap the buttons below.</blockquote>"
        "</blockquote>"
    )


def category_text(media: str, s: Dict[str, Any]) -> str:
    emoji, title, _ = MEDIA_LABELS[media]
    pos_label, pos_emoji = POSITIONS[s["position"]]
    rows = [
        ["Status", "🟢 ENABLED" if s["enabled"] else "🔴 DISABLED"],
        ["Watermark Text", _trunc(s["text"], 24)],
        ["Font Family", f"{s['font']} ({'Bold' if s['bold'] else 'Regular'})"],
        ["Font Size", f"{s['font_size']} px"],
        ["Text Color", s["color"].upper()],
        ["Opacity", f"{s['opacity']}%"],
        ["Anchor Position", f"{pos_emoji} {pos_label}"],
        ["Outline Stroke", "ON" if s["stroke"] else "OFF"],
        ["Drop Shadow", "ON" if s["shadow"] else "OFF"],
        ["Badge & Effect", BADGES[s["badge"]]],
    ]
    if media == "pdf":
        rows.append(["Pages", _trunc(s["pdf_pages"], 24)])
    table = box_table(["Setting", "Value"], rows)
    return (
        "<blockquote>"
        f"{emoji} <b>{serif_bold(title)}</b>\n"
        "<i>━━━━━━━━━━━━━━━━━━━━</i>\n"
        f"<pre>{esc(table)}</pre>\n"
        "<i>━━━━━━━━━━━━━━━━━━━━</i>\n"
        "<blockquote expandable>Click any button below to customize specific "
        "attributes in real-time.</blockquote>"
        "</blockquote>"
    )


def help_text() -> str:
    return (
        f"❓ <b>{serif_bold('Help & Guide')}</b>\n\n"
        "1️⃣ <b>Add Watermark</b> — send any image, PDF or video and it is returned "
        "with your watermark applied.\n"
        "2️⃣ <b>Watermark Settings</b> — configure text/logo, size, color, opacity, "
        "position, rotation, stroke, shadow, badge and tiling per media type.\n"
        "3️⃣ <b>Batch Processing</b> — send multiple files, tap ✅ Done, receive a ZIP.\n"
        "4️⃣ <b>My Settings</b> — view your saved configuration at any time.\n\n"
        "<blockquote expandable>Supported: JPG, JPEG, PNG, WEBP images • PDF "
        "(multi-page, page ranges) • MP4/MKV/MOV/AVI/WEBM videos.\n"
        f"Max incoming file size: {human_size(CFG.max_file_size)} (Telegram Bot API limit).</blockquote>"
    )


def about_text() -> str:
    return (
        f"ℹ️ <b>{serif_bold('About Viraj Watermark')}</b>\n\n"
        "Viraj Watermark adds customizable, permanent watermarks to images, PDFs "
        "and videos — perfect for channels, creators and brands.\n\n"
        "• Independent settings per media type\n"
        "• Text & logo watermarks, tiling, stroke, shadow, badges\n"
        "• Batch processing with ZIP delivery\n"
        "• Privacy-friendly: only your settings & usage stats are stored\n\n"
        "<blockquote expandable>⚡ Channel Batch Watermarking is an automated tool "
        "reserved exclusively for VIP &amp; ranked channels.</blockquote>"
    )


# --------------------------------------------------------------------------
# In-memory session state (prompts, batches) + rate limiting
# --------------------------------------------------------------------------
USER_STATE: Dict[int, Dict[str, Any]] = {}
USER_LOCK: Dict[int, asyncio.Lock] = {}
RATE: Dict[int, deque] = {}


def set_state(uid: int, kind: str, **kw: Any) -> None:
    USER_STATE[uid] = {"kind": kind, **kw}


def get_state(uid: int) -> Optional[Dict[str, Any]]:
    return USER_STATE.get(uid)


def clear_state(uid: int) -> None:
    USER_STATE.pop(uid, None)


def user_lock(uid: int) -> asyncio.Lock:
    if uid not in USER_LOCK:
        USER_LOCK[uid] = asyncio.Lock()
    return USER_LOCK[uid]


def rate_limited(uid: int) -> bool:
    """Artificial per-user rate limiting is disabled by configuration request.

    Telegram/network/provider limits may still apply externally.
    """
    return False


# --------------------------------------------------------------------------
# Temp directory helpers
# --------------------------------------------------------------------------
def user_temp(uid: int) -> str:
    d = os.path.join(CFG.temp_directory, str(uid))
    os.makedirs(d, exist_ok=True)
    return d


def safe_join(base: str, name: str) -> str:
    base = os.path.realpath(base)
    path = os.path.realpath(os.path.join(base, name))
    if not path.startswith(base + os.sep):
        raise WatermarkError("Invalid file name.")
    return path


def clean_temp_dir(max_age: float = 3600) -> int:
    removed = 0
    now = time.time()
    root = Path(CFG.temp_directory)
    if not root.exists():
        return 0
    for p in root.rglob("*"):
        try:
            if p.is_file() and now - p.stat().st_mtime > max_age:
                p.unlink()
                removed += 1
        except OSError:
            pass
    return removed


# --------------------------------------------------------------------------
# Core processing flow
# --------------------------------------------------------------------------
def media_kind_of(ext: str) -> Optional[str]:
    ext = ext.lower()
    if ext in IMAGE_EXTS:
        return "image"
    if ext in PDF_EXTS:
        return "pdf"
    if ext in VIDEO_EXTS:
        return "video"
    return None


async def _tg_retry(fn: Callable[[], Awaitable[Any]], tries: int = 2) -> Any:
    """Retry transient Telegram network failures once."""
    for attempt in range(tries):
        try:
            return await fn()
        except (TimedOut, RetryAfter) as exc:
            if attempt + 1 >= tries:
                raise WatermarkError("Telegram network problem while transferring "
                                     "the file. Please try again.") from exc
            await asyncio.sleep(getattr(exc, "retry_after", 1) + 0.5)
    raise WatermarkError("Telegram network problem while transferring the file.")


async def download_update_file(update: Update) -> Tuple[str, str, int]:
    """Returns (path, ext, size). Raises WatermarkError on validation failure."""
    msg = update.message
    assert msg is not None
    if msg.photo:
        file = await _tg_retry(msg.photo[-1].get_file)
        ext = ".jpg"
        name = sanitize_filename(f"photo{ext}")
    elif msg.video:
        file = await _tg_retry(msg.video.get_file)
        ext = os.path.splitext(msg.video.file_name or ".mp4")[1].lower() or ".mp4"
        name = sanitize_filename(msg.video.file_name or f"video{ext}")
    elif msg.document:
        file = await _tg_retry(msg.document.get_file)
        ext = os.path.splitext(msg.document.file_name or "")[1].lower()
        name = sanitize_filename(msg.document.file_name or f"doc{ext}")
    else:
        raise WatermarkError("Please send a supported file (image, PDF or video).")

    size = file.file_size or 0
    if size > CFG.max_file_size:
        raise WatermarkError(
            f"⚠️ File too large ({human_size(size)}). "
            f"Application limit: {human_size(CFG.max_file_size)}."
        )
    # Telegram may deliver videos as documents; infer the type from MIME/name.
    if not ext and getattr(msg.document, "mime_type", "") == "video/mp4":
        ext = ".mp4"
    if ext and media_kind_of(ext) is None:
        raise WatermarkError(
            "⚠️ Unsupported file type. Supported: JPG, JPEG, PNG, WEBP, PDF, "
            "MP4, MKV, MOV, AVI, WEBM."
        )
    path = safe_join(user_temp(update.effective_user.id), name)
    try:
        await file.download_to_drive(path)
    except TelegramError as exc:
        message = str(exc).lower()
        if "file is too big" in message or "too big" in message or "20 mb" in message:
            raise WatermarkError(
                f"⚠️ Telegram rejected this {human_size(size)} file because the standard "
                "Bot API download limit is about 20 MB. To process larger videos, "
                "configure a self-hosted Telegram Bot API server using "
                "TELEGRAM_API_BASE_URL and TELEGRAM_API_FILE_URL."
            ) from exc
        raise WatermarkError(
            "⚠️ Telegram could not download this file. Check the Bot API connection "
            "or try sending the file as a document."
        ) from exc
    return path, ext, size


async def process_and_send(update: Update, context: ContextTypes.DEFAULT_TYPE,
                           path: str, kind: str) -> None:
    uid = update.effective_user.id
    chat = update.effective_chat
    assert chat is not None
    msg = update.message
    s = DB.get_settings(uid, kind)
    if not s["enabled"]:
        await msg.reply_text(
            f"⚠️ Watermarking is <b>turned OFF</b> for {MEDIA_LABELS[kind][2]}.\n"
            "Enable it in ⚙️ Watermark Settings.", parse_mode=ParseMode.HTML)
        return

    status = await msg.reply_text(f"⏳ Processing your {kind}…")
    await context.bot.send_chat_action(chat.id, "upload_document")
    loop = asyncio.get_running_loop()
    out_path = safe_join(user_temp(uid), "out_" + os.path.basename(path))
    try:
        if kind == "image":
            await asyncio.wait_for(
                loop.run_in_executor(None, process_image_file, path, out_path, s, uid),
                timeout=CFG.process_timeout)
        elif kind == "pdf":
            async def _edit_pdf(t: str) -> None:
                try:
                    await status.edit_text(t)
                except (BadRequest, TelegramError):
                    pass

            def _pdf_progress(done: int, total: int) -> None:
                # called from the executor thread — hop back into the event loop
                asyncio.run_coroutine_threadsafe(_edit_pdf(f"📄 PDF page {done}/{total}…"), loop)

            await asyncio.wait_for(
                loop.run_in_executor(None, process_pdf_file, path, out_path, s, uid, _pdf_progress),
                timeout=CFG.process_timeout)
        elif kind == "video":
            ffmpeg = find_ffmpeg()
            if not ffmpeg:
                await status.edit_text(FFMPEG_SETUP_MSG, parse_mode=ParseMode.HTML)
                return

            async def _vprog(pct: float) -> None:
                try:
                    await status.edit_text(f"🎬 Watermarking video… {pct:.0f}%")
                except (BadRequest, TelegramError):
                    pass

            await process_video_file(path, out_path, s, uid, ffmpeg, _vprog)
        else:
            raise WatermarkError("Unsupported media kind.")

        DB.bump_stat(uid, kind)
        size = os.path.getsize(out_path)
        if size > CFG.upload_limit:
            await status.edit_text(
                f"✅ Processed, but the result ({human_size(size)}) exceeds the configured "
                f"upload limit ({human_size(CFG.upload_limit)}). The file was kept on the server.",
                parse_mode=ParseMode.HTML)
            return
        if not CFG.local_api_base_url and size > 50 * 1024 * 1024:
            await status.edit_text(
                f"✅ Processed ({human_size(size)}), but Telegram's standard Bot API "
                "upload limit is about 50 MB. Configure a self-hosted Bot API server "
                "for larger results. The file was kept on the server.",
                parse_mode=ParseMode.HTML)
            return
        caption = f"✅ Your watermarked {kind} is ready!"
        with open(out_path, "rb") as fh:
            data = fh.read()
        fname = "watermarked" + os.path.splitext(os.path.basename(path))[1]
        if kind == "image":
            await msg.reply_photo(photo=data, caption=caption)
        elif kind == "pdf":
            await msg.reply_document(document=data, filename=fname, caption=caption)
        else:
            await msg.reply_video(video=data, caption=caption)
        await status.delete()
    except WatermarkError as exc:
        DB.bump_stat(uid, "error")
        DB.log_error(uid, kind, str(exc))
        await status.edit_text(f"⚠️ {esc(exc)}", parse_mode=ParseMode.HTML)
    except asyncio.TimeoutError:
        DB.bump_stat(uid, "error")
        await status.edit_text("⚠️ Processing timed out. Please try a smaller file.")
    except (RetryAfter, TimedOut) as exc:
        await status.edit_text("⚠️ Telegram is busy right now. Please try again in a moment.")
        LOG.warning("telegram transient error: %s", exc)
    except TelegramError as exc:
        DB.bump_stat(uid, "error")
        DB.log_error(uid, kind, f"{type(exc).__name__}: {exc}")
        detail = str(exc).lower()
        if "file is too big" in detail or "too big" in detail:
            await status.edit_text(
                "⚠️ Telegram rejected the file because the current Bot API transport "
                "limit was exceeded. Use a self-hosted Bot API server for large files.")
        else:
            await status.edit_text(
                "⚠️ Telegram could not transfer the processed file. Check the Bot API "
                "configuration and try again.")
        LOG.exception("telegram processing error")
    except Exception as exc:  # unexpected — log details, show safe message
        DB.bump_stat(uid, "error")
        DB.log_error(uid, kind, f"{type(exc).__name__}: {exc}")
        LOG.exception("processing failed")
        await status.edit_text("⚠️ Something went wrong while processing this file. "
                               "The admins have been notified.")
    finally:
        for p in (path, out_path):
            try:
                os.remove(p)
            except OSError:
                pass


# --------------------------------------------------------------------------
# Command & callback handlers
# --------------------------------------------------------------------------
async def gate(update: Update) -> bool:
    """Returns True when the update may proceed (not blocked, not rate-limited)."""
    user = update.effective_user
    if not user:
        return False
    if DB.is_blocked(user.id):
        if update.callback_query:
            await update.callback_query.answer("You are blocked.", show_alert=True)
        elif update.message:
            await update.message.reply_text("⛔ You are blocked from using this bot.")
        return False
    if rate_limited(user.id):
        if update.callback_query:
            await update.callback_query.answer("Slow down! Too many requests.", show_alert=True)
        elif update.message:
            await update.message.reply_text("⏳ Slow down! Try again in a minute.")
        return False
    DB.touch_user(user.id, user.username or "", user.first_name or "")
    return True


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await gate(update):
        return
    await update.message.reply_text(  # type: ignore[union-attr]
        main_menu_text(), parse_mode=ParseMode.HTML, reply_markup=main_menu_kb())
    await update.message.reply_text("Use the inline buttons above, or tap ☰ Menu.",
                                    reply_markup=menu_reply_markup())


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await gate(update):
        return
    await update.message.reply_text(help_text(), parse_mode=ParseMode.HTML,  # type: ignore[union-attr]
                                    reply_markup=kb([[btn("🏠 Back to Start", "nav:main")]]))


async def cmd_about(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await gate(update):
        return
    await update.message.reply_text(about_text(), parse_mode=ParseMode.HTML,  # type: ignore[union-attr]
                                    reply_markup=kb([[btn("🏠 Back to Start", "nav:main")]]))


async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await gate(update):
        return
    await update.message.reply_text(settings_hub_text(), parse_mode=ParseMode.HTML,  # type: ignore[union-attr]
                                    reply_markup=settings_hub_kb())


async def cmd_mysettings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await gate(update):
        return
    await update.message.reply_text(  # type: ignore[union-attr]
        my_settings_text(update.effective_user.id), parse_mode=ParseMode.HTML,
        reply_markup=my_settings_kb())


async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    clear_state(update.effective_user.id)
    await update.message.reply_text(  # type: ignore[union-attr]
        "❌ Cancelled.", reply_markup=kb([[btn("🏠 Back to Start", "nav:main")]]))


# ---- admin commands -------------------------------------------------------
async def admin_guard(update: Update) -> bool:
    user = update.effective_user
    if not user or not is_admin(user.id):
        target = update.callback_query or update.message
        if update.callback_query:
            await update.callback_query.answer()
        if target is not None:
            await update.message.reply_text("⛔ Access Denied: Admin only command.")  # type: ignore[union-attr]
        return False
    return True


async def cmd_allow(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await admin_guard(update):
        return
    args = (context.args or [])
    if not args or not args[0].lstrip("-").isdigit():
        await update.message.reply_text("Usage: /allow <user_id>")  # type: ignore[union-attr]
        return
    uid = int(args[0])
    extra = {x for x in DB.kv_get("extra_admins", "").split(",") if x.strip().isdigit()}
    extra.add(str(uid))
    DB.kv_set("extra_admins", ",".join(sorted(extra)))
    await update.message.reply_text(f"✅ User {uid} granted admin rights.")  # type: ignore[union-attr]


async def cmd_block(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await admin_guard(update):
        return
    args = (context.args or [])
    if not args or not args[0].lstrip("-").isdigit():
        await update.message.reply_text("Usage: /block <user_id>")  # type: ignore[union-attr]
        return
    DB.set_blocked(int(args[0]), True)
    await update.message.reply_text(f"🚫 User {args[0]} blocked.")  # type: ignore[union-attr]


async def cmd_unblock(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await admin_guard(update):
        return
    args = (context.args or [])
    if not args or not args[0].lstrip("-").isdigit():
        await update.message.reply_text("Usage: /unblock <user_id>")  # type: ignore[union-attr]
        return
    DB.set_blocked(int(args[0]), False)
    await update.message.reply_text(f"✅ User {args[0]} unblocked.")  # type: ignore[union-attr]


def _admin_stats_text() -> str:
    total_users, active = DB.user_counts()
    tot = DB.totals()
    cpu = psutil.cpu_percent(interval=0.2)
    mem = psutil.virtual_memory()
    disk = psutil.disk_usage(CFG.temp_directory if os.path.isdir(CFG.temp_directory) else ".")
    rows = [
        ["Total Users", str(total_users)],
        ["Active (7d)", str(active)],
        ["Images Processed", str(tot["images"])],
        ["PDFs Processed", str(tot["pdfs"])],
        ["Videos Processed", str(tot["videos"])],
        ["Batches", str(tot["batches"])],
        ["CPU Usage", f"{cpu:.1f}%"],
        ["RAM Usage", f"{mem.percent:.1f}% ({human_size(mem.used)})"],
        ["Disk Usage", f"{disk.percent:.1f}% ({human_size(disk.used)})"],
        ["Bot Uptime", human_duration(time.time() - START_TIME)],
        ["Max Batch", str(limit_max_batch())],
        ["Rate Limit", f"{limit_rate_per_min()}/min"],
    ]
    return ("🛡️ <b>" + serif_bold("Admin Panel") + "</b>\n"
            f"<pre>{esc(box_table(['Metric', 'Value'], rows))}</pre>")


def admin_kb() -> InlineKeyboardMarkup:
    return kb([
        [btn("📢 Broadcast", "adm:broadcast"), btn("🧹 Clean Temp", "adm:clean")],
        [btn("➖ Batch Limit", "lim:batch:-"), btn("➕ Batch Limit", "lim:batch:+")],
        [btn("➖ Rate Limit", "lim:rate:-"), btn("➕ Rate Limit", "lim:rate:+")],
        [btn("📜 Recent Errors", "adm:errors")],
        [btn("🔄 Refresh", "adm:stats"), btn("🏠 Back to Start", "nav:main")],
    ])


async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await admin_guard(update):
        return
    await update.message.reply_text(_admin_stats_text(), parse_mode=ParseMode.HTML,  # type: ignore[union-attr]
                                    reply_markup=admin_kb())


cmd_stats = cmd_admin


# --------------------------------------------------------------------------
# Callback query router
# --------------------------------------------------------------------------
async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    assert query is not None
    user = update.effective_user
    data = query.data or ""
    if not await gate(update):
        return
    uid = user.id

    # every code path below answers the query (exactly once, guarded)
    async def safe_answer(text: Optional[str] = None, alert: bool = True) -> None:
        try:
            await query.answer(text, show_alert=alert)
        except (BadRequest, TelegramError):
            pass

    try:
        await _route_callback(update, context, data, uid)
    except WatermarkError as exc:
        await safe_answer(str(exc))
    except Exception as exc:
        LOG.exception("callback error data=%s", data)
        DB.log_error(uid, "callback", f"{type(exc).__name__}: {exc}")
        await safe_answer("Something went wrong.")


async def _route_callback(update: Update, context: ContextTypes.DEFAULT_TYPE,
                          data: str, uid: int) -> None:
    query = update.callback_query
    assert query is not None
    parts = data.split(":")
    head = parts[0]

    # ---------------- navigation ----------------
    if head == "nav":
        action = parts[1]
        if action == "main":
            await query.answer()
            if query.message and query.message.photo:
                await query.edit_message_caption(main_menu_text(), reply_markup=main_menu_kb())
            else:
                await query.edit_message_text(main_menu_text(), parse_mode=ParseMode.HTML,
                                              reply_markup=main_menu_kb())
            return
        if action == "hub":
            await query.answer()
            await query.edit_message_text(settings_hub_text(), parse_mode=ParseMode.HTML,
                                          reply_markup=settings_hub_kb())
            return
        if action == "myset":
            await query.answer()
            await query.edit_message_text(my_settings_text(uid), parse_mode=ParseMode.HTML,
                                          reply_markup=my_settings_kb())
            return
        if action == "help":
            await query.answer()
            await query.edit_message_text(help_text(), parse_mode=ParseMode.HTML,
                                          reply_markup=kb([[btn("🏠 Back to Start", "nav:main")]]))
            return
        if action == "about":
            await query.answer()
            await query.edit_message_text(about_text(), parse_mode=ParseMode.HTML,
                                          reply_markup=kb([[btn("🏠 Back to Start", "nav:main")]]))
            return
        if action == "add":
            await query.answer()
            set_state(uid, "auto")
            await query.edit_message_text(
                "➕ <b>Add Watermark</b>\n\nSend me an image, PDF or video and I will "
                "return it watermarked with your saved settings.",
                parse_mode=ParseMode.HTML,
                reply_markup=kb([[btn("🏠 Back to Start", "nav:main"), CANCEL_BTN]]))
            return
        if action == "batch":
            await query.answer()
            set_state(uid, "batch", files=[])
            await query.edit_message_text(
                f"⚡ <b>Batch Processing</b>\n\nSend up to <b>{limit_max_batch()}</b> files "
                "(images / PDFs / videos). Tap ✅ Done when finished.",
                parse_mode=ParseMode.HTML, reply_markup=batch_kb())
            return
        if action == "cancel":
            clear_state(uid)
            await query.answer("Cancelled.")
            await query.edit_message_text("❌ Cancelled.",
                                          reply_markup=kb([[btn("🏠 Back to Start", "nav:main")]]))
            return
        if action == "catback":
            media = parts[2]
            await query.answer()
            await _show_category(query, uid, media)
            return
        await query.answer()
        return

    # ---------------- processing entry points ----------------
    if head == "proc":
        kind = parts[1]
        set_state(uid, f"proc_{kind}")
        await query.answer()
        names = {"image": "an image (JPG/PNG/WEBP)", "pdf": "a PDF", "video": "a video"}
        await query.edit_message_text(
            f"📥 Send me {names[kind]} to watermark.", parse_mode=ParseMode.HTML,
            reply_markup=kb([[btn("🏠 Back to Start", "nav:main"), CANCEL_BTN]]))
        return

    # ---------------- category screens ----------------
    if head == "cat":
        media = parts[1]
        await query.answer()
        await _show_category(query, uid, media)
        return

    # ---------------- settings actions ----------------
    if head == "act":
        media, action = parts[1], parts[2]
        s = DB.get_settings(uid, media)
        if action == "toggle":
            s["enabled"] = not s["enabled"]
            DB.save_settings(uid, media, s)
            await query.answer("Toggled.")
            await _show_category(query, uid, media)
            return
        if action == "reset":
            DB.reset_settings(uid, media)
            await query.answer("Reset to defaults.")
            await _show_category(query, uid, media)
            return
        prompts = {
            "text": ("text", "✏️ Send the new watermark text:"),
            "colorc": ("color", "🎨 Send a hex color like #FF00AA:"),
            "posc": ("posc", "🎯 Send custom coordinates as: x,y (pixels from top-left):"),
            "rotc": ("rotc", "🔄 Send a rotation angle in degrees (-360..360):"),
            "pdfpages": ("pdfpages", "📄 Pages to watermark: 'all' or e.g. 1,3-5"),
        }
        if action in prompts:
            kind, text = prompts[action]
            set_state(uid, f"set_{kind}", media=media)
            await query.answer()
            await query.edit_message_text(
                text, parse_mode=ParseMode.HTML,
                reply_markup=kb([[btn("⬅️ Back", f"cat:{media}"), CANCEL_BTN]]))
            return
        if action == "font":
            await query.answer()
            await query.edit_message_text("🔤 Choose a font family:",
                                          reply_markup=font_kb(media, s["font"]))
            return
        if action == "style":
            await query.answer()
            await query.edit_message_text("✨ Style & rotation:", reply_markup=style_kb(media, s))
            return
        if action == "size":
            await query.answer()
            await query.edit_message_text("📏 Font size:", reply_markup=size_kb(media, s))
            return
        if action == "color":
            await query.answer()
            await query.edit_message_text("🎨 Choose a color:", reply_markup=color_kb(media, s))
            return
        if action == "opacity":
            await query.answer()
            await query.edit_message_text("💧 Opacity:", reply_markup=opacity_kb(media, s))
            return
        if action == "position":
            await query.answer()
            await query.edit_message_text("📍 Anchor position & margins:",
                                          reply_markup=position_kb(media, s))
            return
        if action == "badge":
            await query.answer()
            await query.edit_message_text("🧊 Badge & effects:", reply_markup=badge_kb(media, s))
            return
        if action == "animation" and media == "video":
            await query.answer()
            await query.edit_message_text("🎬 Choose video animation:", reply_markup=animation_kb(media, s))
            return
        if action == "stroke":
            await query.answer()
            await query.edit_message_text("⚙️ Stroke & shadow:", reply_markup=stroke_kb(media, s))
            return
        if action == "logo":
            await query.answer()
            await query.edit_message_text("🖼️ Logo watermark settings:",
                                          reply_markup=logo_kb(media, s, uid))
            return
        if action == "mode":
            order = ["text", "logo", "both"]
            s["mode"] = order[(order.index(s["mode"]) + 1) % 3]
            DB.save_settings(uid, media, s)
            await query.answer(f"Mode: {s['mode']}")
            await _show_category(query, uid, media)
            return
        if action == "logoup":
            set_state(uid, "logo", media=media)
            await query.answer()
            await query.edit_message_text(
                "️ Send the logo image (PNG with transparency works best):",
                reply_markup=kb([[btn("⬅️ Back", f"act:{media}:logo"), CANCEL_BTN]]))
            return
        await query.answer()
        return

    # ---------------- submenu value setters ----------------
    s_media = parts[1]
    s = DB.get_settings(uid, s_media)

    if head == "an":
        if s_media != "video":
            await query.answer("Animation is available for videos only.", show_alert=True)
            return
        key = parts[2]
        if key in VIDEO_ANIMATIONS:
            s["animation"] = key
            DB.save_settings(uid, s_media, s)
        await query.answer(VIDEO_ANIMATIONS.get(s.get("animation", "none"), "None"))
        await query.edit_message_text("🎬 Choose video animation:", reply_markup=animation_kb(s_media, s))
        return
    if head == "as":
        if s_media != "video":
            await query.answer("Animation speed is available for videos only.", show_alert=True)
            return
        speed = float(s.get("animation_speed", 1.0))
        speed = min(4.0, speed + 0.1) if parts[2] == "+" else max(0.1, speed - 0.1)
        s["animation_speed"] = round(speed, 1)
        DB.save_settings(uid, s_media, s)
        await query.answer(f"Speed {s['animation_speed']:.1f}x")
        await query.edit_message_text("🎬 Choose video animation:", reply_markup=animation_kb(s_media, s))
        return
    if head == "f":
        s["font"] = parts[2]
        DB.save_settings(uid, s_media, s)
        await query.answer(s["font"])
        await query.edit_message_text("🔤 Choose a font family:",
                                      reply_markup=font_kb(s_media, s["font"]))
        return
    if head == "st":
        act = parts[2]
        if act == "bold":
            s["bold"] = not s["bold"]
        elif act == "italic":
            s["italic"] = not s["italic"]
        elif act == "rot0":
            s["rotation"] = 0
        elif act == "rot45":
            s["rotation"] = 45
        elif act == "rot90":
            s["rotation"] = 90
        elif act == "rotm45":
            s["rotation"] = -45
        DB.save_settings(uid, s_media, s)
        await query.answer()
        await query.edit_message_text("✨ Style & rotation:", reply_markup=style_kb(s_media, s))
        return
    if head == "sz":
        val = parts[2]
        if val == "+":
            s["font_size"] = min(200, s["font_size"] + 4)
        elif val == "-":
            s["font_size"] = max(10, s["font_size"] - 4)
        else:
            s["font_size"] = int(val)
        DB.save_settings(uid, s_media, s)
        await query.answer(f"{s['font_size']} px")
        await query.edit_message_text("📏 Font size:", reply_markup=size_kb(s_media, s))
        return
    if head == "c":
        try:
            hex_to_rgb(parts[2])
        except WatermarkError:
            await query.answer("Bad color", show_alert=True)
            return
        s["color"] = "#" + parts[2].upper()
        DB.save_settings(uid, s_media, s)
        await query.answer(s["color"])
        await query.edit_message_text("🎨 Choose a color:", reply_markup=color_kb(s_media, s))
        return
    if head == "o":
        key, val = parts[2], parts[3]
        cur = s[key]
        if val == "+":
            cur = min(100, cur + 5)
        elif val == "-":
            cur = max(5, cur - 5)
        else:
            cur = int(val)
        s[key] = cur
        DB.save_settings(uid, s_media, s)
        await query.answer(f"{cur}%")
        await query.edit_message_text("💧 Opacity:", reply_markup=opacity_kb(s_media, s, key))
        return
    if head == "p":
        act = parts[2]
        if act == "m+":
            s["margin"] = min(300, s["margin"] + 5)
        elif act == "m-":
            s["margin"] = max(0, s["margin"] - 5)
        else:
            s["position"] = act
        DB.save_settings(uid, s_media, s)
        await query.answer()
        await query.edit_message_text("📍 Anchor position & margins:",
                                      reply_markup=position_kb(s_media, s))
        return
    if head == "b":
        act = parts[2]
        if act in ("plain", "box"):
            s["badge"] = act
            s["tiled"] = False
        elif act == "tile":
            s["tiled"] = not s["tiled"]
        elif act == "sp+":
            s["tile_spacing"] = min(400, s["tile_spacing"] + 10)
        elif act == "sp-":
            s["tile_spacing"] = max(10, s["tile_spacing"] - 10)
        DB.save_settings(uid, s_media, s)
        await query.answer()
        await query.edit_message_text("🧊 Badge & effects:", reply_markup=badge_kb(s_media, s))
        return
    if head == "k":
        act = parts[2]
        if act == "stroke":
            s["stroke"] = not s["stroke"]
        elif act == "shadow":
            s["shadow"] = not s["shadow"]
        elif act == "w+":
            s["stroke_width"] = min(12, s["stroke_width"] + 1)
        elif act == "w-":
            s["stroke_width"] = max(1, s["stroke_width"] - 1)
        DB.save_settings(uid, s_media, s)
        await query.answer()
        await query.edit_message_text("⚙️ Stroke & shadow:", reply_markup=stroke_kb(s_media, s))
        return
    if head == "lg":
        act = parts[2]
        if act == "s+":
            s["logo_scale"] = min(90, s["logo_scale"] + 5)
        elif act == "s-":
            s["logo_scale"] = max(5, s["logo_scale"] - 5)
        elif act == "o+":
            s["logo_opacity"] = min(100, s["logo_opacity"] + 5)
        elif act == "o-":
            s["logo_opacity"] = max(5, s["logo_opacity"] - 5)
        elif act == "r0":
            s["logo_rotation"] = 0
        elif act == "r90":
            s["logo_rotation"] = 90
        elif act == "tile":
            s["logo_tiled"] = not s["logo_tiled"]
        elif act == "clear":
            try:
                os.remove(logo_file_for(uid, s_media))
            except OSError:
                pass
            await query.answer("Logo removed.")
        DB.save_settings(uid, s_media, s)
        await query.answer()
        await query.edit_message_text("🖼️ Logo watermark settings:",
                                      reply_markup=logo_kb(s_media, s, uid))
        return

    # ---------------- batch ----------------
    if head == "batch":
        act = parts[1]
        st = get_state(uid)
        if act == "cancel":
            clear_state(uid)
            await query.answer("Batch cancelled.")
            await query.edit_message_text("❌ Batch cancelled.",
                                          reply_markup=kb([[btn("🏠 Back to Start", "nav:main")]]))
            return
        if act == "done":
            if not st or st["kind"] != "batch" or not st["files"]:
                await query.answer("No files collected.", show_alert=True)
                return
            files = st["files"]
            clear_state(uid)
            await query.answer()
            await query.edit_message_text(f"⚡ Processing {len(files)} file(s)…",
                                          parse_mode=ParseMode.HTML)
            await run_batch(update, context, files)
            return
        await query.answer()
        return

    # ---------------- admin callbacks ----------------
    if head == "adm":
        if not is_admin(uid):
            await query.answer("⛔ Access Denied: Admin only command.", show_alert=True)
            return
        act = parts[1]
        if act == "stats":
            await query.answer()
            await query.edit_message_text(_admin_stats_text(), parse_mode=ParseMode.HTML,
                                          reply_markup=admin_kb())
            return
        if act == "clean":
            n = clean_temp_dir(max_age=0)
            await query.answer(f"Removed {n} temp file(s).", show_alert=True)
            await query.edit_message_text(_admin_stats_text(), parse_mode=ParseMode.HTML,
                                          reply_markup=admin_kb())
            return
        if act == "errors":
            rows = [[r["ts"][11:19], str(r["user_id"]), _trunc(r["message"], 34)]
                    for r in DB.recent_errors()]
            txt = ("📜 <b>Recent Errors</b>\n<pre>" +
                   esc(box_table(["Time", "User", "Message"], rows) if rows else "(no errors)") +
                   "</pre>")
            await query.answer()
            await query.edit_message_text(txt, parse_mode=ParseMode.HTML,
                                          reply_markup=kb([[btn("⬅️ Back", "adm:stats")]]))
            return
        if act == "broadcast":
            if not is_admin(uid):
                await query.answer("⛔ Admin only.", show_alert=True)
                return
            set_state(uid, "broadcast")
            await query.answer()
            await query.edit_message_text(
                "📢 Send the message to broadcast to all users:",
                reply_markup=kb([[CANCEL_BTN]]))
            return
        await query.answer()
        return

    if head == "lim":
        if not is_admin(uid):
            await query.answer("⛔ Access Denied: Admin only command.", show_alert=True)
            return
        key, direction = parts[1], parts[2]
        if key == "batch":
            cur = limit_max_batch()
            cur = min(50, cur + 1) if direction == "+" else max(2, cur - 1)
            DB.kv_set("max_batch", str(cur))
        else:
            cur = limit_rate_per_min()
            cur = min(120, cur + 5) if direction == "+" else max(5, cur - 5)
            DB.kv_set("rate_per_min", str(cur))
        await query.answer()
        await query.edit_message_text(_admin_stats_text(), parse_mode=ParseMode.HTML,
                                      reply_markup=admin_kb())
        return

    await query.answer()


async def _show_category(query: Any, uid: int, media: str) -> None:
    s = DB.get_settings(uid, media)
    await query.edit_message_text(category_text(media, s), parse_mode=ParseMode.HTML,
                                  reply_markup=category_kb(media, s))


# --------------------------------------------------------------------------
# Batch runner
# --------------------------------------------------------------------------
async def run_batch(update: Update, context: ContextTypes.DEFAULT_TYPE,
                    files: List[Tuple[str, str]]) -> None:
    """files: list of (file_id, ext). Downloads & processes each, then zips."""
    uid = update.effective_user.id
    chat = update.effective_chat
    assert chat is not None
    results: List[str] = []
    failed = 0
    status = await context.bot.send_message(chat.id, "⚡ Starting batch…")
    loop = asyncio.get_running_loop()
    for i, (file_id, ext) in enumerate(files, 1):
        kind = media_kind_of(ext) or "image"
        s = DB.get_settings(uid, kind)
        try:
            await status.edit_text(f"⚡ Batch {i}/{len(files)} — downloading…")
            file = await _tg_retry(lambda: context.bot.get_file(file_id))
            name = sanitize_filename(f"batch_{i}{ext}")
            path = safe_join(user_temp(uid), name)
            file_size = file.file_size or 0
            if file_size > CFG.max_file_size:
                raise WatermarkError(f"file too large ({human_size(file_size)})")
            try:
                await file.download_to_drive(path)
            except TelegramError as exc:
                detail = str(exc).lower()
                if "too big" in detail or "20 mb" in detail or "file is too big" in detail:
                    raise WatermarkError(
                        "Telegram standard Bot API cannot download this large file. "
                        "Configure TELEGRAM_API_BASE_URL and TELEGRAM_API_FILE_URL.") from exc
                raise
            out_path = safe_join(user_temp(uid), "out_" + name)
            await status.edit_text(f"⚡ Batch {i}/{len(files)} — processing {kind}…")
            if kind == "video":
                ffmpeg = find_ffmpeg()
                if not ffmpeg:
                    raise WatermarkError("FFmpeg missing")
                await process_video_file(path, out_path, s, uid, ffmpeg)
            elif kind == "pdf":
                await asyncio.wait_for(
                    loop.run_in_executor(None, process_pdf_file, path, out_path, s, uid, None),
                    timeout=CFG.process_timeout)
            else:
                await asyncio.wait_for(
                    loop.run_in_executor(None, process_image_file, path, out_path, s, uid),
                    timeout=CFG.process_timeout)
            results.append(out_path)
            DB.bump_stat(uid, kind)
        except Exception as exc:
            failed += 1
            DB.bump_stat(uid, "error")
            DB.log_error(uid, "batch", f"file {i}: {type(exc).__name__}: {exc}")
            LOG.warning("batch file %d failed: %s", i, exc)

    DB.bump_stat(uid, "batch")
    if not results:
        await status.edit_text("⚠️ Batch finished, but every file failed. "
                               "Check that files are supported and under the size limit.")
        return
    if len(results) == 1:
        p = results[0]
        with open(p, "rb") as fh:
            data = fh.read()
        if len(data) <= CFG.upload_limit and (CFG.local_api_base_url or len(data) <= 50 * 1024 * 1024):
            await context.bot.send_document(chat.id, data, filename="watermarked" + os.path.splitext(p)[1],
                                            caption="✅ Batch complete (1 file).")
        else:
            await status.edit_text(
                f"✅ Done, but the result ({human_size(len(data))}) cannot be uploaded with the current "
                "Telegram transport. Configure a self-hosted Bot API server for large files.")
    else:
        zip_path = safe_join(user_temp(uid), f"batch_{uuid.uuid4().hex[:6]}.zip")
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for p in results:
                zf.write(p, os.path.basename(p)[4:])  # strip out_ prefix
        size = os.path.getsize(zip_path)
        if size <= CFG.upload_limit and (CFG.local_api_base_url or size <= 50 * 1024 * 1024):
            with open(zip_path, "rb") as fh:
                await context.bot.send_document(
                    chat.id, fh.read(), filename="watermarked_batch.zip",
                    caption=f"✅ Batch complete: {len(results)} OK, {failed} failed.")
        else:
            await status.edit_text(
                f"✅ {len(results)} files processed, but the ZIP ({human_size(size)}) "
                "exceeds the current Telegram transport upload limit. Configure a self-hosted "
                "Bot API server for large files. Files kept in server temp dir.")
    await status.delete()
    for p in results + ([zip_path] if len(results) > 1 else []):
        try:
            os.remove(p)
        except OSError:
            pass


# --------------------------------------------------------------------------
# Message router (states + menu + files)
# --------------------------------------------------------------------------
async def on_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await gate(update):
        return
    msg = update.message
    assert msg is not None
    uid = update.effective_user.id
    text = (msg.text or "").strip()

    if text in ("☰ Menu", "/menu"):
        await msg.reply_text(main_menu_text(), parse_mode=ParseMode.HTML,
                             reply_markup=main_menu_kb())
        return

    st = get_state(uid)

    # ---------- state-driven inputs ----------
    if st:
        kind = st["kind"]
        if kind == "broadcast":
            if not is_admin(uid):
                clear_state(uid)
                await msg.reply_text("⛔ Access Denied: Admin only command.")
                return
            users = DB.all_user_ids()
            sent = err = 0
            status = await msg.reply_text(f"📢 Broadcasting to {len(users)} users…")
            for target in users:
                try:
                    await context.bot.copy_message(target, msg.chat.id, msg.message_id)
                    sent += 1
                except (BadRequest, TelegramError):
                    err += 1
                except RetryAfter as exc:
                    await asyncio.sleep(exc.retry_after + 0.5)
                    err += 1
                await asyncio.sleep(0.05)
            clear_state(uid)
            await status.edit_text(f"📢 Broadcast done: {sent} sent, {err} failed.")
            return

        if kind.startswith("set_"):
            media = st["media"]
            s = DB.get_settings(uid, media)
            field = kind[4:]
            ok = True
            if field == "text":
                if not text or len(text) > 100:
                    ok = False
                else:
                    s["text"] = text
            elif field == "color":
                try:
                    hex_to_rgb(text)
                    s["color"] = text if text.startswith("#") else "#" + text
                    s["color"] = s["color"].upper()
                except WatermarkError:
                    ok = False
            elif field == "posc":
                m = re.match(r"^\s*(-?\d+)\s*,\s*(-?\d+)\s*$", text)
                if not m:
                    ok = False
                else:
                    s["position"] = "custom"
                    s["custom_x"], s["custom_y"] = int(m.group(1)), int(m.group(2))
            elif field == "rotc":
                if text.lstrip("-").isdigit() and -360 <= int(text) <= 360:
                    s["rotation"] = int(text)
                else:
                    ok = False
            elif field == "pdfpages":
                s["pdf_pages"] = text
            if not ok:
                await msg.reply_text("⚠️ Invalid input, please try again.")
                return
            DB.save_settings(uid, media, s)
            clear_state(uid)
            await msg.reply_text(category_text(media, s), parse_mode=ParseMode.HTML,
                                 reply_markup=category_kb(media, s))
            return

        if kind == "logo":
            if not (msg.photo or (msg.document and msg.document.mime_type
                                  and msg.document.mime_type.startswith("image/"))):
                await msg.reply_text("⚠️ Please send an image file as the logo.")
                return
            media = st["media"]
            try:
                if msg.photo:
                    file = await msg.photo[-1].get_file()
                else:
                    file = await msg.document.get_file()
                if (file.file_size or 0) > 5 * 1024 * 1024:
                    raise WatermarkError("Logo too large (max 5 MB).")
                tmp = safe_join(user_temp(uid), sanitize_filename("logo.png"))
                await file.download_to_drive(tmp)
                with Image.open(tmp) as im:
                    im.convert("RGBA").save(logo_file_for(uid, media), format="PNG")
                os.remove(tmp)
            except WatermarkError as exc:
                await msg.reply_text(f"⚠️ {exc}")
                return
            s = DB.get_settings(uid, media)
            clear_state(uid)
            await msg.reply_text("✅ Logo saved!", reply_markup=logo_kb(media, s, uid))
            return

        if kind == "batch":
            if msg.photo:
                fid, ext = msg.photo[-1].file_id, ".jpg"
            elif msg.video:
                fid, ext = msg.video.file_id, os.path.splitext(msg.video.file_name or ".mp4")[1]
            elif msg.document:
                fid = msg.document.file_id
                ext = os.path.splitext(msg.document.file_name or "")[1]
            else:
                await msg.reply_text("⚠️ Send supported files, or tap ✅ Done.")
                return
            if media_kind_of(ext) is None:
                await msg.reply_text("⚠️ Unsupported file type skipped.")
                return
            if len(st["files"]) >= limit_max_batch():
                await msg.reply_text(f"⚠️ Batch limit reached ({limit_max_batch()}). Tap ✅ Done.")
                return
            st["files"].append((fid, ext))
            await msg.reply_text(f"📥 Added {len(st['files'])}/{limit_max_batch()} — "
                                 "send more or tap ✅ Done.", reply_markup=batch_kb())
            return

        if kind in ("auto", "proc_image", "proc_pdf", "proc_video"):
            expected = {"proc_image": "image", "proc_pdf": "pdf", "proc_video": "video"}.get(kind)
            try:
                path, ext, _size = await download_update_file(update)
            except WatermarkError as exc:
                await msg.reply_text(f"⚠️ {esc(exc)}", parse_mode=ParseMode.HTML)
                return
            except TelegramError:
                LOG.exception("download failed")
                await msg.reply_text(
                    "⚠️ Telegram could not download this file. For videos larger than "
                    "20 MB, configure a self-hosted Bot API server.")
                return
            got = media_kind_of(ext)
            if expected and got != expected:
                os.remove(path)
                await msg.reply_text(f"⚠️ I expected a {expected} file.")
                return
            if user_lock(uid).locked():
                os.remove(path)
                await msg.reply_text("⏳ Please wait for the current file to finish.")
                return
            async with user_lock(uid):
                clear_state(uid)
                await process_and_send(update, context, path, got)
            return

    # ---------- no state: ignore random text politely ----------
    if text:
        await msg.reply_text(
            "🤔 I didn't understand that. Use /start for the menu or /help for a guide.",
            reply_markup=kb([[btn("🏠 Back to Start", "nav:main")]]))
        return


# --------------------------------------------------------------------------
# Global error handler & maintenance job
# --------------------------------------------------------------------------
async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    exc = context.error
    uid = update.effective_user.id if isinstance(update, Update) and update.effective_user else None
    LOG.exception("unhandled update error")
    try:
        DB.log_error(uid, "update", f"{type(exc).__name__}: {exc}")
    except Exception:
        pass
    if isinstance(update, Update) and update.message:
        try:
            await update.message.reply_text(
                "⚠️ An unexpected error occurred. Please try again.")
        except TelegramError:
            pass


async def cleanup_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    removed = await asyncio.get_running_loop().run_in_executor(None, clean_temp_dir)
    if removed:
        LOG.info("cleanup removed %d temp files", removed)


SCAFFOLD_FILES: Dict[str, str] = {
    'requirements.txt': r'''python-telegram-bot[job-queue]>=21.0,<22
Pillow>=10.0
PyMuPDF>=1.24
psutil>=5.9
python-dotenv>=1.0
imageio-ffmpeg>=0.4.9
''',
    '.env.example': r'''# ---- Required -------------------------------------------------------------
# Get it from @BotFather on Telegram (BotFather -> /newbot -> copy token)
BOT_TOKEN=123456789:AAF_replace_with_your_real_token

# Comma-separated Telegram user IDs that may use the admin panel.
# Find your numeric ID via @userinfobot.
ADMIN_IDS=123456789

# ---- Optional (sensible defaults if unset) --------------------------------
# Where the SQLite database lives
DATABASE_PATH=./watermark_bot.db

# Max incoming file size in bytes (default 5 GiB; standard Bot API limits may still apply)
MAX_FILE_SIZE=5368709120
# Optional: self-hosted Telegram Bot API server for large files (5 GB workflows).
# TELEGRAM_API_BASE_URL=http://127.0.0.1:8081/bot
# TELEGRAM_API_FILE_URL=http://127.0.0.1:8081/file/bot
# MAX_UPLOAD_SIZE=5368709120

# Isolated directory for temporary processing files
TEMP_DIRECTORY=./wm_temp

# Path to a specific TTF/OTF font used for watermark text (optional)
FONT_PATH=

# Path to the ffmpeg binary (auto-detected from PATH or imageio-ffmpeg otherwise)
FFMPEG_PATH=

# URL opened by the "Contact Admin for VIP Plan" button
ADMIN_CONTACT_URL=https://t.me/username

# Processing timeouts in seconds
VIDEO_TIMEOUT=900
PROCESS_TIMEOUT=240

# Log file (optional; leave empty for console-only logging)
LOG_FILE=
''',
    'Dockerfile': r'''FROM python:3.11-slim

# FFmpeg + fonts for watermark rendering
RUN apt-get update && apt-get install -y --no-install-recommends \
        ffmpeg fonts-dejavu-core \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY bot.py .

ENV DATABASE_PATH=/data/watermark_bot.db \
    TEMP_DIRECTORY=/data/wm_temp

RUN mkdir -p /data
VOLUME ["/data"]

CMD ["python", "bot.py"]
''',
    'docker-compose.yml': r'''services:
  watermark-bot:
    build: .
    restart: unless-stopped
    env_file:
      - .env
    volumes:
      - bot-data:/data

volumes:
  bot-data:
''',
    'README.md': r'''# Viraj Watermark — Telegram Watermark Bot

Production-ready, single-file Telegram bot (`bot.py`) that adds customizable
watermarks to **images (JPG/JPEG/PNG/WEBP)**, **PDFs** and **videos**, with
batch processing, per-user persistent settings, an admin panel and the exact
inline-button UI flow shown in the reference screenshots
(Watermark Settings Hub → Video/Image/PDF/Global Defaults → per-category
settings table with Turn OFF / Text / Font / Style / Size / Color / Opacity /
Position / Badge & Effects / Stroke & Shadow / Reset / Back).

---

## 1. Architecture overview

```
┌──────────────────────────── bot.py (single file) ───────────────────────────┐
│ Config (env) → Database (SQLite) → UI layer (screens + inline keyboards)    │
│      │                                                                      │
│      ├─ Handlers: /start /settings /mysettings /help /about /cancel         │
│      │            /admin /allow /block /unblock /stats + callback router    │
│      │            + message router (state prompts, files, batches)          │
│      ├─ Engines:  image (Pillow) · pdf (PyMuPDF) · video (FFmpeg overlay)    │
│      │            all render one shared transparent RGBA watermark layer    │
│      ├─ Security: size limits · sanitization · path-traversal guard ·       │
│      │            rate limiting · per-user locks · timeouts · safe exec     │
│      └─ Jobs:     hourly temp cleanup (APScheduler via PTB job_queue)       │
└─────────────────────────────────────────────────────────────────────────────┘
```

* **One shared renderer** (`build_watermark_layer`) draws text/logo watermarks
  (stroke, shadow, badge box, rotation, tiling, opacity) onto a transparent
  full-frame layer. Images composite it with Pillow, PDFs embed it as an
  overlay PNG per page, videos overlay it with a single FFmpeg `overlay`
  filter (audio copied, no re-encoding of audio).
* **Settings**: per user × per media (`global`, `image`, `pdf`, `video`) in
  SQLite; media rows inherit the user's Global Defaults on first use.

### How to split into modules later

| Module            | Extract these sections of bot.py                          |
|-------------------|-----------------------------------------------------------|
| `config.py`       | `Config`, logging setup, constants (`POSITIONS`, defaults) |
| `db.py`           | `Database`, limit helpers                                  |
| `utils.py`        | `serif_bold`, `box_table`, sanitize/size/color/page utils  |
| `fonts.py`        | font scanning + `get_font`                                |
| `render.py`       | layer builder + text/logo tile renderers                  |
| `engines/image.py`, `engines/pdf.py`, `engines/video.py` | the three engines |
| `ui.py`           | keyboards + screen texts                                  |
| `handlers/*.py`   | user / admin / callback / message routers                 |
| `main.py`         | `build_application()` + `main()`                          |

Everything is already organized top-to-bottom in that order, so each section
can be cut into its own file with only `import` lines added.

---

## 2. Requirements

* Python **3.11+**
* **FFmpeg** for video watermarking (see §4)
* `pip install -r requirements.txt`

```
python-telegram-bot[job-queue]>=21.0,<22
Pillow>=10.0
PyMuPDF>=1.24
psutil>=5.9
python-dotenv>=1.0
imageio-ffmpeg>=0.4.9        # bundled static ffmpeg fallback (great on Windows)
```

## 3. Environment configuration

Copy `.env.example` → `.env` and fill in:

| Variable          | Meaning                                             | Default            |
|-------------------|-----------------------------------------------------|--------------------|
| `BOT_TOKEN`       | from @BotFather (**required**)                      | –                  |
| `ADMIN_IDS`       | comma-separated admin user IDs (from @userinfobot)  | –                  |
| `DATABASE_PATH`   | SQLite file location                                | `./watermark_bot.db` |
| `MAX_FILE_SIZE`   | incoming limit in bytes (application limit; standard Bot API transport may still cap downloads)| `5368709120`         |
| `TEMP_DIRECTORY`  | isolated temp dir                                   | `./wm_temp`        |
| `FONT_PATH`       | optional TTF/OTF for watermark text                 | auto-detect        |
| `FFMPEG_PATH`     | optional explicit ffmpeg binary                     | auto-detect        |
| `ADMIN_CONTACT_URL` | target of "Contact Admin for VIP Plan" button     | `https://t.me/`    |
| `VIDEO_TIMEOUT` / `PROCESS_TIMEOUT` | seconds                          | 900 / 240          |

## 4. FFmpeg setup

* **Ubuntu/Debian:** `sudo apt update && sudo apt install ffmpeg`
* **macOS:** `brew install ffmpeg`
* **Windows:** `pip install imageio-ffmpeg` (bot auto-detects it) or download
  a build from ffmpeg.org and set `FFMPEG_PATH`.
* **Docker:** already included in the `Dockerfile`.
* Verify: `ffmpeg -version`. If missing, the bot keeps working for images/PDFs
  and shows a setup hint for video requests.

## 5. Installation

### Linux / VPS
```bash
sudo apt update && sudo apt install -y python3 python3-pip ffmpeg
git clone <your-repo> && cd watermark-bot
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
cp .env.example .env   # edit it
python bot.py
```

### Windows
```powershell
py -3.11 -m venv venv
venv\Scripts\activate
pip install -r requirements.txt
copy .env.example .env   # edit it
python bot.py
```
(FFmpeg via `imageio-ffmpeg` is automatic; no manual install needed.)

### BotFather setup
1. Open `@BotFather` → `/newbot` → choose name *Viraj Watermark* and a username.
2. Copy the token into `BOT_TOKEN`.
3. Optional: `/setcommands` with the command list from the README, and
   `/setuserpic` for a logo. Find your numeric ID with `@userinfobot` for `ADMIN_IDS`.

### Docker / VPS deployment
```bash
cp .env.example .env && nano .env
docker compose up -d --build          # or:
docker build -t viraj-watermark . && docker run -d --env-file .env -v wmdata:/data viraj-watermark
```
For bare-metal persistence use systemd:
```ini
# /etc/systemd/system/viraj-watermark.service
[Unit]
Description=Viraj Watermark Bot
After=network.target
[Service]
WorkingDirectory=/opt/viraj-watermark
EnvironmentFile=/opt/viraj-watermark/.env
ExecStart=/opt/viraj-watermark/.venv/bin/python bot.py
Restart=always
[Install]
WantedBy=multi-user.target
```

## 6. Running & local testing

```bash
python bot.py                 # starts long-polling
python test_bot.py            # 28 offline engine/security/UI tests (no Telegram needed)
python test_integration.py    # handler registration + proves watermark visibility
```

## 7. Feature usage guide

* `/start` — main menu (Add Watermark, Settings, Process Image/PDF/Video, Batch,
  My Settings, Help, About, Contact Admin for VIP).
* `⚙️ Watermark Settings` (`/settings`) — **Watermark Settings Hub**: Video /
  Image / PDF / Global Defaults.
* Category screen shows the live settings table; buttons: 🔴 Turn OFF, ✏️ Text,
  🔤 Font,  Style (bold/italic/rotation), 📏 Size, 🎨 Color (presets + custom
  hex), 💧 Opacity, 📍 Position (9 anchors + custom x,y + margins), 🧊 Badge &
  Effects (plain/box/tile + spacing), ⚙️ Stroke & Shadow, ✍️ Mode (text/logo/both),
  🖼️ Logo (upload/scale/opacity/rotate/tile), 📄 Pages (PDF ranges like `1,3-5`),
  🔄 Reset to Default, ⬅️ Back.
* `/mysettings` — configuration table for Video/Image/PDF.
* **Batch** — send up to N files (admin-configurable, default 10), tap ✅ Done,
  receive a ZIP; individual failures don't kill the batch.
* **Admin** (`/admin`, admin IDs only): users/active/files stats, CPU/RAM/disk,
  uptime, recent errors, broadcast, block/unblock (`/block /unblock /allow`),
  temp cleanup, batch & rate limit tuning. Every admin action re-checks
  authorization server-side.

## 8. Testing instructions

See §6. `test_bot.py` covers: DB init/save/reset, block/unblock, admin auth,
rate limiting, sanitization/path traversal, page-spec & color validation,
image engines (RGB/RGBA/grayscale/palette/WEBP, tiling, logo, rotation, badge,
custom coords), corrupt inputs, encrypted PDFs, PDF page ranges, FFmpeg video
watermarking (text + tiled logo), temp cleanup, and exact keyboard labels from
the screenshots. Live Telegram polling **cannot** be tested without a real
token — deploy and send `/start` to verify.

## 9. Known limitations

* Telegram Bot API caps **downloads at 20 MB** and **uploads at 50 MB** — the
  bot enforces/states this honestly instead of over-promising.
* Video watermarking re-encodes video (H.264/veryfast/CRF 23) to burn the
  overlay in; audio is copied untouched. Rotation/tiling work because the
  watermark is pre-rendered to a transparent PNG frame.
* PDF watermarks are stamped as vector-safe overlay images (no text-layer
  editing), which preserves the original content and works on any PDF.
* Fonts depend on OS-installed fonts (DejaVu/Roboto etc.); set `FONT_PATH`
  for a specific brand font. Color emoji are rendered by the client, not the
  bot.
* Settings/batch state prompts are in-memory (survive per-session, not restarts).

## 10. Security recommendations

* Keep `ADMIN_IDS` minimal; never share the token; rotate it via BotFather if leaked.
* Run as a non-root user / inside the provided Docker image; mount `/data` volume.
* The bot never executes uploaded files, never uses `shell=True`, sanitizes
  names, isolates per-user temp dirs, validates sizes/types, rate-limits,
  locks one concurrent job per user, times out processing, and logs without
  token/file contents.
* For production scale, put a reverse proxy in front only if you switch to
  webhook mode (not included; polling needs no open ports).

## 11. Troubleshooting

| Symptom | Fix |
|---|---|
| `BOT_TOKEN is not set` | create `.env` from `.env.example` |
| `Invalid token` / 401 | re-copy token from BotFather, no spaces |
| Video fails | `ffmpeg -version`; install FFmpeg or `pip install imageio-ffmpeg` |
| `file too large` | Telegram caps at 20 MB incoming for bots |
| Font looks generic | install fonts (`apt install fonts-dejavu-core`) or set `FONT_PATH` |
| PDF "password-protected" | remove password first (safety by design) |
| No admin panel | your numeric ID must be in `ADMIN_IDS` (or `/allow <id>`) |

## 12. Future improvements

Webhook mode, Redis-backed session state, queue worker (Celery/RQ) for heavy
videos, per-channel VIP licensing, caption/metadata watermarking, OCR-proof
invisible watermarks, i18n, and a web admin dashboard.
''',
    'test_bot.py': r'''#!/usr/bin/env python3
"""Offline test harness for bot.py — exercises engines, DB, security helpers,
UI builders. Does NOT connect to Telegram (no token available in CI)."""
import asyncio
import os
import shutil
import sys
import tempfile
import time

BASE = tempfile.mkdtemp(prefix="wmtest_")
os.environ.setdefault("BOT_TOKEN", "123:TEST_TOKEN_NOT_REAL")
os.environ["DATABASE_PATH"] = os.path.join(BASE, "test.db")
os.environ["TEMP_DIRECTORY"] = os.path.join(BASE, "temp")
os.environ["ADMIN_IDS"] = "123"

import bot  # noqa: E402
from bot import (Database, WatermarkError, box_table, build_watermark_layer,  # noqa: E402
                 category_kb, category_text, clean_temp_dir, find_ffmpeg,
                 hex_to_rgb, is_admin, limit_max_batch, logo_file_for,
                 main_menu_kb, my_settings_text, parse_page_spec,
                 process_image_file, process_pdf_file, process_video_file,
                 rate_limited, sanitize_filename, safe_join, serif_bold,
                 settings_hub_kb, my_settings_kb)

from PIL import Image  # noqa: E402
import fitz  # noqa: E402

PASS, FAIL = [], []


def check(name: str, fn):
    try:
        fn()
        PASS.append(name)
        print(f"  ✅ {name}")
    except Exception as exc:  # noqa: BLE001
        FAIL.append((name, exc))
        print(f"  ❌ {name}: {type(exc).__name__}: {exc}")


bot.CFG = bot.Config.from_env()
os.makedirs(bot.CFG.temp_directory, exist_ok=True)
bot.DB = Database(bot.CFG.database_path)
DB = bot.DB
DB.touch_user(1, "tester", "Tester")

S = lambda **kw: {**dict(bot.DEFAULT_SETTINGS), **kw}

# ---------------------------------------------------------------- UI builders
def t_serif():
    assert serif_bold("Global Default Settings").startswith("𝐆")

def t_table():
    out = box_table(["Media", "Status"], [["🎥 Video", "🟢 ON"]])
    assert "┌" in out and "│" in out and "┘" in out

def t_keyboards():
    labels = [b.text for row in main_menu_kb().inline_keyboard for b in row]
    for want in ["➕ Add Watermark", "⚙️ Watermark Settings", "🖼️ Process Image",
                 "📄 Process PDF", "🎥 Process Video", "⚡ Batch Processing",
                 "📊 My Settings", "❓ Help", "ℹ️ About",
                 "🧑‍ Contact Admin for VIP Plan", "🏠 Back to Start"]:
        assert any(want in l for l in labels), f"missing {want}"
    hub = [b.text for row in settings_hub_kb().inline_keyboard for b in row]
    for want in ["🎥 Video Watermark", "🖼️ Image Watermark", "📄 PDF Watermark",
                 "🌐 Global Defaults", "🏠 Back to Main Menu"]:
        assert want in hub, f"missing {want}"
    cat = [b.text for row in category_kb("global", S()).inline_keyboard for b in row]
    for want in ["🔴 Turn OFF", "✏️ Text", "🔤 Font", "✨ Style", "📏 Size", "🎨 Color",
                 "💧 Opacity", "📍 Position", "🧊 Badge & Effects", "⚙️ Stroke & Shadow",
                 "🔄 Reset to Default", "⬅️ Back"]:
        assert want in cat, f"missing {want}"
    my = [b.text for row in my_settings_kb().inline_keyboard for b in row]
    assert "🎥 Video" in my and "🏠 Back to Start" in my

def t_category_text():
    txt = category_text("global", S())
    assert serif_bold("Global Default Settings") in txt
    assert "ENABLED" in txt and "75%" in txt
    assert "Bottom Right" in txt and "Plain Text" in txt

def t_mysettings():
    txt = my_settings_text(1)
    assert serif_bold("My Watermark Configuration") in txt and "Video" in txt

# ---------------------------------------------------------------- security
def t_sanitize():
    assert sanitize_filename("../../etc/passwd") .count("..") == 0
    assert "/" not in sanitize_filename("a/b\\c.png")

def t_safe_join():
    base = os.path.realpath(BASE)
    good = safe_join(base, "x.png")
    assert good.startswith(base)
    try:
        safe_join(base, "../../etc/passwd")
        raise AssertionError("traversal allowed")
    except WatermarkError:
        pass

def t_rate():
    DB.kv_set("rate_per_min", "3")
    assert not rate_limited(999)
    rate_limited(999); rate_limited(999)
    assert rate_limited(999)
    DB.kv_set("rate_per_min", "40")

def t_admin():
    assert is_admin(123) and not is_admin(999)
    DB.kv_set("extra_admins", "456")
    assert is_admin(456)
    DB.kv_set("extra_admins", "")

def t_pages():
    assert parse_page_spec("all", 5) == [0, 1, 2, 3, 4]
    assert parse_page_spec("1,3-4", 5) == [0, 2, 3]
    try:
        parse_page_spec("x", 5)
        raise AssertionError("bad spec accepted")
    except WatermarkError:
        pass

def t_color():
    assert hex_to_rgb("#FFF") == (255, 255, 255)
    try:
        hex_to_rgb("zz")
        raise AssertionError("bad hex accepted")
    except WatermarkError:
        pass

# ---------------------------------------------------------------- DB
def t_db_settings():
    s = DB.get_settings(1, "image")
    assert s["text"] == "@VirajWatermark" and s["opacity"] == 75
    s["font_size"] = 50
    DB.save_settings(1, "image", s)
    assert DB.get_settings(1, "image")["font_size"] == 50
    DB.reset_settings(1, "image")
    assert DB.get_settings(1, "image")["font_size"] == 36
    assert DB.get_settings(1, "global")["font_size"] == 36

def t_db_stats_errors():
    DB.bump_stat(1, "image")
    assert DB.totals()["images"] >= 1
    DB.log_error(1, "test", "boom")
    assert DB.recent_errors()[0]["message"] == "boom"
    tot, week = DB.user_counts()
    assert tot >= 1 and week >= 1

def t_block():
    DB.set_blocked(77, True)
    assert DB.is_blocked(77)
    DB.set_blocked(77, False)
    assert not DB.is_blocked(77)

# ---------------------------------------------------------------- image engine
def _mk_image(path, mode="RGB", fmt=None):
    im = Image.new(mode, (800, 600), (120, 120, 200) if mode == "RGB" else 128)
    if mode == "P":
        im = Image.new("RGB", (800, 600), (10, 200, 30)).convert("P")
    if mode == "RGBA":
        im = Image.new("RGBA", (800, 600), (10, 10, 10, 128))
    im.save(path, format=fmt)

def t_image_rgb_jpg():
    src, dst = os.path.join(BASE, "a.jpg"), os.path.join(BASE, "a_out.jpg")
    _mk_image(src, "RGB", "JPEG")
    process_image_file(src, dst, S(), 1)
    with Image.open(dst) as im:
        assert im.format == "JPEG" and im.size == (800, 600)

def t_image_png_rgba():
    src, dst = os.path.join(BASE, "b.png"), os.path.join(BASE, "b_out.png")
    _mk_image(src, "RGBA")
    process_image_file(src, dst, S(tiled=True), 1)
    with Image.open(dst) as im:
        assert im.mode == "RGBA"

def t_image_gray_palette_webp():
    for mode, ext in [("L", ".png"), ("P", ".png")]:
        src, dst = os.path.join(BASE, f"g{ext}"), os.path.join(BASE, f"g_out{ext}")
        _mk_image(src, mode)
        process_image_file(src, dst, S(rotation=45, badge="box"), 1)
        assert os.path.getsize(dst) > 0
    src, dst = os.path.join(BASE, "w.webp"), os.path.join(BASE, "w_out.webp")
    _mk_image(src, "RGB", "WEBP")
    process_image_file(src, dst, S(position="custom", custom_x=5, custom_y=5), 1)
    with Image.open(dst) as im:
        assert im.format == "WEBP"

def t_image_logo():
    logo = logo_file_for(1, "image")
    Image.new("RGBA", (100, 60), (255, 0, 0, 200)).save(logo, "PNG")
    src, dst = os.path.join(BASE, "l.png"), os.path.join(BASE, "l_out.png")
    _mk_image(src, "RGB")
    process_image_file(src, dst, S(mode="both", logo_tiled=True), 1)
    assert os.path.getsize(dst) > 0

def t_image_corrupt():
    src = os.path.join(BASE, "bad.png")
    with open(src, "wb") as fh:
        fh.write(b"not an image at all")
    try:
        process_image_file(src, os.path.join(BASE, "bad_out.png"), S(), 1)
        raise AssertionError("corrupt image accepted")
    except WatermarkError:
        pass

def t_layer_build():
    layer = build_watermark_layer((640, 480), S(stroke=True, shadow=True), None, 1.0)
    assert layer.mode == "RGBA" and layer.size == (640, 480)
    assert layer.getbbox() is not None  # something was drawn

# ---------------------------------------------------------------- pdf engine
def _mk_pdf(path, pages=3, password=None):
    doc = fitz.open()
    for i in range(pages):
        page = doc.new_page(width=595, height=842)
        page.insert_text((72, 72), f"page {i+1}")
    if password:
        doc.save(path, encryption=fitz.PDF_ENCRYPT_AES_256,
                 user_pw=password, owner_pw=password)
    else:
        doc.save(path)
    doc.close()

def t_pdf_all():
    src, dst = os.path.join(BASE, "d.pdf"), os.path.join(BASE, "d_out.pdf")
    _mk_pdf(src)
    n = process_pdf_file(src, dst, S(), 1)
    assert n == 3
    doc = fitz.open(dst)
    assert doc.page_count == 3 and not doc.is_encrypted
    doc.close()

def t_pdf_range():
    src, dst = os.path.join(BASE, "e.pdf"), os.path.join(BASE, "e_out.pdf")
    _mk_pdf(src)
    process_pdf_file(src, dst, S(pdf_pages="2"), 1)
    assert os.path.getsize(dst) > 0

def t_pdf_encrypted():
    src = os.path.join(BASE, "enc.pdf")
    _mk_pdf(src, password="secret")
    try:
        process_pdf_file(src, os.path.join(BASE, "enc_out.pdf"), S(), 1)
        raise AssertionError("encrypted pdf accepted")
    except WatermarkError:
        pass

def t_pdf_corrupt():
    src = os.path.join(BASE, "bad.pdf")
    with open(src, "wb") as fh:
        fh.write(b"%PDF-garbage")
    try:
        process_pdf_file(src, os.path.join(BASE, "bad_out.pdf"), S(), 1)
        raise AssertionError("corrupt pdf accepted")
    except WatermarkError:
        pass

# ---------------------------------------------------------------- video engine
def t_video():
    ffmpeg = find_ffmpeg()
    assert ffmpeg, "ffmpeg not found"
    src, dst = os.path.join(BASE, "v.mp4"), os.path.join(BASE, "v_out.mp4")
    import subprocess
    subprocess.run([ffmpeg, "-y", "-f", "lavfi", "-i",
                    "testsrc=duration=2:size=320x240:rate=15",
                    "-c:v", "libx264", "-pix_fmt", "yuv420p", src],
                   check=True, capture_output=True)
    asyncio.run(process_video_file(src, dst, S(), 1, ffmpeg))
    assert os.path.getsize(dst) > 0

def t_video_tiled_logo():
    ffmpeg = find_ffmpeg()
    src, dst = os.path.join(BASE, "v2.mp4"), os.path.join(BASE, "v2_out.mp4")
    import subprocess
    subprocess.run([ffmpeg, "-y", "-f", "lavfi", "-i",
                    "testsrc=duration=1:size=320x240:rate=15",
                    "-c:v", "libx264", "-pix_fmt", "yuv420p", src],
                   check=True, capture_output=True)
    logo = logo_file_for(1, "video")
    Image.new("RGBA", (60, 40), (0, 255, 0, 180)).save(logo, "PNG")
    asyncio.run(process_video_file(src, dst, S(mode="logo", tiled=True), 1, ffmpeg))
    assert os.path.getsize(dst) > 0

# ---------------------------------------------------------------- temp cleanup
def t_cleanup():
    d = os.path.join(bot.CFG.temp_directory, "1")
    os.makedirs(d, exist_ok=True)
    old = os.path.join(d, "old.txt")
    with open(old, "w") as fh:
        fh.write("x")
    os.utime(old, (time.time() - 7200, time.time() - 7200))
    new = os.path.join(d, "new.txt")
    with open(new, "w") as fh:
        fh.write("x")
    n = clean_temp_dir(max_age=3600)
    assert n >= 1 and not os.path.exists(old) and os.path.exists(new)
    clean_temp_dir(max_age=0)
    assert not os.path.exists(new)

def t_limits():
    assert limit_max_batch() == 10

TESTS = [
    ("serif_bold header styling", t_serif),
    ("box_table grid rendering", t_table),
    ("keyboards match screenshot labels", t_keyboards),
    ("category settings panel text", t_category_text),
    ("my settings panel text", t_mysettings),
    ("filename sanitization", t_sanitize),
    ("path traversal protection", t_safe_join),
    ("rate limiter", t_rate),
    ("admin authorization", t_admin),
    ("page range parsing", t_pages),
    ("hex color validation", t_color),
    ("sqlite settings save/reset", t_db_settings),
    ("sqlite stats & error log", t_db_stats_errors),
    ("block / unblock", t_block),
    ("image watermark JPEG/RGB", t_image_rgb_jpg),
    ("image watermark PNG/RGBA tiled", t_image_png_rgba),
    ("image watermark gray/palette/webp/custom", t_image_gray_palette_webp),
    ("image watermark logo + both + tile", t_image_logo),
    ("corrupt image rejected", t_image_corrupt),
    ("watermark layer builder", t_layer_build),
    ("pdf watermark all pages", t_pdf_all),
    ("pdf watermark page range", t_pdf_range),
    ("encrypted pdf rejected", t_pdf_encrypted),
    ("corrupt pdf rejected", t_pdf_corrupt),
    ("video watermark via ffmpeg", t_video),
    ("video logo watermark tiled", t_video_tiled_logo),
    ("temp cleanup old files", t_cleanup),
    ("default batch limit", t_limits),
]

print("== Viraj Watermark offline test harness ==")
for name, fn in TESTS:
    check(name, fn)

print(f"\n{len(PASS)} passed, {len(FAIL)} failed")
if FAIL:
    for name, exc in FAIL:
        print(f"  FAILED: {name}: {exc}")
    sys.exit(1)
shutil.rmtree(BASE, ignore_errors=True)
print("ALL TESTS PASSED")
''',
    'test_integration.py': r'''#!/usr/bin/env python3
"""Integration-level verification: handler registration, config validation,
and proof that outputs actually contain the watermark."""
import asyncio
import os
import subprocess
import sys
import tempfile

BASE = tempfile.mkdtemp(prefix="wmint_")
os.environ.setdefault("BOT_TOKEN", "123:TEST_TOKEN_NOT_REAL")
os.environ["DATABASE_PATH"] = os.path.join(BASE, "test.db")
os.environ["TEMP_DIRECTORY"] = os.path.join(BASE, "temp")
os.environ["ADMIN_IDS"] = "123"

import bot
from PIL import Image
import fitz

ok = True

# 1) missing token -> clean SystemExit with instructions
os.environ.pop("BOT_TOKEN")
try:
    bot.Config.from_env()
    print("❌ missing token did not exit"); ok = False
except SystemExit as e:
    print("✅ missing BOT_TOKEN exits with setup instructions" if "BOT_TOKEN" in str(e) else "❌ bad message")
os.environ["BOT_TOKEN"] = "123:TEST_TOKEN_NOT_REAL"

bot.CFG = bot.Config.from_env()
os.makedirs(bot.CFG.temp_directory, exist_ok=True)
bot.DB = bot.Database(bot.CFG.database_path)

# 2) application builds and all handlers are registered
app = bot.build_application()
kinds = [type(h).__name__ for hs in app.handlers.values() for h in hs]
print(f"✅ application built; handlers registered: {len(kinds)} -> {sorted(set(kinds))}")
cmds = []
for hs in app.handlers.values():
    for h in hs:
        if type(h).__name__ == "CommandHandler":
            cmds += list(h.commands)
missing = {"start", "help", "about", "settings", "mysettings", "cancel",
           "allow", "block", "unblock", "admin", "stats"} - set(cmds)
if missing:
    print("❌ missing commands:", missing); ok = False
else:
    print("✅ all commands registered:", sorted(cmds))
if app.job_queue is None:
    print("❌ job queue unavailable"); ok = False
else:
    print("✅ hourly temp-cleanup job scheduled")

S = lambda **kw: {**dict(bot.DEFAULT_SETTINGS), **kw}

# 3) image output actually differs (watermark visible)
src = os.path.join(BASE, "src.png"); dst = os.path.join(BASE, "dst.png")
Image.new("RGB", (800, 600), (30, 30, 30)).save(src)
bot.process_image_file(src, dst, S(), 1)
a = Image.open(src).convert("RGB"); b = Image.open(dst).convert("RGB")
diff = sum(1 for pa, pb in zip(a.getdata(), b.getdata()) if pa != pb)
print(f"✅ watermarked image differs in {diff} pixels" if diff > 500 else f"❌ watermark invisible ({diff}px)")
ok = ok and diff > 500

# 4) PDF output actually contains an inserted watermark image on every page
psrc = os.path.join(BASE, "s.pdf"); pdst = os.path.join(BASE, "s_out.pdf")
doc = fitz.open()
for _ in range(2):
    doc.new_page()
doc.save(psrc); doc.close()
bot.process_pdf_file(psrc, pdst, S(), 1)
doc = fitz.open(pdst)
imgs = [len(p.get_images()) for p in doc]
doc.close()
print(f"✅ pdf pages contain watermark image: {imgs}" if imgs == [1, 1] else f"❌ pdf watermark missing: {imgs}")
ok = ok and imgs == [1, 1]

# 5) video frame actually differs after overlay
ffmpeg = bot.find_ffmpeg()
vsrc = os.path.join(BASE, "v.mp4"); vdst = os.path.join(BASE, "v_out.mp4")
subprocess.run([ffmpeg, "-y", "-f", "lavfi", "-i", "testsrc=duration=1:size=320x240:rate=10",
                "-c:v", "libx264", "-pix_fmt", "yuv420p", vsrc], check=True, capture_output=True)
asyncio.run(bot.process_video_file(vsrc, vdst, S(), 1, ffmpeg))
fa, fb = os.path.join(BASE, "fa.png"), os.path.join(BASE, "fb.png")
for out, vid in ((fa, vsrc), (fb, vdst)):
    subprocess.run([ffmpeg, "-y", "-i", vid, "-frames:v", "1", "-vf", "select=eq(n\\,8)", out],
                   check=True, capture_output=True)
ia, ib = Image.open(fa).convert("RGB"), Image.open(fb).convert("RGB")
vdiff = sum(1 for pa, pb in zip(ia.getdata(), ib.getdata()) if pa != pb)
print(f"✅ watermarked video frame differs in {vdiff} pixels" if vdiff > 500 else f"❌ video watermark invisible ({vdiff}px)")
ok = ok and vdiff > 500

print("INTEGRATION:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
''',
}


# --------------------------------------------------------------------------
# Optional in-process Local Bot API Server launcher
# --------------------------------------------------------------------------
LOCAL_BOT_API_PROCESS: Optional[subprocess.Popen] = None


def _start_local_bot_api_if_available() -> bool:
    """Start Telegram's Local Bot API Server from this same Python file.

    Set AUTO_START_LOCAL_BOT_API=0 to disable automatic startup.
    The executable must already be installed as `telegram-bot-api`.
    """
    global LOCAL_BOT_API_PROCESS, CFG

    auto = os.getenv("AUTO_START_LOCAL_BOT_API", "1").strip().lower()
    if auto in {"0", "false", "no", "off"}:
        return False

    # Respect an explicitly configured endpoint; do not start a second server.
    if os.getenv("TELEGRAM_API_BASE_URL", "").strip():
        LOG.info("Using externally configured Telegram Bot API endpoint")
        return True

    executable = shutil.which("telegram-bot-api")
    if not executable:
        LOG.warning(
            "telegram-bot-api was not found. Continuing with the standard Telegram API; "
            "large-file downloads will still be limited."
        )
        return False

    port = int(os.getenv("TELEGRAM_LOCAL_API_PORT", "8081"))
    command = [
        executable,
        "--api-id", str(CFG.telegram_api_id),
        "--api-hash", CFG.telegram_api_hash,
        "--local",
        "--http-port", str(port),
    ]

    try:
        LOCAL_BOT_API_PROCESS = subprocess.Popen(
            command,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        time.sleep(1.0)
        if LOCAL_BOT_API_PROCESS.poll() is not None:
            LOG.warning(
                "Local Bot API Server exited immediately (code=%s). "
                "Continuing with the standard API.",
                LOCAL_BOT_API_PROCESS.returncode,
            )
            LOCAL_BOT_API_PROCESS = None
            return False

        CFG.local_api_base_url = f"http://127.0.0.1:{port}/bot"
        CFG.local_api_file_url = f"http://127.0.0.1:{port}/file/bot"
        LOG.info("Started Local Telegram Bot API Server on port %s", port)
        return True
    except Exception as exc:  # noqa: BLE001
        LOG.warning("Could not start Local Bot API Server: %s", exc)
        LOCAL_BOT_API_PROCESS = None
        return False


def _stop_local_bot_api() -> None:
    global LOCAL_BOT_API_PROCESS
    proc = LOCAL_BOT_API_PROCESS
    LOCAL_BOT_API_PROCESS = None
    if proc is None or proc.poll() is not None:
        return
    try:
        proc.terminate()
        proc.wait(timeout=5)
        LOG.info("Stopped Local Telegram Bot API Server")
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait(timeout=5)
    except Exception as exc:  # noqa: BLE001
        LOG.warning("Could not stop Local Bot API Server cleanly: %s", exc)


# --------------------------------------------------------------------------
# Application bootstrap
# --------------------------------------------------------------------------
async def post_init(application: Application) -> None:
    await application.bot.set_my_commands([
        BotCommand("start", "Main menu"),
        BotCommand("settings", "Watermark settings hub"),
        BotCommand("mysettings", "View my configuration"),
        BotCommand("help", "Help & guide"),
        BotCommand("about", "About this bot"),
        BotCommand("cancel", "Cancel current action"),
        BotCommand("admin", "Admin panel"),
        BotCommand("allow", "Admin: grant admin rights"),
        BotCommand("block", "Admin: block a user"),
        BotCommand("unblock", "Admin: unblock a user"),
    ])


def build_application() -> Application:
    builder = Application.builder().token(CFG.bot_token).concurrent_updates(True).post_init(post_init)
    # A self-hosted Bot API server is required for genuinely large files.
    if CFG.local_api_base_url:
        builder = builder.base_url(CFG.local_api_base_url)
        if CFG.local_api_file_url:
            builder = builder.base_file_url(CFG.local_api_file_url)
        LOG.info("Using configured local Telegram Bot API endpoint")
    application = builder.build()
    application.add_handler(CommandHandler("start", cmd_start))
    application.add_handler(CommandHandler("menu", cmd_start))
    application.add_handler(CommandHandler("help", cmd_help))
    application.add_handler(CommandHandler("about", cmd_about))
    application.add_handler(CommandHandler("settings", cmd_settings))
    application.add_handler(CommandHandler("mysettings", cmd_mysettings))
    application.add_handler(CommandHandler("cancel", cmd_cancel))
    application.add_handler(CommandHandler("allow", cmd_allow))
    application.add_handler(CommandHandler("block", cmd_block))
    application.add_handler(CommandHandler("unblock", cmd_unblock))
    application.add_handler(CommandHandler("admin", cmd_admin))
    application.add_handler(CommandHandler("stats", cmd_stats))
    application.add_handler(CallbackQueryHandler(on_callback))
    application.add_handler(MessageHandler(filters.ALL & ~filters.COMMAND, on_message))
    application.add_error_handler(on_error)
    if application.job_queue is not None:
        application.job_queue.run_repeating(cleanup_job, interval=3600, first=30)
    return application


def cmd_scaffold() -> None:
    """Write the embedded auxiliary project files next to bot.py.

    bot.py is fully self-contained: requirements.txt, .env.example, Dockerfile,
    docker-compose.yml, README.md and the offline test suites are stored inside
    SCAFFOLD_FILES and can be materialized with:  python bot.py --scaffold
    """
    base = Path(__file__).resolve().parent
    for name, content in SCAFFOLD_FILES.items():
        target = base / name
        target.write_text(content, encoding="utf-8")
        print(f"wrote {target}")


def run_selftest() -> None:
    """Built-in offline verification (no Telegram token needed).

    Exercises the DB, security helpers, UI builders and all three engines.
    Run with:  python bot.py --selftest
    """
    import subprocess
    import tempfile as _tf

    global CFG, DB
    base = _tf.mkdtemp(prefix="wmself_")
    CFG = Config(
        bot_token="SELFTEST", admin_ids=[1],
        database_path=os.path.join(base, "t.db"),
        max_file_size=20 * 1024 * 1024,
        temp_directory=os.path.join(base, "tmp"),
        font_path="", ffmpeg_path="", admin_contact_url="https://t.me/",
        video_timeout=180, process_timeout=120, local_api_base_url="",
        local_api_file_url="", telegram_api_id=36421171,
        telegram_api_hash="069627fa19eb45a775ce87939f1768c5",
        upload_limit=5 * 1024 * 1024 * 1024,
    )
    os.makedirs(CFG.temp_directory, exist_ok=True)
    DB = Database(CFG.database_path)
    DB.touch_user(1, "self", "Self")
    passed = failed = 0

    def check(name: str, fn: Callable[[], None]) -> None:
        nonlocal passed, failed
        try:
            fn()
            passed += 1
            print(f"  ✅ {name}")
        except Exception as exc:  # noqa: BLE001
            failed += 1
            print(f"  ❌ {name}: {type(exc).__name__}: {exc}")

    S = lambda **kw: {**DEFAULT_SETTINGS, **kw}  # noqa: E731

    def ui():
        labels = [b.text for row in main_menu_kb().inline_keyboard for b in row]
        assert "➕ Add Watermark" in labels and "🏠 Back to Start" in labels
        hub = [b.text for row in settings_hub_kb().inline_keyboard for b in row]
        assert "🌐 Global Defaults" in hub and "🏠 Back to Main Menu" in hub
        cat = [b.text for row in category_kb("global", S()).inline_keyboard for b in row]
        assert "🔴 Turn OFF" in cat and "⚙️ Stroke & Shadow" in cat
        assert serif_bold("Global Default Settings") in category_text("global", S())

    def sec():
        assert "/" not in sanitize_filename("../../etc/passwd")
        try:
            safe_join(os.path.realpath(base), "../../etc/passwd")
            raise AssertionError("traversal allowed")
        except WatermarkError:
            pass
        assert parse_page_spec("1,3-5", 6) == [0, 2, 3, 4]
        assert hex_to_rgb("#FFF") == (255, 255, 255)
        assert is_admin(1) and not is_admin(2)

    def db():
        s = DB.get_settings(1, "image")
        s["font_size"] = 50
        DB.save_settings(1, "image", s)
        assert DB.get_settings(1, "image")["font_size"] == 50
        DB.reset_settings(1, "image")
        assert DB.get_settings(1, "image")["font_size"] == 36
        DB.bump_stat(1, "image")
        DB.log_error(1, "self", "boom")
        assert DB.recent_errors()[0]["message"] == "boom"
        DB.set_blocked(9, True)
        assert DB.is_blocked(9)
        DB.set_blocked(9, False)

    def img():
        src, dst = os.path.join(base, "a.jpg"), os.path.join(base, "a_out.jpg")
        Image.new("RGB", (800, 600), (30, 30, 30)).save(src, "JPEG")
        process_image_file(src, dst, S(), 1)
        with Image.open(dst) as im:
            assert im.format == "JPEG"
        a = Image.open(src).convert("RGB")
        b = Image.open(dst).convert("RGB")
        assert sum(1 for x, y in zip(a.getdata(), b.getdata()) if x != y) > 500
        bad = os.path.join(base, "bad.png")
        open(bad, "wb").write(b"junk")
        try:
            process_image_file(bad, os.path.join(base, "bad_out.png"), S(), 1)
            raise AssertionError("corrupt accepted")
        except WatermarkError:
            pass

    def pdf():
        src, dst = os.path.join(base, "d.pdf"), os.path.join(base, "d_out.pdf")
        doc = fitz.open()
        doc.new_page()
        doc.new_page()
        doc.save(src)
        doc.close()
        process_pdf_file(src, dst, S(), 1)
        doc = fitz.open(dst)
        assert doc.page_count == 2 and all(len(p.get_images()) == 1 for p in doc)
        doc.close()
        enc = os.path.join(base, "enc.pdf")
        d2 = fitz.open()
        d2.new_page()
        d2.save(enc, encryption=fitz.PDF_ENCRYPT_AES_256, user_pw="x", owner_pw="x")
        d2.close()
        try:
            process_pdf_file(enc, os.path.join(base, "enc_out.pdf"), S(), 1)
            raise AssertionError("encrypted accepted")
        except WatermarkError:
            pass

    def video():
        ffmpeg = find_ffmpeg()
        if not ffmpeg:
            print("  ⚠️ ffmpeg not found — video engine check skipped")
            return
        src, dst = os.path.join(base, "v.mp4"), os.path.join(base, "v_out.mp4")
        subprocess.run([ffmpeg, "-y", "-f", "lavfi", "-i",
                        "testsrc=duration=1:size=320x240:rate=10",
                        "-c:v", "libx264", "-pix_fmt", "yuv420p", src],
                       check=True, capture_output=True)
        asyncio.run(process_video_file(src, dst, S(), 1, ffmpeg))
        assert os.path.getsize(dst) > 0

    def clean():
        d = os.path.join(CFG.temp_directory, "1")
        os.makedirs(d, exist_ok=True)
        old = os.path.join(d, "old.txt")
        open(old, "w").write("x")
        os.utime(old, (time.time() - 7200,) * 2)
        assert clean_temp_dir(3600) >= 1 and not os.path.exists(old)

    print("== Viraj Watermark built-in selftest ==")
    check("UI keyboards & panels", ui)
    check("security helpers", sec)
    check("database layer", db)
    check("image engine", img)
    check("pdf engine", pdf)
    check("video engine", video)
    check("temp cleanup", clean)
    print(f"{passed} passed, {failed} failed")
    sys.exit(1 if failed else 0)


def main() -> None:
    global CFG, DB
    if "--scaffold" in sys.argv[1:]:
        cmd_scaffold()
        return
    if "--selftest" in sys.argv[1:]:
        run_selftest()
    _setup_logging()
    CFG = Config.from_env()
    os.makedirs(CFG.temp_directory, exist_ok=True)
    DB = Database(CFG.database_path)
    clean_temp_dir(max_age=0)

    ffmpeg = find_ffmpeg()
    if ffmpeg:
        LOG.info("FFmpeg found: %s", ffmpeg)
    else:
        LOG.warning("FFmpeg NOT found. Video watermarking disabled. %s",
                    "Install: apt install ffmpeg / brew install ffmpeg / pip install imageio-ffmpeg")

    # Automatically start the Local Bot API Server in this same file when available.
    # This removes the need for a separate launcher script.
    _start_local_bot_api_if_available()

    LOG.info("Starting Viraj Watermark bot…")
    application = build_application()
    try:
        application.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)
    finally:
        _stop_local_bot_api()


if __name__ == "__main__":
    main()
