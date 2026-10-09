"""
Rus shashkasi (русские шашки) — kombinatsiyalar va masalalar.
Telegram bot (aiogram 3.x) + WebApp serveri (aiohttp) + SQLite.

Ishga tushirish:
    pip install -r requirements.txt
    export BOT_TOKEN="123456:ABC..."
    export WEBAPP_URL="https://sizning-domen.uz"     # HTTPS majburiy!
    python bot.py

Mahalliy sinov (brauzerda, Telegramsiz):
    DEV_MODE=1 python bot.py   ->  http://localhost:8080
"""
import asyncio
import hashlib
import hmac
import html
import json
import logging
import os
import sqlite3
import time
from contextlib import contextmanager
from pathlib import Path
from urllib.parse import parse_qsl

from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramBadRequest
from aiogram.filters import CommandStart
from aiogram.types import (
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    MenuButtonWebApp,
    Message,
    ReplyKeyboardMarkup,
    WebAppInfo,
)
from aiohttp import web

# --------------------------------------------------------------------------
# SOZLAMALAR
# --------------------------------------------------------------------------
BASE_DIR = Path(__file__).resolve().parent
BOT_TOKEN = "8631217713:AAHW58BCjzNvcO9tYJWNzZJfN0lggvmf_48"
WEBAPP_URL = "https://reconvene-overload-helping.ngrok-free.dev"
PORT = int(os.getenv("PORT", "8080"))
DB_PATH = os.getenv("DB_PATH", str(BASE_DIR / "shashka.db"))
DEV_MODE = os.getenv("DEV_MODE", "0") == "1"
INIT_DATA_MAX_AGE = 24 * 3600  # initData necha soniya amal qiladi

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("shashka")

BTN_PUZZLES = "🧩 Masalalar yechish (WebApp)"
BTN_LESSONS = "📚 Darslar"
BTN_RATING = "🏆 Reyting"
BTN_PROFILE = "👤 Profil"


# --------------------------------------------------------------------------
# MA'LUMOTLAR BAZASI (SQLite)
# --------------------------------------------------------------------------
@contextmanager
def db():
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def init_db() -> None:
    with db() as conn:
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS Users (
                user_id    INTEGER PRIMARY KEY,
                username   TEXT,
                full_name  TEXT,
                xp         INTEGER NOT NULL DEFAULT 0,
                created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
            );
            CREATE TABLE IF NOT EXISTS Puzzles (
                id         INTEGER PRIMARY KEY,
                title      TEXT NOT NULL,
                difficulty TEXT NOT NULL DEFAULT 'Oson',
                xp         INTEGER NOT NULL DEFAULT 10,
                data       TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS UserProgress (
                user_id   INTEGER NOT NULL,
                puzzle_id INTEGER NOT NULL,
                solved    INTEGER NOT NULL DEFAULT 0,
                attempts  INTEGER NOT NULL DEFAULT 0,
                mistakes  INTEGER NOT NULL DEFAULT 0,
                xp_earned INTEGER NOT NULL DEFAULT 0,
                solved_at TEXT,
                PRIMARY KEY (user_id, puzzle_id),
                FOREIGN KEY (user_id)   REFERENCES Users(user_id),
                FOREIGN KEY (puzzle_id) REFERENCES Puzzles(id)
            );
            """
        )


def seed_puzzles() -> None:
    """puzzles.json dagi masalalarni bazaga yuklaydi (mavjudlarini yangilaydi)."""
    path = BASE_DIR / "puzzles.json"
    puzzles = json.loads(path.read_text(encoding="utf-8"))
    with db() as conn:
        for p in puzzles:
            conn.execute(
                """
                INSERT INTO Puzzles (id, title, difficulty, xp, data)
                VALUES (?, ?, ?, ?, ?)
                ON CONFLICT(id) DO UPDATE SET
                    title = excluded.title,
                    difficulty = excluded.difficulty,
                    xp = excluded.xp,
                    data = excluded.data
                """,
                (
                    int(p["id"]),
                    p["title"],
                    p.get("difficulty", "Oson"),
                    int(p.get("xp", 10)),
                    json.dumps(p, ensure_ascii=False),
                ),
            )
    log.info("%d ta masala yuklandi", len(puzzles))


def upsert_user(user_id: int, username: str | None, full_name: str | None) -> None:
    with db() as conn:
        conn.execute(
            """
            INSERT INTO Users (user_id, username, full_name) VALUES (?, ?, ?)
            ON CONFLICT(user_id) DO UPDATE SET
                username = excluded.username,
                full_name = excluded.full_name
            """,
            (user_id, username, full_name),
        )


def get_stats(user_id: int) -> dict:
    with db() as conn:
        u = conn.execute("SELECT xp FROM Users WHERE user_id = ?", (user_id,)).fetchone()
        solved = conn.execute(
            "SELECT COUNT(*) AS n FROM UserProgress WHERE user_id = ? AND solved = 1", (user_id,)
        ).fetchone()["n"]
        total = conn.execute("SELECT COUNT(*) AS n FROM Puzzles").fetchone()["n"]
        rank = None
        if u is not None:
            rank = conn.execute(
                "SELECT COUNT(*) + 1 AS r FROM Users WHERE xp > ?", (u["xp"],)
            ).fetchone()["r"]
    return {"xp": u["xp"] if u else 0, "solved": solved, "total": total, "rank": rank}


def get_puzzle_row(puzzle_id: int):
    with db() as conn:
        return conn.execute("SELECT * FROM Puzzles WHERE id = ?", (puzzle_id,)).fetchone()


def get_next_puzzle_row(user_id: int):
    with db() as conn:
        return conn.execute(
            """
            SELECT p.* FROM Puzzles p
            LEFT JOIN UserProgress up ON up.puzzle_id = p.id AND up.user_id = ?
            WHERE COALESCE(up.solved, 0) = 0
            ORDER BY p.id LIMIT 1
            """,
            (user_id,),
        ).fetchone()


def list_puzzles(user_id: int) -> list[dict]:
    with db() as conn:
        rows = conn.execute(
            """
            SELECT p.id, p.title, p.difficulty, p.xp, COALESCE(up.solved, 0) AS solved
            FROM Puzzles p
            LEFT JOIN UserProgress up ON up.puzzle_id = p.id AND up.user_id = ?
            ORDER BY p.id
            """,
            (user_id,),
        ).fetchall()
    return [dict(r) for r in rows]


def record_solve(user_id: int, puzzle_id: int, mistakes: int) -> dict | None:
    """Masala yechilganini yozadi va XP beradi (har bir masala uchun faqat bir marta)."""
    with db() as conn:
        pz = conn.execute("SELECT xp FROM Puzzles WHERE id = ?", (puzzle_id,)).fetchone()
        if pz is None:
            return None
        prog = conn.execute(
            "SELECT solved FROM UserProgress WHERE user_id = ? AND puzzle_id = ?",
            (user_id, puzzle_id),
        ).fetchone()
        if prog and prog["solved"]:
            total = conn.execute("SELECT xp FROM Users WHERE user_id = ?", (user_id,)).fetchone()["xp"]
            return {"awarded": 0, "already_solved": True, "total_xp": total}

        base = pz["xp"]
        awarded = max(base // 2, base - 2 * mistakes)  # har xato -2 XP, lekin kamida yarmi
        conn.execute(
            """
            INSERT INTO UserProgress (user_id, puzzle_id, solved, attempts, mistakes, xp_earned, solved_at)
            VALUES (?, ?, 1, 1, ?, ?, CURRENT_TIMESTAMP)
            ON CONFLICT(user_id, puzzle_id) DO UPDATE SET
                solved = 1,
                attempts = attempts + 1,
                mistakes = excluded.mistakes,
                xp_earned = excluded.xp_earned,
                solved_at = CURRENT_TIMESTAMP
            """,
            (user_id, puzzle_id, mistakes, awarded),
        )
        conn.execute("UPDATE Users SET xp = xp + ? WHERE user_id = ?", (awarded, user_id))
        total = conn.execute("SELECT xp FROM Users WHERE user_id = ?", (user_id,)).fetchone()["xp"]
    return {"awarded": awarded, "already_solved": False, "total_xp": total}


def leaderboard(limit: int = 10) -> list[dict]:
    with db() as conn:
        rows = conn.execute(
            """
            SELECT u.user_id, u.username, u.full_name, u.xp,
                   (SELECT COUNT(*) FROM UserProgress up
                    WHERE up.user_id = u.user_id AND up.solved = 1) AS solved
            FROM Users u
            WHERE u.xp > 0
            ORDER BY u.xp DESC, u.user_id ASC
            LIMIT ?
            """,
            (limit,),
        ).fetchall()
    return [dict(r) for r in rows]


# --------------------------------------------------------------------------
# TELEGRAM initData TEKSHIRUVI (WebApp foydalanuvchisini aniqlash)
# --------------------------------------------------------------------------
def verify_init_data(init_data: str) -> dict | None:
    """Telegram WebApp initData imzosini tekshiradi. To'g'ri bo'lsa user dict qaytaradi."""
    if not init_data or not BOT_TOKEN:
        return None
    try:
        parsed = dict(parse_qsl(init_data, keep_blank_values=True, strict_parsing=True))
    except ValueError:
        return None
    received_hash = parsed.pop("hash", None)
    if not received_hash:
        return None
    check_string = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
    secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
    calc = hmac.new(secret, check_string.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(calc, received_hash):
        return None
    try:
        if time.time() - int(parsed.get("auth_date", "0")) > INIT_DATA_MAX_AGE:
            return None
        return json.loads(parsed["user"])
    except (ValueError, KeyError):
        return None


def json_error(message: str, status: int) -> web.Response:
    return web.json_response({"error": message}, status=status)


def auth_user(request: web.Request) -> dict | None:
    user = verify_init_data(request.headers.get("X-Init-Data", ""))
    if user is None and DEV_MODE:
        user = {"id": 1, "first_name": "Dev", "username": "dev"}
    if user is None:
        return None
    full_name = " ".join(x for x in (user.get("first_name"), user.get("last_name")) if x)
    upsert_user(int(user["id"]), user.get("username"), full_name or None)
    return user


# --------------------------------------------------------------------------
# WEB SERVER (WebApp + API)
# --------------------------------------------------------------------------
def puzzle_payload(row: sqlite3.Row) -> dict:
    data = json.loads(row["data"])
    data.update(id=row["id"], title=row["title"], difficulty=row["difficulty"], xp=row["xp"])
    return data


async def handle_index(request: web.Request) -> web.StreamResponse:
    return web.FileResponse(BASE_DIR / "index.html", headers={"Cache-Control": "no-store"})


async def handle_next(request: web.Request) -> web.Response:
    user = auth_user(request)
    if user is None:
        return json_error("Ilovani Telegram ichida oching", 401)
    uid = int(user["id"])
    row = get_next_puzzle_row(uid)
    stats = get_stats(uid)
    if row is None:
        return web.json_response({"done": True, "stats": stats})
    return web.json_response({"done": False, "puzzle": puzzle_payload(row), "stats": stats})


async def handle_get_puzzle(request: web.Request) -> web.Response:
    user = auth_user(request)
    if user is None:
        return json_error("Ilovani Telegram ichida oching", 401)
    row = get_puzzle_row(int(request.match_info["pid"]))
    if row is None:
        return json_error("Masala topilmadi", 404)
    return web.json_response({"done": False, "puzzle": puzzle_payload(row), "stats": get_stats(int(user["id"]))})


async def handle_list(request: web.Request) -> web.Response:
    user = auth_user(request)
    if user is None:
        return json_error("Ilovani Telegram ichida oching", 401)
    return web.json_response({"puzzles": list_puzzles(int(user["id"]))})


async def handle_solve(request: web.Request) -> web.Response:
    user = auth_user(request)
    if user is None:
        return json_error("Ilovani Telegram ichida oching", 401)
    try:
        body = await request.json()
        pid = int(body["puzzle_id"])
        moves = [(int(m["from"]), int(m["to"])) for m in body["moves"]]
        mistakes = max(0, min(int(body.get("mistakes", 0) or 0), 50))
    except (ValueError, KeyError, TypeError):
        return json_error("Noto'g'ri so'rov", 400)

    row = get_puzzle_row(pid)
    if row is None:
        return json_error("Masala topilmadi", 404)
    expected = [(int(m["from"]), int(m["to"])) for m in json.loads(row["data"])["solution_moves"]]
    if moves != expected:
        return json_error("Yechim noto'g'ri", 400)

    result = record_solve(int(user["id"]), pid, mistakes)
    result["stats"] = get_stats(int(user["id"]))
    return web.json_response(result)


def build_web_app() -> web.Application:
    app = web.Application()
    app.router.add_get("/", handle_index)
    app.router.add_get("/api/puzzle/next", handle_next)
    app.router.add_get(r"/api/puzzle/{pid:\d+}", handle_get_puzzle)
    app.router.add_get("/api/puzzles", handle_list)
    app.router.add_post("/api/solve", handle_solve)
    return app


# --------------------------------------------------------------------------
# TELEGRAM BOT (aiogram 3.x)
# --------------------------------------------------------------------------
router = Router()

LESSONS = [
    (
        "1. Taxta va donalar",
        "Rus shashkasi <b>8×8</b> taxtada, faqat <b>to'q (qora) kataklarda</b> o'ynaladi. "
        "Chap pastki burchak (a1) — to'q katak.\n\n"
        "Har bir o'yinchida 12 tadan dona bor. Oq donalar pastda, qora donalar tepada turadi. "
        "Birinchi yurishni <b>oq</b> boshlaydi.",
    ),
    (
        "2. Oddiy yurish",
        "Oddiy dona faqat <b>oldinga</b>, diagonal bo'yicha <b>bir katakka</b> yuradi.\n\n"
        "Yurish uchun katak bo'sh bo'lishi kerak. Orqaga yurish mumkin emas.",
    ),
    (
        "3. Urish qoidalari",
        "Raqib donasi yoniga diagonal bo'yicha turgan va uning ortidagi katak bo'sh bo'lsa, "
        "donani <b>sakrab urish</b> mumkin.\n\n"
        "• Urish <b>majburiy</b> — urish imkoni bo'lsa, oddiy yurish qilib bo'lmaydi.\n"
        "• Oddiy dona <b>oldinga ham, orqaga ham</b> uradi.\n"
        "• Urish davom etishi mumkin bo'lsa, shu dona <b>ketma-ket</b> urishi shart.\n"
        "• Urilgan donalar yurish tugagach olinadi; bir donani ikki marta urib bo'lmaydi.\n"
        "• Bir nechta urish varianti bo'lsa, istalganini tanlash mumkin (eng ko'pini urish shart emas).",
    ),
    (
        "4. Damka",
        "Oddiy dona oxirgi qatorga yetsa, <b>damka</b>ga aylanadi.\n\n"
        "• Damka diagonal bo'yicha <b>istalgan masofaga</b> yuradi.\n"
        "• Damka uzoqdan uradi: raqib donasi ortidagi istalgan bo'sh katakka tushishi mumkin.\n"
        "• Urish paytida oddiy dona oxirgi qatorga yetsa, <b>darhol damka bo'lib</b>, urishni davom ettiradi.",
    ),
    (
        "5. Kombinatsiya nima?",
        "<b>Kombinatsiya</b> — bir yoki bir necha donani qurbon qilib, raqibni majburiy urishga "
        "undash va keyin ko'proq dona urib olish.\n\n"
        "Masalani yechishda: avval raqibning majburiy urishlarini tasavvur qiling, so'ng o'zingizning "
        "ketma-ket urishingizni hisoblang.",
    ),
]


def main_menu() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text=BTN_PUZZLES)],
            [KeyboardButton(text=BTN_LESSONS), KeyboardButton(text=BTN_RATING)],
            [KeyboardButton(text=BTN_PROFILE)],
        ],
        resize_keyboard=True,
    )


def lessons_kb() -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(text=title, callback_data=f"lesson:{i}")] for i, (title, _) in enumerate(LESSONS)]
    return InlineKeyboardMarkup(inline_keyboard=rows)


def display_name(row: dict) -> str:
    return row.get("full_name") or (f"@{row['username']}" if row.get("username") else str(row["user_id"]))


@router.message(CommandStart())
async def cmd_start(message: Message) -> None:
    u = message.from_user
    upsert_user(u.id, u.username, u.full_name)
    await message.answer(
        f"Salom, <b>{html.escape(u.first_name or 'do‘st')}</b>! 👋\n\n"
        "Bu yerda rus shashkasi bo'yicha kombinatsiyalarni yechib, XP to'plashingiz mumkin.\n"
        "Quyidagi menyudan tanlang:",
        reply_markup=main_menu(),
    )


@router.message(F.text == BTN_PUZZLES)
async def open_puzzles(message: Message) -> None:
    u = message.from_user
    upsert_user(u.id, u.username, u.full_name)
    if not WEBAPP_URL.startswith("https://"):
        await message.answer(
            "⚠️ WebApp manzili sozlanmagan. <code>WEBAPP_URL</code> (HTTPS) o'zgaruvchisini o'rnating."
        )
        return
    kb = InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="▶️ Masalalarni ochish", web_app=WebAppInfo(url=WEBAPP_URL))]]
    )
    await message.answer("Tayyormisiz? Taxtani ochish uchun tugmani bosing 👇", reply_markup=kb)


@router.message(F.text == BTN_LESSONS)
async def show_lessons(message: Message) -> None:
    await message.answer("📚 <b>Darslar</b>\nMavzuni tanlang:", reply_markup=lessons_kb())


@router.callback_query(F.data == "lessons")
async def cb_lessons(call: CallbackQuery) -> None:
    try:
        await call.message.edit_text("📚 <b>Darslar</b>\nMavzuni tanlang:", reply_markup=lessons_kb())
    except TelegramBadRequest:
        pass
    await call.answer()


@router.callback_query(F.data.startswith("lesson:"))
async def cb_lesson(call: CallbackQuery) -> None:
    try:
        idx = int(call.data.split(":", 1)[1])
        title, text = LESSONS[idx]
    except (ValueError, IndexError):
        await call.answer("Dars topilmadi", show_alert=True)
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="⬅️ Darslar ro'yxati", callback_data="lessons")]])
    try:
        await call.message.edit_text(f"<b>{title}</b>\n\n{text}", reply_markup=kb)
    except TelegramBadRequest:
        pass
    await call.answer()


@router.message(F.text == BTN_RATING)
async def show_rating(message: Message) -> None:
    rows = leaderboard(10)
    if not rows:
        await message.answer("🏆 Reyting hozircha bo'sh. Birinchi bo'lib masala yeching!")
        return
    medals = ["🥇", "🥈", "🥉"]
    lines = ["🏆 <b>Eng kuchli 10 talik</b>\n"]
    for i, r in enumerate(rows):
        mark = medals[i] if i < 3 else f"{i + 1}."
        lines.append(f"{mark} {html.escape(display_name(r))} — <b>{r['xp']}</b> XP ({r['solved']} ta masala)")
    me = get_stats(message.from_user.id)
    lines.append(f"\nSizning o'rningiz: <b>{me['rank']}</b> • {me['xp']} XP")
    await message.answer("\n".join(lines))


@router.message(F.text == BTN_PROFILE)
async def show_profile(message: Message) -> None:
    u = message.from_user
    upsert_user(u.id, u.username, u.full_name)
    s = get_stats(u.id)
    await message.answer(
        f"👤 <b>{html.escape(u.full_name)}</b>\n\n"
        f"⭐ XP: <b>{s['xp']}</b>\n"
        f"✅ Yechilgan masalalar: <b>{s['solved']}</b> / {s['total']}\n"
        f"🏆 Reytingdagi o'rin: <b>{s['rank']}</b>"
    )


async def main() -> None:
    if not BOT_TOKEN:
        raise SystemExit("BOT_TOKEN o'rnatilmagan. Misol: export BOT_TOKEN='123456:ABC...'")

    init_db()
    seed_puzzles()

    # Web server (WebApp + API)
    runner = web.AppRunner(build_web_app())
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()
    log.info("Web server: http://0.0.0.0:%d  (WEBAPP_URL=%s)", PORT, WEBAPP_URL or "-")

    # Telegram bot
    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    dp = Dispatcher()
    dp.include_router(router)

    if WEBAPP_URL.startswith("https://"):
        try:
            await bot.set_chat_menu_button(
                menu_button=MenuButtonWebApp(text="🧩 Masalalar", web_app=WebAppInfo(url=WEBAPP_URL))
            )
        except Exception as exc:  # menyu tugmasi majburiy emas
            log.warning("Menyu tugmasini o'rnatib bo'lmadi: %s", exc)

    try:
        await bot.delete_webhook(drop_pending_updates=True)
        await dp.start_polling(bot)
    finally:
        await bot.session.close()
        await runner.cleanup()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        pass
