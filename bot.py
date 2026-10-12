"""
Rus shashkasi (русские шашки) — kombinatsiyalar va masalalar.
Telegram bot (aiogram 3.x) + WebApp serveri (aiohttp) + SQLite + masalalar generatori (BITTA FAYL).

Ishga tushirish:
    pip install -r requirements.txt          # aiogram>=3.4, aiohttp
    export BOT_TOKEN="123456:ABC..."          # BotFather tokeni (kodga yozmang!)
    export WEBAPP_URL="https://sizning-domen" # HTTPS majburiy
    python bot.py

Mahalliy sinov (brauzerda, Telegramsiz):
    DEV_MODE=1 python bot.py   ->  http://localhost:8080

Masalalar generatori (alohida ham ishlaydi, bot tokeni kerak emas):
    python bot.py --gen --seconds 120 --workers 4

Tashqaridan masalalar qo'shish: extra_puzzles.json (puzzles.json bilan bir xil format) faylini
yoniga qo'ying — bot ishga tushganda har bir yechim qoidalar dvigateli bilan tekshiriladi va qo'shiladi.
"""
import argparse
import asyncio
import gzip
import io
import hashlib
import hmac
import html
import json
import logging
import os
import random
import sqlite3
import sys
import time
from contextlib import contextmanager
from multiprocessing import Pool
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
    BufferedInputFile,
    Message,
    ReplyKeyboardMarkup,
    WebAppInfo,
)
from aiohttp import web

# --------------------------------------------------------------------------
# SOZLAMALAR
# --------------------------------------------------------------------------
BASE_DIR = Path(__file__).resolve().parent
BOT_TOKEN = os.getenv("BOT_TOKEN", "")            # FAQAT muhit o'zgaruvchisidan (kodga yozmang!)
WEBAPP_URL = os.getenv("WEBAPP_URL", "")
PORT = int(os.getenv("PORT", "8080"))
# DOIMIY papka: Render'da Disk (Persistent Disk) ulab, DATA_DIR=/var/data qiling.
# Disksiz Render fayl tizimi har deploy/restartda tozalanadi -> baza va masalalar o'chib ketadi!
DATA_DIR = Path(os.getenv("DATA_DIR", str(BASE_DIR)))
DATA_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = os.getenv("DB_PATH", str(DATA_DIR / "shashka.db"))
# Telegram zaxira: baza nusxasi shu chatga (sizning Telegram ID ingiz) yuboriladi va biriktiriladi (pin).
BACKUP_CHAT_ID = int(os.getenv("BACKUP_CHAT_ID", "0") or 0)
BACKUP_INTERVAL = int(os.getenv("BACKUP_INTERVAL", "60"))  # soniya; faqat o'zgarish bo'lsa yuboriladi
DEV_MODE = os.getenv("DEV_MODE", "0") == "1"
INIT_DATA_MAX_AGE = 24 * 3600  # initData necha soniya amal qiladi
PUZZLES_PATH = Path(os.getenv("PUZZLES_PATH", str(DATA_DIR / "puzzles.json")))
BUNDLED_PUZZLES = BASE_DIR / "puzzles.json"   # repodagi boshlang'ich masalalar (faqat o'qiladi)
EXTRA_PATH = BASE_DIR / "extra_puzzles.json"
AUTO_TARGET = int(os.getenv("AUTO_TARGET", "400"))  # bot shuncha masalagacha o'zi generatsiya qiladi
START_RATING = 1000
TZ_OFFSET = "+5 hours"  # Toshkent vaqti (kunlik/haftalik reyting chegarasi)

SOLID_PLIES = 6   # kombinatsiyadan keyin necha yarim-yurish chuqurlikda ustunlik tekshiriladi
MIN_ADV = 4       # kamida 2 ta oddiy dona (dona=2, damka=5) ustunlik, yoki yutuq
FIRST_ID = 1001   # yangi tizim masalalari ID si shu yerdan boshlanadi
LEVELS = {1: (500, 1000), 2: (1000, 1500), 3: (1500, 2500)}
LEVEL_NAMES = {1: "Oson", 2: "O'rta", 3: "Qiyin"}

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("shashka")

BTN_PUZZLES = "🧩 Masalalar yechish (WebApp)"
BTN_LESSONS = "📚 Darslar"
BTN_RATING = "🏆 Reyting"
BTN_PROFILE = "👤 Profil"


# ==========================================================================
# 1) QOIDALAR DVIGATELI VA GENERATOR
# ==========================================================================
DIRS = ((-1, -1), (-1, 1), (1, -1), (1, 1))
MAN, KING = 2, 5


def inb(r, c):
    return 0 <= r < 8 and 0 <= c < 8


def sq_to_rc(n):
    r, k = (n - 1) // 4, (n - 1) % 4
    return (r, 2 * k + 1 if r % 2 == 0 else 2 * k)


def rc_to_sq(r, c):
    k = (c - 1) // 2 if r % 2 == 0 else c // 2
    return r * 4 + k + 1


def enemy(col):
    return 'b' if col == 'w' else 'w'


# ----------------------------------------------------------------- QOIDALAR
def can_continue(board, frm, to, captured):
    p = board.pop(frm)
    board[to] = p
    ok = bool(jumps_from(board, to[0], to[1], captured))
    del board[to]
    board[frm] = p
    return ok


def jumps_from(board, r, c, captured):
    col, king = board[(r, c)]
    res = []
    for dr, dc in DIRS:
        if not king:
            mr, mc, lr, lc = r + dr, c + dc, r + 2 * dr, c + 2 * dc
            if inb(lr, lc):
                t = board.get((mr, mc))
                if t and t[0] != col and (mr, mc) not in captured and (lr, lc) not in board:
                    res.append(((lr, lc), (mr, mc)))
        else:
            rr, cc = r + dr, c + dc
            while inb(rr, cc) and (rr, cc) not in board:
                rr += dr
                cc += dc
            if not inb(rr, cc):
                continue
            t = board[(rr, cc)]
            if t[0] == col or (rr, cc) in captured:
                continue
            lands = []
            lr, lc = rr + dr, cc + dc
            while inb(lr, lc) and (lr, lc) not in board:
                lands.append((lr, lc))
                lr += dr
                lc += dc
            if not lands:
                continue
            newcap = captured + ((rr, cc),)
            cont = [l for l in lands if can_continue(board, (r, c), l, newcap)]
            for l in (cont or lands):
                res.append((l, (rr, cc)))
    return res


def _chain(board, pos, captured, steps, out):
    js = jumps_from(board, pos[0], pos[1], captured)
    if not js:
        if steps:
            out.append((steps, {k: v for k, v in board.items() if k not in captured}, True))
        return
    col, king = board[pos]
    promo = 0 if col == 'w' else 7
    for to, cap in js:
        b2 = dict(board)
        del b2[pos]
        b2[to] = (col, king or to[0] == promo)
        _chain(b2, to, captured + (cap,), steps + [(pos, to)], out)


def capture_seqs(board, col):
    out = []
    for pos, (pc, _) in list(board.items()):
        if pc == col:
            _chain(board, pos, (), [], out)
    return out


def quiet_moves(board, col):
    out = []
    for (r, c), (pc, k) in board.items():
        if pc != col:
            continue
        if not k:
            fwd = -1 if col == 'w' else 1
            for dc in (-1, 1):
                nr, nc = r + fwd, c + dc
                if inb(nr, nc) and (nr, nc) not in board:
                    out.append(((r, c), (nr, nc)))
        else:
            for dr, dc in DIRS:
                nr, nc = r + dr, c + dc
                while inb(nr, nc) and (nr, nc) not in board:
                    out.append(((r, c), (nr, nc)))
                    nr += dr
                    nc += dc
    return out


def apply_quiet(board, mv):
    fr, to = mv
    p = board[fr]
    b = dict(board)
    del b[fr]
    b[to] = (p[0], p[1] or to[0] == (0 if p[0] == 'w' else 7))
    return b


def moves(board, col):
    """[(steps, yangi_taxta, urishmi)] — urish majburiy."""
    caps = capture_seqs(board, col)
    if caps:
        return caps
    return [([mv], apply_quiet(board, mv), False) for mv in quiet_moves(board, col)]


def ev(board):
    s = 0
    for (_, (col, k)) in board.items():
        v = KING if k else MAN
        s += v if col == 'w' else -v
    return s


def qs(board, side, d=8):
    caps = capture_seqs(board, side)
    if not caps or d == 0:
        return ev(board)
    vals = [qs(fb, enemy(side), d - 1) for _, fb, _ in caps]
    return max(vals) if side == 'w' else min(vals)


def val(board, side, plies, alpha=-10 ** 6, beta=10 ** 6):
    if plies == 0:
        return qs(board, side)
    ms = moves(board, side)
    if not ms:
        return -1000 if side == 'w' else 1000
    if side == 'w':
        v = -10 ** 6
        for _, nb, _ in ms:
            v = max(v, val(nb, 'b', plies - 1, alpha, beta))
            alpha = max(alpha, v)
            if alpha >= beta:
                break
        return v
    v = 10 ** 6
    for _, nb, _ in ms:
        v = min(v, val(nb, 'w', plies - 1, alpha, beta))
        beta = min(beta, v)
        if alpha >= beta:
            break
    return v


# ----------------------------------------------------------------- TAHLIL
def pick_unique(vals, margin=2):
    """Eng yaxshi indeksni qaytaradi, agar u boshqalardan kamida `margin` ga yaxshi bo'lsa."""
    order = sorted(range(len(vals)), key=lambda i: -vals[i])
    if len(order) > 1 and vals[order[0]] - vals[order[1]] < margin:
        return None
    return order[0]


def analyze(b0, mode):
    """mode 1: 1 ta qurbonlik; mode 2: 2 ta qurbonlik. Qaytaradi: dict yoki None."""
    base = ev(b0)
    roots = moves(b0, 'w')
    if len(roots) < 2:
        return None
    plies = 2 if mode == 1 else 4
    vals = [val(nb, 'b', plies) for _, nb, _ in roots]
    best = pick_unique(vals)
    if best is None or vals[best] - base < 2:
        return None
    steps1, s1, cap1 = roots[best]
    pv = [steps1]
    bs = moves(s1, 'b')
    if len(bs) != 1 or not bs[0][2]:
        return None
    pv.append(bs[0][0])
    s2 = bs[0][1]
    ws = moves(s2, 'w')
    if not ws:
        return None
    if mode == 1:
        if not ws[0][2]:
            return None
        i = pick_unique([qs(nb, 'b') for _, nb, _ in ws])
        if i is None:
            return None
        pv.append(ws[i][0])
        final_board = ws[i][1]
        sacs = 1
    else:
        i = pick_unique([val(nb, 'b', 2) for _, nb, _ in ws])
        if i is None:
            return None
        pv.append(ws[i][0])
        bs2 = moves(ws[i][1], 'b')
        if len(bs2) != 1 or not bs2[0][2]:
            return None
        pv.append(bs2[0][0])
        ws3 = moves(bs2[0][1], 'w')
        if not ws3 or not ws3[0][2]:
            return None
        j = pick_unique([qs(nb, 'b') for _, nb, _ in ws3])
        if j is None:
            return None
        pv.append(ws3[j][0])
        final_board = ws3[j][1]
        sacs = 2
    if val(final_board, 'b', SOLID_PLIES) - base < MIN_ADV:
        return None
    # SIFAT TEKSHIRUVI: kombinatsiyadan keyin ham oq HAQIQATAN yutuqda bo'lishi shart
    if base > 2 or val(final_board, 'b', 5) < 2:
        return None
    gain = vals[best] - base
    w_steps = sum(len(s) for k, s in enumerate(pv) if k % 2 == 0)
    kings0 = sum(1 for _, (c, k) in b0.items() if k)
    kings1 = sum(1 for _, (c, k) in final_board.items() if k and c == 'w')
    return {
        'board': b0, 'pv': pv, 'sacs': sacs, 'gain': gain, 'white_steps': w_steps,
        'king': kings0 > 0 or kings1 > sum(1 for _, (c, k) in b0.items() if k and c == 'w'),
        'quiet_first': not cap1, 'pieces': len(b0),
    }


def estimate_elo(r):
    """Masala murakkabligi: 500..2500 (3 daraja: 500-1000, 1000-1500, 1500-2500)."""
    opp = sum(len(s) for k, s in enumerate(r['pv']) if k % 2 == 1)
    e = 500
    e += 190 * max(0, r['white_steps'] - 2)
    e += 65 * min(10, max(0, r['gain'] - 2))
    e += 130 if r['king'] else 0
    e += 90 if r['quiet_first'] else 0
    e += 160 * max(0, opp - 1)
    e += min(150, 15 * max(0, r['pieces'] - 6))
    if r['sacs'] == 2:
        e += 500
    return max(500, min(2500, int(round(e / 10.0)) * 10))


def level_for_elo(elo):
    return 1 if elo < 1000 else (2 if elo < 1500 else 3)



# ----------------------------------------------------------------- POZITSIYALAR
def start_board():
    b = {}
    for n in range(1, 13):
        b[sq_to_rc(n)] = ('b', False)
    for n in range(21, 33):
        b[sq_to_rc(n)] = ('w', False)
    return b


def selfplay_positions(rng):
    b, side, out = start_board(), 'w', []
    for ply in range(rng.randint(10, 60)):
        ms = moves(b, side)
        if not ms:
            break
        b = rng.choice(ms)[1]
        side = enemy(side)
        if side == 'w' and ply >= 8:
            out.append(b)
    return out


def random_endgame(rng):
    nw, nb = rng.randint(2, 6), rng.randint(2, 7)
    sqs = list(range(1, 33))
    rng.shuffle(sqs)
    b = {}
    for col, n in (('w', nw), ('b', nb)):
        placed = 0
        while placed < n and sqs:
            rc = sq_to_rc(sqs.pop())
            king = rng.random() < 0.22
            if not king and rc[0] == (0 if col == 'w' else 7):
                continue
            b[rc] = (col, king)
            placed += 1
    return b


def rot(board):
    return {(7 - r, 7 - c): (enemy(col), k) for (r, c), (col, k) in board.items()}


def canon(board):
    a = tuple(sorted(board.items()))
    b = tuple(sorted(rot(board).items()))
    return min(a, b)


def worker(args):
    seed, seconds = args
    rng = random.Random(seed)
    t0, found, seen = time.time(), [], set()
    while time.time() - t0 < seconds:
        positions = selfplay_positions(rng) if rng.random() < 0.65 else [random_endgame(rng)]
        for b0 in positions:
            if time.time() - t0 > seconds:
                break
            key = canon(b0)
            if key in seen:
                continue
            seen.add(key)
            res = analyze(b0, 1)
            if res is None and rng.random() < 0.2:
                res = analyze(b0, 2)
            if res:
                found.append(res)
    return found


# ----------------------------------------------------------------- JSON
def board_from_puzzle(p):
    ib, b = p['initial_board'], {}
    for key, col, king in (('white', 'w', False), ('white_kings', 'w', True),
                           ('black', 'b', False), ('black_kings', 'b', True)):
        for n in ib.get(key, []):
            b[sq_to_rc(n)] = (col, king)
    return b


def board_to_json(board):
    d = {'white': [], 'white_kings': [], 'black': [], 'black_kings': []}
    for (r, c), (col, k) in sorted(board.items(), key=lambda x: rc_to_sq(*x[0])):
        d[('white' if col == 'w' else 'black') + ('_kings' if k else '')].append(rc_to_sq(r, c))
    return {k: v for k, v in d.items() if v}


def title_for(r, n):
    if r['sacs'] == 2:
        return "Ikki qurbonlik: %d-kombinatsiya" % n
    if r['king']:
        return "Damkaga yo'l: %d-kombinatsiya" % n
    if r['gain'] >= 6:
        return "Katta zarba: %d-kombinatsiya" % n
    if r['gain'] >= 4:
        return "Qo'sh zarba: %d-kombinatsiya" % n
    return "Qurbonlik va zarba: %d-kombinatsiya" % n


def to_puzzle(r, pid, flip):
    board, pv = r['board'], r['pv']
    sol = []
    for steps in pv:
        for a, b in steps:
            sol.append((a, b))
    if flip:
        board = rot(board)
        sol = [((7 - a[0], 7 - a[1]), (7 - b[0], 7 - b[1])) for a, b in sol]
    elo = estimate_elo(r)
    lvl = level_for_elo(elo)
    return {
        'id': pid,
        'title': title_for(r, pid),
        'difficulty': {1: 'Oson', 2: "O'rta", 3: 'Qiyin'}[lvl],
        'level': lvl,
        'elo': elo,
        'turn': 'black' if flip else 'white',
        'initial_board': board_to_json(board),
        'solution_moves': [{'from': rc_to_sq(*a), 'to': rc_to_sq(*b)} for a, b in sol],
    }


def validate_puzzle(p):
    """Yechimni dvigatel bilan qayta o'ynab tekshiradi: har yurish qonuniy, oxirida material yutuq."""
    try:
        board = board_from_puzzle(p)
        sol = [(sq_to_rc(m['from']), sq_to_rc(m['to'])) for m in p['solution_moves']]
        user = 'w' if p.get('turn', 'white') == 'white' else 'b'
        sign = 1 if user == 'w' else -1
        base = ev(board)
        side, i = user, 0
        while i < len(sol):
            ms = [m for m in moves(board, side) if list(m[0]) == sol[i:i + len(m[0])]]
            if not ms:
                return False
            board = ms[0][1]
            i += len(ms[0][0])
            side = enemy(side)
        if side == user:
            return False
        if p.get('source') == 'Antologiya' or not moves(board, side):
            return True   # kitobdagi (muallif tasdiqlagan) yutuq yoki raqib yura olmaydi
        v = val(board, side, SOLID_PLIES)  # raqib yurishi, chuqur qidiruv
        return sign * (v - base) >= MIN_ADV
    except Exception:
        return False


def _normalize(existing):
    for p in existing:  # qo'lda yozilgan masalalarga daraja/ELO qo'shamiz
        if 'elo' not in p:
            p['elo'] = {1: 800, 2: 1100}.get(p['id'], 900)
        p['level'] = level_for_elo(p['elo'])
        p.setdefault('difficulty', LEVEL_NAMES[p['level']])
        p.pop('xp', None)
    return existing


def _save_json(path, data):
    tmp = str(path) + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=1)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def generate_to_file(out, seconds, workers, cap, seed, start_id=1):
    """Yangi masalalarni topib, `out` fayliga QO'SHADI (mavjud ID lar o'zgarmaydi)."""
    existing = _normalize(json.load(open(out, encoding='utf-8')) if os.path.exists(out) else [])
    db_rows, db_max = db_puzzle_info()
    seen = {canon(board_from_puzzle(p)) for p in existing + db_rows}
    next_id = max([p['id'] for p in existing] + [db_max, FIRST_ID - 1]) + 1

    jobs = [(seed + i, seconds) for i in range(workers)]
    if workers <= 1:
        batches = [worker(jobs[0])]
    else:
        with Pool(workers) as pool:
            batches = pool.map(worker, jobs)
    cands = [r for b in batches for r in b]

    rng = random.Random(seed)
    rng.shuffle(cands)
    count = {1: 0, 2: 0, 3: 0}
    chosen = []
    for r in cands:
        key = canon(r['board'])
        if key in seen:
            continue
        elo = estimate_elo(r)
        lvl = level_for_elo(elo)
        if count[lvl] >= cap:
            continue
        seen.add(key)
        count[lvl] += 1
        chosen.append((elo, r, rng.random() < 0.5))
    chosen.sort(key=lambda x: x[0])
    new = []
    for _, r, flip in chosen:
        p = to_puzzle(r, next_id, flip)
        if validate_puzzle(p):
            new.append(p)
            next_id += 1
    allp = existing + new
    _save_json(out, allp)
    by = {1: 0, 2: 0, 3: 0}
    for p in allp:
        by[p['level']] += 1
    return len(cands), len(new), len(allp), by


def import_extra_puzzles():
    """extra_puzzles.json dagi masalalarni tekshirib, puzzles.json ga qo'shadi."""
    if not EXTRA_PATH.exists():
        return
    try:
        extra = json.loads(EXTRA_PATH.read_text(encoding='utf-8'))
        existing = _normalize(json.loads(PUZZLES_PATH.read_text(encoding='utf-8')) if PUZZLES_PATH.exists() else [])
        db_rows, db_max = db_puzzle_info()
        seen = {canon(board_from_puzzle(p)) for p in existing + db_rows}
        next_id = max([p['id'] for p in existing] + [db_max, FIRST_ID - 1]) + 1
        added = bad = 0
        for p in extra:
            if not validate_puzzle(p) or canon(board_from_puzzle(p)) in seen:
                bad += 1
                continue
            seen.add(canon(board_from_puzzle(p)))
            p['id'] = next_id
            p.setdefault('title', 'Kombinatsiya %d' % next_id)
            p.setdefault('elo', 1000)
            p.setdefault('turn', 'white')
            existing.append(p)
            next_id += 1
            added += 1
        _save_json(PUZZLES_PATH, _normalize(existing))
        EXTRA_PATH.rename(EXTRA_PATH.with_suffix('.json.done'))
        log.info("extra_puzzles.json: %d qo'shildi, %d o'tkazib yuborildi (noto'g'ri yoki takror)", added, bad)
    except Exception as exc:
        log.warning("extra_puzzles.json o'qilmadi: %s", exc)


def gen_main(argv):
    ap = argparse.ArgumentParser(prog='bot.py --gen')
    ap.add_argument('--seconds', type=int, default=120)
    ap.add_argument('--workers', type=int, default=min(4, os.cpu_count() or 1))
    ap.add_argument('--out', default=str(PUZZLES_PATH))
    ap.add_argument('--cap', type=int, default=60, help="har bir daraja uchun yangi masalalar chegarasi")
    ap.add_argument('--seed', type=int, default=int(time.time()))
    ap.add_argument('--start-id', type=int, default=1)
    a = ap.parse_args(argv)
    cands, new, total, by = generate_to_file(a.out, a.seconds, a.workers, a.cap, a.seed, a.start_id)
    print('topilgan nomzodlar:', cands, '| yangi:', new, '| jami:', total, '| darajalar:', by)


# ==========================================================================
# 2) MA'LUMOTLAR BAZASI (SQLite)
# ==========================================================================
@contextmanager
def db():
    conn = sqlite3.connect(DB_PATH, timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA busy_timeout = 30000")
    conn.execute("PRAGMA journal_mode = WAL")      # bot + generator bir vaqtda yozsa ham buzilmaydi
    conn.execute("PRAGMA synchronous = NORMAL")
    try:
        yield conn
        conn.commit()
        if conn.total_changes:
            mark_dirty()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


# ==========================================================================
# 2b) TELEGRAM ZAXIRA (disksiz hostingda ma'lumot yo'qolmasligi uchun)
# ==========================================================================
_dirty = False
_last_backup_msg = None


def mark_dirty() -> None:
    global _dirty
    _dirty = True


def make_snapshot() -> bytes:
    """Bazaning izchil nusxasi (SQLite backup API), gzip bilan siqilgan."""
    tmp = DB_PATH + ".snap"
    src = sqlite3.connect(DB_PATH, timeout=30)
    dst = sqlite3.connect(tmp)
    try:
        src.backup(dst)
    finally:
        dst.close()
        src.close()
    try:
        with open(tmp, "rb") as f:
            return gzip.compress(f.read(), 6)
    finally:
        os.remove(tmp)


def install_snapshot(data: bytes) -> bool:
    """Zaxirani tekshirib, bazaning o'rniga qo'yadi."""
    tmp = DB_PATH + ".restore"
    with open(tmp, "wb") as f:
        f.write(gzip.decompress(data))
    conn = sqlite3.connect(tmp)
    try:
        ok = conn.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
    finally:
        conn.close()
    if not ok:
        os.remove(tmp)
        return False
    for ext in ("-wal", "-shm"):
        if os.path.exists(DB_PATH + ext):
            os.remove(DB_PATH + ext)
    os.replace(tmp, DB_PATH)
    return True


async def restore_backup_if_needed(bot) -> None:
    """Baza fayli yo'q bo'lsa (hosting tozalangan), biriktirilgan zaxirani Telegram'dan tiklaydi."""
    global _last_backup_msg
    if not BACKUP_CHAT_ID:
        log.warning("BACKUP_CHAT_ID o'rnatilmagan — zaxira o'chiq, ma'lumot yo'qolishi mumkin!")
        return
    if os.path.exists(DB_PATH):
        return
    try:
        chat = await bot.get_chat(BACKUP_CHAT_ID)
        pm = getattr(chat, "pinned_message", None)
        doc = getattr(pm, "document", None)
        if not doc:
            log.info("Tiklash uchun zaxira topilmadi (birinchi ishga tushish).")
            return
        buf = io.BytesIO()
        await bot.download(doc.file_id, destination=buf)
        if await asyncio.to_thread(install_snapshot, buf.getvalue()):
            _last_backup_msg = pm.message_id
            log.info("Baza Telegram zaxirasidan tiklandi.")
        else:
            log.error("Zaxira buzilgan, tiklanmadi.")
    except Exception as exc:
        log.warning("Zaxiradan tiklab bo'lmadi: %s", exc)


async def send_backup(bot) -> None:
    global _dirty, _last_backup_msg
    if not BACKUP_CHAT_ID or not os.path.exists(DB_PATH):
        return
    _dirty = False
    try:
        data = await asyncio.to_thread(make_snapshot)
        name = time.strftime("shashka-%Y%m%d-%H%M%S.db.gz")
        msg = await bot.send_document(
            BACKUP_CHAT_ID, BufferedInputFile(data, filename=name),
            caption="💾 Baza zaxirasi", disable_notification=True,
        )
        await bot.pin_chat_message(BACKUP_CHAT_ID, msg.message_id, disable_notification=True)
        old, _last_backup_msg = _last_backup_msg, msg.message_id
        if old:
            for fn in (bot.unpin_chat_message, bot.delete_message):
                try:
                    if fn is bot.unpin_chat_message:
                        await fn(BACKUP_CHAT_ID, message_id=old)
                    else:
                        await fn(BACKUP_CHAT_ID, old)
                except Exception:
                    pass
        log.info("Zaxira yuborildi (%d KB)", len(data) // 1024)
    except Exception as exc:
        _dirty = True  # keyingi safar qayta uriniladi
        log.warning("Zaxira yuborilmadi: %s", exc)


async def backup_loop(bot) -> None:
    while True:
        await asyncio.sleep(BACKUP_INTERVAL)
        if _dirty:
            await send_backup(bot)


def _add_column(conn, table, column, ddl):
    cols = [r["name"] for r in conn.execute(f"PRAGMA table_info({table})")]
    if column not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {ddl}")


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
        # eski bazalar uchun yangi ustunlar (migratsiya)
        _add_column(conn, "Users", "rating", f"INTEGER NOT NULL DEFAULT {START_RATING}")
        _add_column(conn, "Puzzles", "elo", "INTEGER NOT NULL DEFAULT 1000")
        _add_column(conn, "Puzzles", "level", "INTEGER NOT NULL DEFAULT 1")
        _add_column(conn, "UserProgress", "stars", "INTEGER NOT NULL DEFAULT 0")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_up_solved ON UserProgress(solved, solved_at)")


def seed_puzzles() -> int:
    """JSON dagi YANGI masalalarni bazaga qo'shadi. Mavjud masala va foydalanuvchi natijalari
    HECH QACHON o'chirilmaydi/o'zgartirilmaydi (baza — asosiy manba)."""
    sources = [PUZZLES_PATH] + ([BUNDLED_PUZZLES] if BUNDLED_PUZZLES != PUZZLES_PATH else [])
    added = 0
    with db() as conn:
        have = {r["id"] for r in conn.execute("SELECT id FROM Puzzles")}
        for src in sources:
            if not src.exists():
                continue
            try:
                puzzles = _normalize(json.loads(src.read_text(encoding="utf-8")))
            except (OSError, ValueError) as exc:
                log.warning("%s o'qilmadi: %s", src, exc)
                continue
            for p in puzzles:
                pid = int(p["id"])
                if pid in have:
                    continue
                conn.execute(
                    "INSERT INTO Puzzles (id, title, difficulty, xp, elo, level, data) VALUES (?, ?, ?, 10, ?, ?, ?)",
                    (pid, p["title"], p["difficulty"], int(p["elo"]), int(p["level"]),
                     json.dumps(p, ensure_ascii=False)),
                )
                have.add(pid)
                added += 1
    log.info("Bazaga %d ta yangi masala qo'shildi (jami %d)", added, len(have))
    return added


def db_puzzle_info():
    """(bazadagi masalalar, eng katta ID) — generator ID to'qnashuvining oldini olish uchun."""
    if not os.path.exists(DB_PATH):
        return [], 0
    try:
        with db() as conn:
            rows = [json.loads(r["data"]) for r in conn.execute("SELECT data FROM Puzzles")]
            mx = conn.execute("SELECT COALESCE(MAX(id), 0) AS m FROM Puzzles").fetchone()["m"]
        return rows, mx
    except sqlite3.Error:
        return [], 0


def count_puzzles() -> int:
    with db() as conn:
        return conn.execute("SELECT COUNT(*) AS n FROM Puzzles").fetchone()["n"]


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
        u = conn.execute("SELECT rating FROM Users WHERE user_id = ?", (user_id,)).fetchone()
        rating = u["rating"] if u else START_RATING
        row = conn.execute(
            "SELECT COUNT(*) AS n, COALESCE(SUM(stars), 0) AS s FROM UserProgress WHERE user_id = ? AND solved = 1",
            (user_id,),
        ).fetchone()
        solved, stars = row["n"], row["s"]
        total = conn.execute("SELECT COUNT(*) AS n FROM Puzzles").fetchone()["n"]
        rank = None
        if solved:
            rank = conn.execute(
                """SELECT COUNT(*) + 1 AS r FROM Users
                   WHERE rating > ? AND user_id IN (SELECT user_id FROM UserProgress WHERE solved = 1)""",
                (rating,),
            ).fetchone()["r"]
        lv = {1: {"total": 0, "solved": 0}, 2: {"total": 0, "solved": 0}, 3: {"total": 0, "solved": 0}}
        for r in conn.execute(
            """
            SELECT p.level AS level, COUNT(*) AS total, COALESCE(SUM(up.solved), 0) AS solved
            FROM Puzzles p LEFT JOIN UserProgress up ON up.puzzle_id = p.id AND up.user_id = ?
            GROUP BY p.level
            """,
            (user_id,),
        ):
            if r["level"] in lv:
                lv[r["level"]] = {"total": r["total"], "solved": r["solved"]}
    return {"rating": rating, "solved": solved, "stars": stars, "total": total, "rank": rank, "levels": lv}


def get_puzzle_row(puzzle_id: int):
    with db() as conn:
        return conn.execute("SELECT * FROM Puzzles WHERE id = ?", (puzzle_id,)).fetchone()


def get_next_puzzle_row(user_id: int, level: int = 0, skip=()):
    """Yechilmagan masala. level=0: reytingga eng yaqin ELO; level 1..3: shu daraja, osondan qiyinga."""
    with db() as conn:
        rating = get_stats_rating(conn, user_id)
        where, args = "COALESCE(up.solved, 0) = 0", [user_id]
        if level in LEVELS:
            where += " AND p.level = ?"
            args.append(level)
            order = "p.elo ASC, p.id ASC"
        else:
            order = "ABS(p.elo - ?) ASC, p.id ASC"
        if skip:
            where += " AND p.id NOT IN (%s)" % ",".join(str(int(x)) for x in skip)
        sql = f"""SELECT p.* FROM Puzzles p
                  LEFT JOIN UserProgress up ON up.puzzle_id = p.id AND up.user_id = ?
                  WHERE {where} ORDER BY {order} LIMIT 1"""
        if level not in LEVELS:
            args.append(rating)
        return conn.execute(sql, args).fetchone()


def get_stats_rating(conn, user_id: int) -> int:
    u = conn.execute("SELECT rating FROM Users WHERE user_id = ?", (user_id,)).fetchone()
    return u["rating"] if u else START_RATING


def stars_for(mistakes: int) -> int:
    return 3 if mistakes == 0 else (2 if mistakes == 1 else 1)


def new_rating(user_rating: int, puzzle_elo: int, stars: int) -> int:
    score = {3: 1.0, 2: 0.65, 1: 0.35}[stars]
    expected = 1.0 / (1.0 + 10 ** ((puzzle_elo - user_rating) / 400.0))
    return max(100, int(round(user_rating + 32 * (score - expected))))


def record_solve(user_id: int, puzzle_id: int, mistakes: int) -> dict | None:
    """Yechimni AVTOMATIK saqlaydi: yulduz, reyting. Reyting/kunlik hisob faqat birinchi yechim uchun."""
    stars = stars_for(mistakes)
    with db() as conn:
        conn.execute("BEGIN IMMEDIATE")   # ikki parallel so'rov reytingni ikki marta hisoblamasligi uchun
        pz = conn.execute("SELECT elo FROM Puzzles WHERE id = ?", (puzzle_id,)).fetchone()
        if pz is None:
            return None
        rating = get_stats_rating(conn, user_id)
        prog = conn.execute(
            "SELECT solved, stars FROM UserProgress WHERE user_id = ? AND puzzle_id = ?",
            (user_id, puzzle_id),
        ).fetchone()
        if prog and prog["solved"]:
            best = prog["stars"]
            if stars > best:  # qayta yechib yulduzni yaxshilash mumkin
                conn.execute(
                    "UPDATE UserProgress SET stars = ?, mistakes = ?, attempts = attempts + 1 "
                    "WHERE user_id = ? AND puzzle_id = ?",
                    (stars, mistakes, user_id, puzzle_id),
                )
                best = stars
            return {"already_solved": True, "stars": stars, "best_stars": best, "delta": 0, "rating": rating}
        updated = new_rating(rating, pz["elo"], stars)
        conn.execute(
            """
            INSERT INTO UserProgress (user_id, puzzle_id, solved, attempts, mistakes, stars, solved_at)
            VALUES (?, ?, 1, 1, ?, ?, CURRENT_TIMESTAMP)
            ON CONFLICT(user_id, puzzle_id) DO UPDATE SET
                solved = 1, attempts = attempts + 1, mistakes = excluded.mistakes,
                stars = excluded.stars, solved_at = CURRENT_TIMESTAMP
            """,
            (user_id, puzzle_id, mistakes, stars),
        )
        conn.execute("UPDATE Users SET rating = ? WHERE user_id = ?", (updated, user_id))
    return {"already_solved": False, "stars": stars, "best_stars": stars, "delta": updated - rating, "rating": updated}


# ---- Top-10 ligalar: kunlik / haftalik / umumiy (yechilgan masalalar soni bo'yicha) ----
PERIOD_COND = {
    "day": f"AND date(up.solved_at, '{TZ_OFFSET}') = date('now', '{TZ_OFFSET}')",
    "week": f"AND date(up.solved_at, '{TZ_OFFSET}') >= date('now', '{TZ_OFFSET}', 'weekday 0', '-6 days')",
    "all": "",
}


def leaderboard(period: str, limit: int = 10) -> list[dict]:
    cond = PERIOD_COND[period]
    with db() as conn:
        rows = conn.execute(
            f"""
            SELECT u.user_id, u.username, u.full_name, u.rating,
                   COUNT(*) AS solved, COALESCE(SUM(up.stars), 0) AS stars
            FROM UserProgress up JOIN Users u ON u.user_id = up.user_id
            WHERE up.solved = 1 {cond}
            GROUP BY u.user_id
            ORDER BY solved DESC, stars DESC, MAX(up.solved_at) ASC, u.user_id ASC
            LIMIT ?
            """,
            (limit,),
        ).fetchall()
    return [dict(r) for r in rows]


def my_period_rank(period: str, user_id: int) -> tuple[int, int] | None:
    """(yechilgan soni, o'rni) yoki shu davrda yechmagan bo'lsa None."""
    cond = PERIOD_COND[period]
    with db() as conn:
        row = conn.execute(
            f"""
            WITH c AS (SELECT up.user_id AS uid, COUNT(*) AS n FROM UserProgress up
                       WHERE up.solved = 1 {cond} GROUP BY up.user_id)
            SELECT n, (SELECT COUNT(*) + 1 FROM c AS o WHERE o.n > c.n) AS rank
            FROM c WHERE uid = ?
            """,
            (user_id,),
        ).fetchone()
    return (row["n"], row["rank"]) if row else None


def rating_leaderboard(limit: int = 10) -> list[dict]:
    with db() as conn:
        rows = conn.execute(
            """
            SELECT u.user_id, u.username, u.full_name, u.rating,
                   (SELECT COUNT(*) FROM UserProgress up WHERE up.user_id = u.user_id AND up.solved = 1) AS solved
            FROM Users u
            WHERE EXISTS (SELECT 1 FROM UserProgress up WHERE up.user_id = u.user_id AND up.solved = 1)
            ORDER BY u.rating DESC, u.user_id ASC LIMIT ?
            """,
            (limit,),
        ).fetchall()
    return [dict(r) for r in rows]


def today_solved(user_id: int) -> int:
    r = my_period_rank("day", user_id)
    return r[0] if r else 0


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

# ==========================================================================
# 3) WEB SERVER (WebApp + API)
# ==========================================================================
def puzzle_payload(row: sqlite3.Row) -> dict:
    data = json.loads(row["data"])
    data.update(id=row["id"], title=row["title"], difficulty=row["difficulty"], elo=row["elo"], level=row["level"])
    return data


def need_user(request: web.Request):
    user = auth_user(request)
    if user is None:
        return None, json_error("Ilovani Telegram ichida oching", 401)
    return user, None


async def handle_index(request: web.Request) -> web.StreamResponse:
    return web.FileResponse(BASE_DIR / "index.html", headers={"Cache-Control": "no-store"})


async def handle_next(request: web.Request) -> web.Response:
    user, err = need_user(request)
    if err:
        return err
    uid = int(user["id"])
    try:
        level = int(request.query.get("level", "0"))
    except ValueError:
        level = 0
    skip = [int(x) for x in request.query.get("skip", "").split(",") if x.strip().isdigit()][:200]
    row = get_next_puzzle_row(uid, level, skip)
    if row is None and skip:  # hammasi o'tkazib yuborilgan bo'lsa, qaytadan boshlaymiz
        row = get_next_puzzle_row(uid, level)
    stats = get_stats(uid)
    if row is None:
        return web.json_response({"done": True, "stats": stats})
    return web.json_response({"done": False, "puzzle": puzzle_payload(row), "stats": stats})


async def handle_get_puzzle(request: web.Request) -> web.Response:
    user, err = need_user(request)
    if err:
        return err
    row = get_puzzle_row(int(request.match_info["pid"]))
    if row is None:
        return json_error("Masala topilmadi", 404)
    return web.json_response({"done": False, "puzzle": puzzle_payload(row), "stats": get_stats(int(user["id"]))})


async def handle_solve(request: web.Request) -> web.Response:
    user, err = need_user(request)
    if err:
        return err
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
    app.router.add_post("/api/solve", handle_solve)
    return app


# ==========================================================================
# 4) TELEGRAM BOT (aiogram 3.x)
# ==========================================================================
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
        "Bu yerda rus shashkasi kombinatsiyalarini yechib, reyting va ⭐ yulduzlar to'plashingiz mumkin.\n"
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


# ---- Reyting: kunlik / haftalik / umumiy top-10 + ELO ----
LB_TITLES = {
    "day": "📅 Kunlik top-10 (bugun)",
    "week": "📆 Haftalik top-10 (dushanbadan)",
    "all": "🌍 Umumiy top-10 (boshidan beri)",
}
MEDALS = ["🥇", "🥈", "🥉"]


def rating_kb(active: str) -> InlineKeyboardMarkup:
    def b(text, key):
        return InlineKeyboardButton(text=("• " + text) if key == active else text, callback_data=f"lb:{key}")

    return InlineKeyboardMarkup(
        inline_keyboard=[[b("Kunlik", "day"), b("Haftalik", "week")], [b("Umumiy", "all"), b("⭐ ELO", "elo")]]
    )


def render_leaderboard(period: str, uid: int) -> str:
    if period == "elo":
        rows = rating_leaderboard(10)
        lines = ["⭐ <b>ELO reyting top-10</b>\n"]
        for i, r in enumerate(rows):
            mark = MEDALS[i] if i < 3 else f"{i + 1}."
            lines.append(f"{mark} {html.escape(display_name(r))} — <b>{r['rating']}</b> ELO ({r['solved']} ta)")
        if not rows:
            lines.append("Hozircha bo'sh.")
        me = get_stats(uid)
        lines.append(f"\nSizning ELO: <b>{me['rating']}</b>" + (f" • o'rin: <b>{me['rank']}</b>" if me["rank"] else ""))
        return "\n".join(lines)
    rows = leaderboard(period, 10)
    lines = [f"<b>{LB_TITLES[period]}</b>\n"]
    for i, r in enumerate(rows):
        mark = MEDALS[i] if i < 3 else f"{i + 1}."
        lines.append(f"{mark} {html.escape(display_name(r))} — <b>{r['solved']}</b> ta ({r['stars']}⭐)")
    if not rows:
        lines.append("Hozircha bo'sh. Birinchi bo'lib masala yeching!")
    mine = my_period_rank(period, uid)
    lines.append(f"\nSiz: <b>{mine[0]}</b> ta • o'rin: <b>{mine[1]}</b>" if mine else "\nSiz bu davrda hali yechmagansiz.")
    return "\n".join(lines)


@router.message(F.text == BTN_RATING)
async def show_rating(message: Message) -> None:
    u = message.from_user
    upsert_user(u.id, u.username, u.full_name)
    await message.answer(render_leaderboard("day", u.id), reply_markup=rating_kb("day"))


@router.callback_query(F.data.startswith("lb:"))
async def cb_rating(call: CallbackQuery) -> None:
    period = call.data.split(":", 1)[1]
    if period not in ("day", "week", "all", "elo"):
        await call.answer()
        return
    try:
        await call.message.edit_text(render_leaderboard(period, call.from_user.id), reply_markup=rating_kb(period))
    except TelegramBadRequest:
        pass
    await call.answer()


@router.message(F.text == BTN_PROFILE)
async def show_profile(message: Message) -> None:
    u = message.from_user
    upsert_user(u.id, u.username, u.full_name)
    s = get_stats(u.id)
    lv = s["levels"]
    levels_txt = "\n".join(
        f"   • {LEVELS[k][0]}–{LEVELS[k][1]}: {lv[k]['solved']} / {lv[k]['total']}" for k in (1, 2, 3)
    )
    await message.answer(
        f"👤 <b>{html.escape(u.full_name)}</b>\n\n"
        f"📈 ELO reyting: <b>{s['rating']}</b>" + (f" (o'rin: {s['rank']})" if s["rank"] else "") + "\n"
        f"✅ Yechilgan: <b>{s['solved']}</b> / {s['total']}\n"
        f"⭐ Yulduzlar: <b>{s['stars']}</b>\n"
        f"📅 Bugun yechilgan: <b>{today_solved(u.id)}</b>\n\n"
        f"Darajalar bo'yicha:\n{levels_txt}"
    )


# ---- Fon rejimida masalalar generatsiyasi ----
async def auto_generate_loop() -> None:
    """Masalalar soni AUTO_TARGET dan kam bo'lsa, bot ishlayotgan paytda ham generatorni fon jarayonida yuritadi."""
    await asyncio.sleep(3)
    for _ in range(40):
        try:
            if count_puzzles() >= AUTO_TARGET:
                return
            workers = max(1, min(2, os.cpu_count() or 1))
            proc = await asyncio.create_subprocess_exec(
                sys.executable, str(Path(__file__).resolve()), "--gen",
                "--seconds", "90", "--workers", str(workers), "--cap", "40", "--out", str(PUZZLES_PATH),
            )
            await proc.wait()
            await asyncio.to_thread(seed_puzzles)
        except Exception as exc:
            log.warning("Generatsiya xatosi: %s", exc)
        await asyncio.sleep(20)


async def main() -> None:
    if not BOT_TOKEN:
        raise SystemExit("BOT_TOKEN o'rnatilmagan. Misol: export BOT_TOKEN='123456:ABC...'")

    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    await restore_backup_if_needed(bot)   # baza yo'q bo'lsa Telegram zaxirasidan tiklaydi
    init_db()
    import_extra_puzzles()
    seed_puzzles()
    if DATA_DIR == BASE_DIR and os.getenv("RENDER"):
        log.warning("DIQQAT: DATA_DIR o'rnatilmagan — Render'da baza har deployda o'chadi! "
                    "Persistent Disk ulab DATA_DIR=/var/data qiling.")

    # Web server (WebApp + API)
    runner = web.AppRunner(build_web_app())
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()
    log.info("Web server: http://0.0.0.0:%d  (WEBAPP_URL=%s)", PORT, WEBAPP_URL or "-")

    # Telegram bot
    dp = Dispatcher()
    dp.include_router(router)

    if WEBAPP_URL.startswith("https://"):
        try:
            await bot.set_chat_menu_button(
                menu_button=MenuButtonWebApp(text="🧩 Masalalar", web_app=WebAppInfo(url=WEBAPP_URL))
            )
        except Exception as exc:  # menyu tugmasi majburiy emas
            log.warning("Menyu tugmasini o'rnatib bo'lmadi: %s", exc)

    gen_task = asyncio.create_task(auto_generate_loop())
    backup_task = asyncio.create_task(backup_loop(bot))
    try:
        await bot.delete_webhook(drop_pending_updates=True)
        await dp.start_polling(bot)
    finally:
        gen_task.cancel()
        backup_task.cancel()
        try:
            await send_backup(bot)   # to'xtashdan oldin oxirgi zaxira
        except Exception:
            pass
        await bot.session.close()
        await runner.cleanup()


if __name__ == "__main__":
    if "--gen" in sys.argv:
        gen_main([a for a in sys.argv[1:] if a != "--gen"])
    else:
        try:
            asyncio.run(main())
        except (KeyboardInterrupt, SystemExit):
            pass
