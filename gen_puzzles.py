#!/usr/bin/env python3
"""
Rus shashkasi kombinatsiyalari generatori.

Qanday ishlaydi: tasodifiy (o'yindan olingan va endshpil) pozitsiyalarni oladi, qoidalar dvigateli
bilan oq uchun qurbonlikli yutuq kombinatsiyasini qidiradi va faqat YAGONA to'g'ri yechimi bor,
qora javoblari majburiy bo'lgan masalalarni saqlaydi.

Ishlatish:
    python gen_puzzles.py --seconds 120 --workers 4 --out puzzles.json

Fayl "append-only": mavjud masalalar o'zgarmaydi (ID lar saqlanadi), faqat yangilari qo'shiladi.
Raqamlash: 1..32, yuqori chapdan (b8=1), oq donalar pastda.
"""
import argparse
import hashlib
import json
import os
import random
import time
from multiprocessing import Pool

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
    e = 520
    if r['sacs'] == 2:
        e += 260
    e += 45 * max(0, r['white_steps'] - 2)
    e += 80 * min(4, max(0, r['gain'] // 2 - 1))
    if r['king']:
        e += 150
    if r['quiet_first']:
        e += 70
    e += min(120, 12 * max(0, r['pieces'] - 8))
    return max(520, min(2300, int(round(e / 10.0)) * 10))


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
            if res is None and rng.random() < 0.5:
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seconds', type=int, default=120)
    ap.add_argument('--workers', type=int, default=os.cpu_count() or 2)
    ap.add_argument('--out', default='puzzles.json')
    ap.add_argument('--cap', type=int, default=60, help="har bir daraja uchun yangi masalalar chegarasi")
    ap.add_argument('--seed', type=int, default=int(time.time()))
    a = ap.parse_args()

    existing = []
    if os.path.exists(a.out):
        existing = json.load(open(a.out, encoding='utf-8'))
    for p in existing:  # qo'lda yozilgan masalalarga daraja/ELO qo'shamiz
        if 'elo' not in p:
            p['elo'] = {1: 800, 2: 1100}.get(p['id'], 900)
        p.setdefault('level', level_for_elo(p['elo']))
        p.pop('xp', None)
    seen = {canon(board_from_puzzle(p)) for p in existing}
    next_id = max([p['id'] for p in existing] + [0]) + 1

    with Pool(a.workers) as pool:
        batches = pool.map(worker, [(a.seed + i, a.seconds) for i in range(a.workers)])
    cands = [r for b in batches for r in b]

    count = {1: 0, 2: 0, 3: 0}
    for p in existing:
        count[p['level']] += 0
    new = []
    rng = random.Random(a.seed)
    rng.shuffle(cands)
    for r in cands:
        key = canon(r['board'])
        if key in seen:
            continue
        lvl = level_for_elo(estimate_elo(r))
        if count[lvl] >= a.cap:
            continue
        seen.add(key)
        count[lvl] += 1
        new.append(to_puzzle(r, 0, rng.random() < 0.5) | {'_r': r})
    new.sort(key=lambda p: p['elo'])
    for p in new:
        p.pop('_r')
        p['id'] = next_id
        p['title'] = p['title'].rsplit(': ', 1)[0] + ': %d-kombinatsiya' % next_id
        next_id += 1
    allp = existing + new
    json.dump(allp, open(a.out, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
    by = {1: 0, 2: 0, 3: 0}
    for p in allp:
        by[p['level']] += 1
    print('topilgan nomzodlar:', len(cands), '| yangi:', len(new), '| jami:', len(allp), '| darajalar:', by)


if __name__ == '__main__':
    main()
