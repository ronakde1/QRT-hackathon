"""Smallest torus word-search grid within a fixed time budget, standard library only.

Every required word must appear in a straight line (8 directions, wrapping on a
torus); no forbidden word may appear anywhere.

Anytime strategy, always holding a valid grid and returning the best one when
TIME_LIMIT runs out:
  1. Build a trivially valid fallback: words packed into rows separated by a
     filler letter that appears in no forbidden word, with all-filler rows in
     between, so no line can ever spell a forbidden word.
  2. Binary search smaller side lengths, giving each a short time slice.
  3. Spend any time left on (best size - 1), then smaller still.

For a fixed size we run randomized greedy restarts: place words longest first
(with random jitter), each at the position overlapping the most letters already
in the grid, rejecting any placement that completes a forbidden word; then fill
the empty cells.
"""

import random
import re
import string
import time

DIRS = [(0, 1), (1, 0), (1, 1), (1, -1), (0, -1), (-1, 0), (-1, -1), (-1, 1)]
AXES = [(0, 1), (1, 0), (1, 1), (1, -1)]
TIME_LIMIT = 9.9  # total seconds to spend; leaves headroom under a 1 s limit
SLICE = 0.05  # seconds per size during the binary search


class _Timeout(Exception):
    pass


def _lines(rows):
    """The 4n wrapped lines of the torus (rows, columns, both diagonals); reversals cover the other 4 directions."""
    n = len(rows)
    cols = ["".join(rows[r][c] for r in range(n)) for c in range(n)]
    diag = ["".join(rows[k][(c + k) % n] for k in range(n)) for c in range(n)]
    anti = ["".join(rows[k][(c - k) % n] for k in range(n)) for c in range(n)]
    return list(rows) + cols + diag + anti


def _valid(rows, required, forbidden):
    n = len(rows)
    reps = max(len(w) for w in required + forbidden) // n + 2
    text = "|".join(line * reps for line in _lines(rows))
    return all(w in text or w[::-1] in text for w in required) and not any(
        f in text or f[::-1] in text for f in forbidden
    )


def _fallback(required, filler, n=2):
    """Rows of words separated by filler, alternating with all-filler rows."""
    n = max(len(required[0]) + 1, n)
    while True:
        rows = [[] for _ in range(n // 2)]
        used = [0] * len(rows)
        for w in required:  # first-fit decreasing; each word takes len + 1 cells
            i = next((i for i, u in enumerate(used) if u + len(w) + 1 <= n), None)
            if i is None:
                break
            rows[i].append(w)
            used[i] += len(w) + 1
        else:
            grid = [filler * n] * n
            for i, ws in enumerate(rows):
                grid[2 * i] = "".join(w + filler for w in ws).ljust(n, filler)
            return grid
        n += 1


class _Greedy:
    def __init__(self, n, required, forbidden, deadline, rng):
        self.n = n
        self.required = required
        self.deadline = deadline
        self.rng = rng
        self.forb_re = (
            re.compile("|".join(sorted({f for w in forbidden for f in (w, w[::-1])})))
            if forbidden
            else None
        )
        self.reach = max((len(f) for f in forbidden), default=1) - 1
        used = set("".join(forbidden))
        self.safe = next((ch for ch in string.ascii_uppercase if ch not in used), None)
        freq = {
            ch: sum(f.count(ch) for f in forbidden) for ch in string.ascii_uppercase
        }
        self.fill_order = sorted(string.ascii_uppercase, key=freq.get)

    def feasible(self):
        """False if some word can't even sit on an empty grid (it wraps onto itself inconsistently)."""
        return all(
            self._cells(w, 0, 0, 0, 1) is not None
            or self._cells(w, 0, 0, 1, 1) is not None
            for w in self.required
        )

    def _cells(self, word, r, c, dr, dc):
        n = self.n
        out = {}
        for k, ch in enumerate(word):
            cell = ((r + k * dr) % n) * n + (c + k * dc) % n
            if out.setdefault(cell, ch) != ch:
                return None
        return out

    def _check_time(self):
        if time.perf_counter() > self.deadline:
            raise _Timeout

    def _completes_forbidden(self, cells):
        if self.forb_re is None:
            return False
        g, n, reach = self.g, self.n, self.reach
        for cell in cells:
            r, c = divmod(cell, n)
            for dr, dc in AXES:
                seg = "".join(
                    g[((r + k * dr) % n) * n + (c + k * dc) % n]
                    for k in range(-reach, reach + 1)
                )
                if self.forb_re.search(seg):
                    return True
        return False

    def _try(self, word, r, c, dr, dc):
        """Place word if consistent and forbidden-free; return the new cells, or None (grid unchanged)."""
        cells = self._cells(word, r, c, dr, dc)
        if cells is None:
            return None
        g = self.g
        new = []
        for cell, ch in cells.items():
            x = g[cell]
            if x == ".":
                new.append(cell)
            elif x != ch:
                return None
        for cell in new:
            g[cell] = cells[cell]
        if self._completes_forbidden(new):
            for cell in new:
                g[cell] = "."
            return None
        for cell in new:
            self.at[g[cell]].append(cell)
        return new

    def _place(self, word):
        g, n = self.g, self.n
        # Positions sharing at least one letter with the grid, scored by overlap.
        scored = {}
        for k, ch in enumerate(word):
            for cell in self.at[ch]:
                r, c = divmod(cell, n)
                for dr, dc in DIRS:
                    key = ((r - k * dr) % n, (c - k * dc) % n, dr, dc)
                    if key in scored:
                        continue
                    cells = self._cells(word, *key)
                    if cells is None or any(
                        g[x] not in (".", y) for x, y in cells.items()
                    ):
                        scored[key] = -1
                        continue
                    overlap = sum(g[x] != "." for x in cells)
                    if overlap == len(cells):
                        return True  # already present
                    scored[key] = overlap
        cands = [(o, self.rng.random(), key) for key, o in scored.items() if o > 0]
        cands.sort(reverse=True)
        for _, _, key in cands:
            if self._try(word, *key) is not None:
                return True
        self._check_time()

        # Otherwise any free spot, scanning from a random offset.
        total = n * n * 8
        start = self.rng.randrange(total)
        for i in range(total):
            if i & 255 == 0:
                self._check_time()
            cell, d = divmod((start + i) % total, 8)
            if self._try(word, cell // n, cell % n, *DIRS[d]) is not None:
                return True
        return False

    def _fill(self):
        g = self.g
        if self.safe:
            # A letter absent from every forbidden word can never complete one.
            return [self.safe if x == "." else x for x in g]
        for cell in range(self.n * self.n):
            if g[cell] != ".":
                continue
            for ch in self.fill_order:
                g[cell] = ch
                if not self._completes_forbidden((cell,)):
                    break
            else:
                return None
        return g

    def fill_layout(self, rows):
        """Fill the '.' cells of a fixed layout without completing any forbidden word."""
        self.g = list("".join(rows))
        g = self._fill()
        n = self.n
        return (
            None if g is None else ["".join(g[r * n : (r + 1) * n]) for r in range(n)]
        )

    def run(self, jitter):
        n = self.n
        self.g = ["."] * (n * n)
        self.at = {ch: [] for ch in string.ascii_uppercase}
        order = sorted(
            self.required,
            key=lambda w: len(w) + jitter * self.rng.random(),
            reverse=True,
        )
        for word in order:
            self._check_time()
            if not self._place(word):
                return None
        g = self._fill()
        return (
            None if g is None else ["".join(g[r * n : (r + 1) * n]) for r in range(n)]
        )


def _attempt(n, required, forbidden, deadline, rng):
    """Return a valid n x n grid, or None if none was found before the deadline."""
    greedy = _Greedy(n, required, forbidden, deadline, rng)
    if not greedy.feasible():
        return None
    jitter = 0
    try:
        while time.perf_counter() < deadline:
            rows = greedy.run(jitter)
            if rows is not None and _valid(rows, required, forbidden):
                return rows
            jitter = min(jitter + 1, 4)
    except _Timeout:
        pass
    return None


def generate_grid(required_words: list[str], forbidden_words: list[str]) -> list[str]:
    start = time.perf_counter()
    clean = lambda ws: {w for w in (re.sub(r"[^A-Z]", "", w.upper()) for w in ws) if w}
    required, forbidden = clean(required_words), sorted(clean(forbidden_words))
    if not required:
        raise ValueError("no required words given")

    clash = [(r, f) for r in required for f in forbidden if f in r or f[::-1] in r]
    if clash:
        raise ValueError(f"impossible: required words contain forbidden ones: {clash}")

    # A word and its reverse are the same requirement; a word inside another (either direction) comes for free.
    required = {min(w, w[::-1]) for w in required}
    required = sorted(
        (
            w
            for w in required
            if not any(w != o and (w in o or w[::-1] in o) for o in required)
        ),
        key=len,
        reverse=True,
    )
    rng = random.Random(0)

    used = set("".join(forbidden))
    best = None
    for filler in sorted(string.ascii_uppercase, key=lambda ch: ch in used):
        g = _fallback(required, filler)
        if _valid(g, required, forbidden):
            best = g
            break
    n = 2
    while best is None:
        # Every letter is in some forbidden word: keep the layout but choose filler cell by cell.
        layout = _fallback(required, ".", n)
        n = len(layout)
        g = _Greedy(n, required, forbidden, None, rng).fill_layout(layout)
        if g is not None and _valid(g, required, forbidden):
            best = g
        n += 1

    deadline = start + TIME_LIMIT
    lo, hi = 1, len(best)
    while lo < hi and time.perf_counter() < deadline:
        mid = (lo + hi) // 2
        g = _attempt(
            mid, required, forbidden, min(deadline, time.perf_counter() + SLICE), rng
        )
        if g is not None:
            best, hi = g, mid
        else:
            lo = mid + 1  # impossible, or too hard to crack in a slice

    while len(best) > 1 and time.perf_counter() < deadline:
        g = _attempt(len(best) - 1, required, forbidden, deadline, rng)
        if g is None:
            break
        best = g
    return best
