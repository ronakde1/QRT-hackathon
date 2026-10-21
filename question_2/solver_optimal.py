"""Provably smallest torus word-search grid, no time limit, standard library only.

Every required word must appear in a straight line (8 directions, wrapping on a
torus); no forbidden word may appear anywhere.

Sizes N = 1, 2, ... are each searched exhaustively, so the first N with a grid
is optimal. The search places required words one at a time:
  * every placement of every word is precomputed; per-placement counters of
    matched/conflicting cells are updated incrementally as cells are set, so
    picking the word with the fewest live placements (fail-first) is cheap;
  * placements overlapping the most existing letters are tried first;
  * once a placement's subtree is exhausted it is banned for the remaining
    sibling branches (any grid containing it was already ruled out);
  * the longest word is pinned to (0, 0) heading E or SE, which loses nothing
    because the torus is invariant under translation and the square's symmetries;
  * a partial grid completing a forbidden word is rejected immediately.
Empty cells are finally filled with a letter absent from every forbidden word,
or, if none exists, by exhaustive backtracking.
"""
import re
import string
import sys

DIRS = [(0, 1), (1, 0), (1, 1), (1, -1), (0, -1), (-1, 0), (-1, -1), (-1, 1)]
AXES = [(0, 1), (1, 0), (1, 1), (1, -1)]

sys.setrecursionlimit(100000)


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


def _fallback(required, filler):
    """Rows of words separated by filler, alternating with all-filler rows."""
    n = max(len(required[0]) + 1, 2)
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


def _cells(word, n, r, c, dr, dc):
    """Sorted (cell, letter) pairs for word at (r, c) heading (dr, dc), or None if it wraps inconsistently."""
    out = {}
    for k, ch in enumerate(word):
        cell = ((r + k * dr) % n) * n + (c + k * dc) % n
        if out.setdefault(cell, ch) != ch:
            return None
    return tuple(sorted(out.items()))


class _Exact:
    def __init__(self, n, required, forbidden):
        self.n = n
        self.words = required
        self.grid = ["."] * (n * n)

        # Placements as parallel arrays; cover[cell][letter] lists placements needing that letter there.
        self.pword, self.pcells, self.psize, self.wpl = [], [], [], [[] for _ in required]
        self.cover = [{} for _ in range(n * n)]
        every = [(r, c, dr, dc) for r in range(n) for c in range(n) for dr, dc in DIRS]
        for wi, w in enumerate(required):
            starts = [(0, 0, 0, 1), (0, 0, 1, 1)] if wi == 0 else every
            for key in dict.fromkeys(p for p in (_cells(w, n, *s) for s in starts) if p is not None):
                i = len(self.pword)
                self.pword.append(wi)
                self.pcells.append(key)
                self.psize.append(len(key))
                self.wpl[wi].append(i)
                for cell, ch in key:
                    self.cover[cell].setdefault(ch, []).append(i)

        count = len(self.pword)
        self.matched = [0] * count
        self.dead = [0] * count  # conflicting cells, plus one if banned
        self.banned = [False] * count
        self.alive = [len(p) for p in self.wpl]
        self.sat = [0] * len(required)
        self.conflict = 0  # banned placements that are fully present

        self.forb_re = re.compile("|".join(sorted({f for w in forbidden for f in (w, w[::-1])}))) if forbidden else None
        self.reach = max((len(f) for f in forbidden), default=1) - 1
        used = set("".join(forbidden))
        self.safe = next((ch for ch in string.ascii_uppercase if ch not in used), None)
        freq = {ch: sum(f.count(ch) for f in forbidden) for ch in string.ascii_uppercase}
        self.fill_order = sorted(string.ascii_uppercase, key=freq.get)

    def _set(self, cell, x):
        self.grid[cell] = x
        for ch, lst in self.cover[cell].items():
            if ch == x:
                for i in lst:
                    self.matched[i] += 1
                    if self.matched[i] == self.psize[i]:
                        if self.banned[i]:
                            self.conflict += 1
                        else:
                            self.sat[self.pword[i]] += 1
            else:
                for i in lst:
                    self.dead[i] += 1
                    if self.dead[i] == 1:
                        self.alive[self.pword[i]] -= 1

    def _unset(self, cell):
        x = self.grid[cell]
        self.grid[cell] = "."
        for ch, lst in self.cover[cell].items():
            if ch == x:
                for i in lst:
                    if self.matched[i] == self.psize[i]:
                        if self.banned[i]:
                            self.conflict -= 1
                        else:
                            self.sat[self.pword[i]] -= 1
                    self.matched[i] -= 1
            else:
                for i in lst:
                    self.dead[i] -= 1
                    if self.dead[i] == 0:
                        self.alive[self.pword[i]] += 1

    def _ban(self, i, on):
        self.banned[i] = on
        self.dead[i] += 1 if on else -1
        if self.dead[i] == (1 if on else 0):
            self.alive[self.pword[i]] += -1 if on else 1

    def _completes_forbidden(self, cells):
        if self.forb_re is None:
            return False
        g, n, reach = self.grid, self.n, self.reach
        for cell in cells:
            r, c = divmod(cell, n)
            for dr, dc in AXES:
                seg = "".join(g[((r + k * dr) % n) * n + (c + k * dc) % n] for k in range(-reach, reach + 1))
                if self.forb_re.search(seg):
                    return True
        return False

    def solve(self):
        if any(a == 0 for a in self.alive):
            return None
        g = self._search()
        n = self.n
        return None if g is None else ["".join(g[r * n:(r + 1) * n]) for r in range(n)]

    def _search(self):
        best, best_alive = None, None
        for wi in range(len(self.words)):
            if self.sat[wi]:
                continue
            a = self.alive[wi]
            if a == 0:
                return None
            if best is None or a < best_alive:
                best, best_alive = wi, a
        if best is None:
            return self._fill()

        grid, matched, psize = self.grid, self.matched, self.psize
        opts = [i for i in self.wpl[best] if self.dead[i] == 0]
        opts.sort(key=lambda i: psize[i] - matched[i])
        tried = []
        result = None
        for i in opts:
            if self.dead[i]:  # killed by an earlier sibling's ban? (can't be, but stay safe)
                continue
            new = [(cell, ch) for cell, ch in self.pcells[i] if grid[cell] == "."]
            for cell, ch in new:
                self._set(cell, ch)
            if self.conflict == 0 and not self._completes_forbidden([cell for cell, _ in new]):
                result = self._search()
            for cell, _ in reversed(new):
                self._unset(cell)
            if result is not None:
                break
            # Every grid containing placement i has now been ruled out.
            self._ban(i, True)
            tried.append(i)
        for i in tried:
            self._ban(i, False)
        return result

    def _fill(self):
        if self.safe:
            # A letter absent from every forbidden word can never complete one.
            return [self.safe if x == "." else x for x in self.grid]
        return self._fill_from([c for c, x in enumerate(self.grid) if x == "."], 0)

    def _fill_from(self, empty, k):
        if k == len(empty):
            return list(self.grid)
        cell = empty[k]
        for ch in self.fill_order:
            self.grid[cell] = ch
            if not self._completes_forbidden((cell,)):
                result = self._fill_from(empty, k + 1)
                if result is not None:
                    self.grid[cell] = "."
                    return result
        self.grid[cell] = "."
        return None


def generate_grid(required_words: list[str], forbidden_words: list[str]) -> list[str]:
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
        (w for w in required if not any(w != o and (w in o or w[::-1] in o) for o in required)),
        key=len,
        reverse=True,
    )

    # A guaranteed grid caps the search; without a safe filler letter the search alone must find one.
    used = set("".join(forbidden))
    cap = None
    for filler in sorted(string.ascii_uppercase, key=lambda ch: ch in used):
        g = _fallback(required, filler)
        if _valid(g, required, forbidden):
            cap = g
            break

    n = 1
    while cap is None or n < len(cap):
        g = _Exact(n, required, forbidden).solve()
        if g is not None:
            assert _valid(g, required, forbidden), "verification failed"
            return g
        n += 1
    return cap


if __name__ == "__main__":
    import time

    required_words = ["PYTHON", "QUANT", "TRADING", "ALPHA", "MARKET", "HEDGE", "RISK", "ORDER", "SIGNAL", "PRICE"]
    forbidden_words = ["CAT", "DOG", "TOP", "EAR", "TEN"]
    t0 = time.perf_counter()
    grid = generate_grid(required_words, forbidden_words)
    print(len(grid), f"{time.perf_counter() - t0:.3f}s")
    print("\n".join(grid))
