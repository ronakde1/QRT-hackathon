import importlib.util
import random
import unittest
from itertools import chain, repeat
from pathlib import Path
from unittest.mock import patch


def load_solver(filename):
    spec = importlib.util.spec_from_file_location(
        'masyu', Path(__file__).with_name(filename)
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SOLVERS = [load_solver(name) for name in ('masyu.py', 'masyu (1).py')]
PORTS = {
    '|': ((-1, 0), (1, 0)), '-': ((0, -1), (0, 1)),
    'L': ((-1, 0), (0, 1)), 'J': ((-1, 0), (0, -1)),
    'F': ((1, 0), (0, 1)), '7': ((1, 0), (0, -1)),
}


class MasyuTests(unittest.TestCase):
    def assert_loop(self, grid, result, require_pearls=False):
        self.assertIsNotNone(result)
        self.assertEqual(len(result), len(grid))
        self.assertTrue(all(len(row) == len(grid[0]) for row in result))
        self.assertTrue(all(ch in '.|-LJF7' for row in result for ch in row))
        used = {(y, x) for y, row in enumerate(result)
                for x, ch in enumerate(row) if ch != '.'}
        self.assertGreaterEqual(len(used), 4)
        neighbors = {}
        for y, x in used:
            neighbors[y, x] = []
            for dy, dx in PORTS[result[y][x]]:
                target = (y + dy, x + dx)
                self.assertIn(target, used)
                self.assertIn((-dy, -dx), PORTS[result[target[0]][target[1]]])
                neighbors[y, x].append(target)
        seen = set()
        stack = [next(iter(used))]
        while stack:
            cell = stack.pop()
            if cell not in seen:
                seen.add(cell)
                stack.extend(neighbors[cell])
        self.assertEqual(seen, used)
        if require_pearls:
            for y, row in enumerate(grid):
                for x, pearl in enumerate(row):
                    if pearl not in 'WB':
                        continue
                    self.assertIn((y, x), used)
                    adjacent = [result[ny][nx] for ny, nx in neighbors[y, x]]
                    if pearl == 'W':
                        self.assertIn(result[y][x], '|-')
                        self.assertTrue(any(ch in 'LJF7' for ch in adjacent))
                    else:
                        self.assertIn(result[y][x], 'LJF7')
                        self.assertTrue(all(ch in '|-' for ch in adjacent))

    def test_timeout_before_first_solution_returns_loop(self):
        for solver in SOLVERS:
            for rows, cols in ((2, 2), (3, 7), (15, 15)):
                with self.subTest(solver=solver.__file__, rows=rows, cols=cols):
                    grid = ['B' * cols for _ in range(rows)]
                    with patch.object(solver.time, 'monotonic',
                                      side_effect=chain([0], repeat(8.5))):
                        result = solver.solve(grid)
                    self.assert_loop(grid, result)

    def test_timeout_during_propagation_returns_loop(self):
        # These pearls fix the only candidate rectangle, which is invalid.
        grid = ['B.B', '.W.', 'B.B']
        for solver in SOLVERS:
            with self.subTest(solver=solver.__file__):
                with patch.object(solver.time, 'monotonic',
                                  side_effect=chain([0, 0, 0], repeat(9))):
                    result = solver.solve(grid)
                self.assert_loop(grid, result)

    def test_timeout_preserves_solution_already_found(self):
        # The central black pearl makes every rectangular loop invalid.
        grid = ['.W...', '.....', '..B..', '.....', '.W...']
        for solver in SOLVERS:
            with self.subTest(solver=solver.__file__):
                with patch.object(solver.time, 'monotonic',
                                  side_effect=chain(repeat(0, 40), repeat(9))) as clock:
                    result = solver.solve(grid)
                self.assertGreater(clock.call_count, 40)
                self.assert_loop(grid, result, require_pearls=True)

    def test_timeout_returns_valid_seed_before_main_search(self):
        grids = (
            ['BWB', '...', 'BWB'],
            ['B.B', 'W.W', 'B.B'],
            ['......', '..BWB.', '......', '..BWB.', '......'],
            ['....', '....', '....'],
        )
        for solver in SOLVERS:
            for grid in grids:
                with self.subTest(solver=solver.__file__, grid=grid):
                    with patch.object(solver.time, 'monotonic',
                                      side_effect=chain([0, 0], repeat(9))) as clock:
                        result = solver.solve(grid)
                    self.assertEqual(clock.call_count, 3)
                    self.assert_loop(grid, result, require_pearls=True)

    def test_invalid_rectangles_are_not_saved_as_solutions(self):
        grids = (
            ['B.B', 'B.B'],  # Black pearls need straight neighbors.
            ['W.B', '...', 'B.B'],  # White pearls cannot turn.
            ['B.W.B', '.....', '.....', '.....', 'B...B'],  # No adjacent turn.
            ['B.B', '.W.', 'B.B'],  # Interior pearl is not visited.
        )
        for solver in SOLVERS:
            for grid in grids:
                with self.subTest(solver=solver.__file__, grid=grid):
                    with patch.object(solver.time, 'monotonic',
                                      side_effect=chain([0, 0], repeat(9))):
                        result = solver.solve(grid)
                    self.assert_loop(grid, result)
                    # None of these full-size rectangles is valid. Retain the
                    # original four-cell geometric fallback on immediate expiry.
                    self.assertEqual(sum(ch != '.' for row in result for ch in row), 4)

    def test_completed_search_still_obeys_pearl_rules(self):
        for solver in SOLVERS:
            for grid in (['B.B', '...', 'B.B'], ['.W.', '...', '.W.']):
                with self.subTest(solver=solver.__file__, grid=grid):
                    self.assert_loop(grid, solver.solve(grid), require_pearls=True)

    def test_finds_valid_loops_on_larger_boards_with_short_budget(self):
        # Generated solvable boards, including the reported pearl position.
        # The sparse boards previously exhausted the whole 8.5-second budget.
        grids = (
            ['.W..WWBB..B', '....WBWW...', '.....W.W...', '........B..',
             '.WW.WW.....', '.....W.W...', '....W....W.', '.W.W....W..',
             '.WWW.......', '.........W.'],
            ['...........', '...........', '...W.......', 'W..........',
             '...........', '.....W.....', '...........', '..W...W....',
             '..W......W.', '....W....W.'],
            ['...........', 'W....WW....', '......W....', '...........',
             '.W.....W...', '....W...W.W', '.......W...', '..W........',
             'W..WW.....W', '...........'],
        )
        self.assertEqual(grids[0][0][6], 'B')
        for solver in SOLVERS:
            for grid in grids:
                with self.subTest(solver=solver.__file__, grid=grid):
                    result = solver.solve(grid, time_limit=0.5)
                    self.assert_loop(grid, result, require_pearls=True)

    def test_small_boards_match_exhaustive_loop_enumeration(self):
        # Independent oracle: enumerate every simple loop on a 4x4 board.
        rows = cols = 4
        neighbors = []
        for i in range(rows*cols):
            y, x = divmod(i, cols)
            neighbors.append([ny*cols+nx
                              for ny, nx in ((y-1,x), (y+1,x), (y,x-1), (y,x+1))
                              if 0 <= ny < rows and 0 <= nx < cols])
        loops = []

        def enumerate_cycles(path, used):
            start = path[0]
            for j in neighbors[path[-1]]:
                if j == start:
                    if len(path) < 4 or path[1] > path[-1]:
                        continue
                    straight = []
                    for k in range(len(path)):
                        before, after = path[k-1], path[(k+1) % len(path)]
                        straight.append(before//cols == after//cols
                                        or before % cols == after % cols)
                    white = black = 0
                    for k, i in enumerate(path):
                        previous = straight[k-1]
                        following = straight[(k+1) % len(path)]
                        if straight[k] and not (previous and following):
                            white |= 1 << i
                        if not straight[k] and previous and following:
                            black |= 1 << i
                    loops.append((white, black, len(path)))
                elif j > start and not used & (1 << j):
                    enumerate_cycles(path+[j], used | (1 << j))

        for start in range(rows*cols):
            enumerate_cycles([start], 1 << start)
        self.assertEqual(len(loops), 213)
        rng = random.Random(2026)
        for case in range(200):
            cells = rng.choices('.WB', weights=(7, 2, 1), k=rows*cols)
            grid = [''.join(cells[y*cols:(y+1)*cols]) for y in range(rows)]
            white = sum(1 << i for i, p in enumerate(cells) if p == 'W')
            black = sum(1 << i for i, p in enumerate(cells) if p == 'B')
            lengths = [length for w, b, length in loops
                       if white & w == white and black & b == black]
            for solver in SOLVERS:
                with self.subTest(solver=solver.__file__, case=case):
                    result = solver.solve(grid, time_limit=1)
                    if lengths:
                        self.assert_loop(grid, result, require_pearls=True)
                        self.assertEqual(sum(ch != '.' for row in result for ch in row),
                                         min(lengths))
                    else:
                        self.assertIsNone(result)

    def test_exhausted_unsatisfiable_search_still_returns_none(self):
        for solver in SOLVERS:
            with self.subTest(solver=solver.__file__):
                self.assertIsNone(solver.solve(['BW', '..']))

    def test_narrow_boards_cannot_return_a_loop(self):
        for solver in SOLVERS:
            for grid in (['....'], ['.', '.', '.']):
                with self.subTest(solver=solver.__file__, grid=grid):
                    with patch.object(solver.time, 'monotonic',
                                      side_effect=chain([0], repeat(9))):
                        self.assertIsNone(solver.solve(grid))


if __name__ == '__main__':
    unittest.main()
