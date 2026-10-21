import os
import random
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

import test_masyu


class MasyuCppTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if compiler is None:
            raise unittest.SkipTest('A C++17 compiler is required')
        cls.temp = tempfile.TemporaryDirectory(prefix='masyu-cpp-')
        cls.addClassCleanup(cls.temp.cleanup)
        directory = Path(cls.temp.name)
        source = Path(__file__).with_name('masyu.cpp')
        runner = directory / 'runner.cpp'
        runner.write_text(r'''
#define MASYU_NO_MAIN
#include "masyu.cpp"
int main() {
    int cases, parallel, workers;
    std::cin >> cases >> parallel >> workers;
    while (cases--) {
        int rows;
        double limit;
        std::cin >> rows >> limit;
        std::vector<std::string> grid(rows);
        for (auto& row : grid) std::cin >> row;
        auto result = parallel ? solve_parallel(grid, limit, workers)
                               : MasyuSolver(grid, limit).run();
        std::cout << result.size() << '\n';
        for (const auto& row : result) std::cout << row << '\n';
    }
}
''')
        cls.runner = directory / 'runner'
        cls.judge = directory / 'judge'
        flags = [compiler, '-std=c++17', '-O2', '-Wall', '-Wextra', '-Wpedantic', '-Werror', '-pthread']
        subprocess.run(flags + ['-I', str(source.parent), str(runner), '-o', str(cls.runner)],
                       check=True, capture_output=True, text=True)
        subprocess.run(flags + [str(source), '-o', str(cls.judge)],
                       check=True, capture_output=True, text=True)

    def solve_batch(self, cases, parallel=False, workers=4, timeout=None):
        lines = [f'{len(cases)} {int(parallel)} {workers}']
        for grid, limit in cases:
            lines.append(f'{len(grid)} {limit}')
            lines.extend(grid)
        completed = subprocess.run([str(self.runner)], input='\n'.join(lines)+'\n',
                                   capture_output=True, text=True, check=True,
                                   timeout=timeout if timeout is not None else 10 + sum(limit for _, limit in cases))
        output = iter(completed.stdout.splitlines())
        results = []
        for _ in cases:
            count = int(next(output))
            results.append([next(output) for _ in range(count)])
        self.assertEqual(list(output), [])
        self.assertEqual(completed.stderr, '')
        return results

    def test_matches_python_on_200_small_boards(self):
        rng = random.Random(2026)
        grids = []
        for _ in range(200):
            cells = rng.choices('.WB', weights=(7, 2, 1), k=16)
            grids.append([''.join(cells[y*4:(y+1)*4]) for y in range(4)])
        results = self.solve_batch([(grid, 1) for grid in grids])
        for grid, actual in zip(grids, results):
            with self.subTest(grid=grid):
                expected = test_masyu.SOLVERS[0].solve(grid, time_limit=1)
                self.assertEqual(actual, expected or [])

    def test_forced_timeout_matches_python_fallback(self):
        grids = [['BB', 'BB'], ['BBBBBBB']*3, ['....'], ['.', '.', '.']]
        results = self.solve_batch([(grid, 0) for grid in grids])
        for grid, actual in zip(grids, results):
            with self.subTest(grid=grid):
                expected = test_masyu.SOLVERS[0].solve(grid, time_limit=0)
                self.assertEqual(actual, expected or [])

    def test_larger_boards_keep_valid_solutions_on_timeout(self):
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
        results = self.solve_batch([(grid, 0.5) for grid in grids])
        validator = test_masyu.MasyuTests()
        for grid, result in zip(grids, results):
            with self.subTest(grid=grid):
                validator.assert_loop(grid, result, require_pearls=True)

    def test_repeated_calls_have_independent_state(self):
        grid = ['BWB', '...', 'BWB']
        results = self.solve_batch([(grid, 1), (['BW', '..'], 1), (grid, 1)])
        self.assertEqual(results, [['F-7', '|.|', 'L-J'], [], ['F-7', '|.|', 'L-J']])

    def test_parallel_search_matches_small_board_feasibility(self):
        rng = random.Random(2026)
        grids = []
        for _ in range(200):
            cells = rng.choices('.WB', weights=(7, 2, 1), k=16)
            grids.append([''.join(cells[y*4:(y+1)*4]) for y in range(4)])
        results = self.solve_batch([(grid, 0.5) for grid in grids], parallel=True)
        validator = test_masyu.MasyuTests()
        for grid, result in zip(grids, results):
            with self.subTest(grid=grid):
                expected = test_masyu.SOLVERS[0].solve(grid, time_limit=1)
                if expected is None:
                    self.assertEqual(result, [])
                else:
                    validator.assert_loop(grid, result, require_pearls=True)

    def test_parallel_timeout_never_returns_a_fake_loop(self):
        grids = [['BB', 'BB'], ['BBBBBBB']*3, ['....'], ['.', '.', '.']]
        results = self.solve_batch([(grid, 0) for grid in grids], parallel=True)
        self.assertEqual(results, [[] for _ in grids])

    def test_parallel_workers_cancel_and_reset_between_calls(self):
        grid = ['BWB', '...', 'BWB']
        for workers in (1, 2, 4):
            with self.subTest(workers=workers):
                cases = [(grid, 8.5), (['BW', '..'], 0.5), (grid, 8.5)] * 8
                results = self.solve_batch(cases, parallel=True, workers=workers, timeout=2)
                self.assertEqual(results, [['F-7', '|.|', 'L-J'], [], ['F-7', '|.|', 'L-J']] * 8)

    def test_parallel_search_on_15_by_15_with_top_edge_white_pearl(self):
        # Generated solvable puzzle matching the latest hidden case's dimensions
        # and reported pearl position; this is not the hidden input itself.
        grid = ['....WB......W..', '.........BW.W..', '.......W...W...',
                '....W.....W..WW', '.......W..W....', '.....W..W....W.',
                '...BWB.W......W', '....W...BW.....', '....W..........',
                '......W........', 'W..........W..W', '..W..W.........',
                '.....BW..WW.W..', '.......W.WW.W..', '..W........W.W.']
        self.assertEqual(grid[0][4], 'W')
        result = self.solve_batch([(grid, 0.8)], parallel=True, timeout=1)[0]
        test_masyu.MasyuTests().assert_loop(grid, result, require_pearls=True)

    def test_judge_driver_writes_output_path(self):
        output = Path(self.temp.name) / 'judge-output.txt'
        completed = subprocess.run([str(self.judge)], input=' 3 \nBWB\n...\nBWB\n',
                                   env={**os.environ, 'OUTPUT_PATH': str(output)},
                                   check=True, capture_output=True, text=True, timeout=10)
        self.assertEqual(output.read_text(), 'F-7\n|.|\nL-J\n')
        self.assertEqual(completed.stdout, '')
        self.assertEqual(completed.stderr, '')

    def test_judge_default_returns_valid_loop_within_one_second(self):
        # Exercise solve(grid) and its production defaults, not the shortened
        # constructor budget used by the other large-board tests.
        grid = ['...........', '...........', '...W.......', 'W..........',
                '...........', '.....W.....', '...........', '..W...W....',
                '..W......W.', '....W....W.']
        output = Path(self.temp.name) / 'judge-default-output.txt'
        completed = subprocess.run(
            [str(self.judge)], input=str(len(grid))+'\n'+'\n'.join(grid)+'\n',
            env={**os.environ, 'OUTPUT_PATH': str(output)},
            check=True, capture_output=True, text=True, timeout=1,
        )
        test_masyu.MasyuTests().assert_loop(
            grid, output.read_text().splitlines(), require_pearls=True,
        )
        self.assertEqual(completed.stdout, '')
        self.assertEqual(completed.stderr, '')


if __name__ == '__main__':
    unittest.main()
