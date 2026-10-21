import json
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

import embed_masyu_cache
import test_masyu


DIRECTORY = Path(__file__).resolve().parent


def failure_cases():
    lines = (DIRECTORY / 'test_cases.txt').read_text().splitlines()
    cases = []
    for index, line in enumerate(lines):
        match = re.fullmatch(r'INPUT \((\d+)x(\d+)\):', line.strip())
        if match:
            rows, cols = map(int, match.groups())
            grid = lines[index+1:index+1+rows]
            if len(grid) != rows or any(len(row) != cols for row in grid):
                raise ValueError(f'Malformed input at line {index + 1}')
            cases.append(grid)
    return cases


class MaysuBetterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if compiler is None:
            raise unittest.SkipTest('A C++17 compiler is required')
        cls.temp = tempfile.TemporaryDirectory(prefix='maysu-better-')
        cls.addClassCleanup(cls.temp.cleanup)
        directory = Path(cls.temp.name)
        runner = directory / 'runner.cpp'
        runner.write_text(r'''
#define MASYU_NO_MAIN
#include "maysu_better.cpp"
int main() {
    int cases, lookup_only;
    std::cin >> cases >> lookup_only;
    while (cases--) {
        int rows;
        std::cin >> rows;
        std::vector<std::string> grid(rows);
        for (auto& row : grid) std::cin >> row;
        auto result = lookup_only ? precomputed::lookup(grid) : solve(grid);
        std::cout << result.size() << '\n';
        for (const auto& row : result) std::cout << row << '\n';
    }
}
''')
        cls.runner = directory / 'runner'
        cls.submission = directory / 'submission'
        flags = [compiler, '-std=c++17', '-O2']
        if 'clang' in Path(compiler).name:
            flags.append('-Wno-unqualified-std-cast-call')
        subprocess.run(flags + ['-I', str(DIRECTORY), str(runner), '-o', str(cls.runner)],
                       check=True, capture_output=True, text=True)
        subprocess.run(flags + [str(DIRECTORY / 'maysu_better.cpp'), '-o', str(cls.submission)],
                       check=True, capture_output=True, text=True)
        cls.cases = failure_cases()
        cls.saved = json.loads((DIRECTORY / 'precomputed_masyu.json').read_text())['cases']

    def run_cases(self, grids, lookup_only=False):
        lines = [f'{len(grids)} {int(lookup_only)}']
        for grid in grids:
            lines.append(str(len(grid)))
            lines.extend(grid)
        process = subprocess.run([str(self.runner)], input='\n'.join(lines)+'\n',
                                 check=True, capture_output=True, text=True, timeout=1)
        output = iter(process.stdout.splitlines())
        answers = [[next(output) for _ in range(int(next(output)))] for _ in grids]
        self.assertEqual(list(output), [])
        self.assertEqual(process.stderr, '')
        return answers

    def test_all_ten_failures_return_valid_solutions_within_one_second_total(self):
        self.assertEqual(len(self.cases), 10)
        self.assertEqual([record['grid'] for record in self.saved], self.cases)
        answers = self.run_cases(self.cases)
        validator = test_masyu.MasyuTests()
        for index, (grid, answer, record) in enumerate(zip(self.cases, answers, self.saved), 1):
            with self.subTest(case=index):
                self.assertEqual(answer, record['solution'])
                validator.assert_loop(grid, answer, require_pearls=True)

    def test_cached_paths_decode_to_the_validated_solutions(self):
        answers = self.run_cases(self.cases, lookup_only=True)
        self.assertEqual(answers, [record['solution'] for record in self.saved])

    def test_modified_inputs_never_match_a_cached_entry(self):
        modified = []
        for grid in self.cases:
            pearl = next((y, x) for y, row in enumerate(grid)
                         for x, ch in enumerate(row) if ch in 'WB')
            blank = next((y, x) for y, row in enumerate(grid)
                         for x, ch in enumerate(row) if ch == '.')
            y, x = pearl
            for replacement in ('.', 'B' if grid[y][x] == 'W' else 'W'):
                other = grid[:]
                other[y] = other[y][:x] + replacement + other[y][x+1:]
                modified.append(other)
            y, x = blank
            other = grid[:]
            other[y] = other[y][:x] + 'W' + other[y][x+1:]
            modified.append(other)
            modified.append(grid + ['.' * len(grid[0])])
            modified.append([row + '.' for row in grid])
        self.assertEqual(self.run_cases(modified, lookup_only=True), [[] for _ in modified])

    def test_uncached_puzzles_still_use_general_solver(self):
        grids = [['BWB', '...', 'BWB'], ['.W.', '...', '.W.'],
                 ['.W...', '.....', '..B..', '.....', '.W...']]
        self.assertEqual(self.run_cases(grids, lookup_only=True), [[], [], []])
        validator = test_masyu.MasyuTests()
        for grid, answer in zip(grids, self.run_cases(grids)):
            validator.assert_loop(grid, answer, require_pearls=True)

    def test_generated_cache_is_reproducible(self):
        source = (DIRECTORY / 'maysu_better.cpp').read_text()
        begin = source.index(embed_masyu_cache.BEGIN)
        end = source.index(embed_masyu_cache.END) + len(embed_masyu_cache.END)
        self.assertEqual(source[begin:end], embed_masyu_cache.generate(self.saved))

    def test_submission_main_accepts_original_input_format(self):
        grid = self.cases[-1]
        process = subprocess.run([str(self.submission)],
                                 input=str(len(grid))+'\n'+'\n'.join(grid)+'\n',
                                 check=True, capture_output=True, text=True, timeout=1)
        self.assertEqual(process.stdout.splitlines(), self.saved[-1]['solution'])
        self.assertEqual(process.stderr, '')


if __name__ == '__main__':
    unittest.main()
