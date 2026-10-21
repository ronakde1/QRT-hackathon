#include <algorithm>
#include <array>
#include <chrono>
#include <cctype>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using namespace std;

namespace {

constexpr int N = 1, E = 2, S = 4, W = 8;
constexpr array<int, 7> SHAPES = {0, N | S, E | W, N | E, N | W, S | E, S | W};
constexpr array<int, 4> DIRS = {N, E, S, W};
constexpr char CHARS[] = ".|-LJF7";
constexpr int FULL = (1 << 7) - 1;
constexpr int STRAIGHT = (1 << 1) | (1 << 2);
constexpr int TURN = FULL & ~(1 | STRAIGHT);
// Leave headroom for input, output, and unwinding under a one-second limit.
constexpr double DEFAULT_TIME_LIMIT = 0.80;
constexpr double IMPROVEMENT_TIME_LIMIT = 0.05;

struct Tables {
    array<vector<int>, FULL + 1> states;
    array<int, 4> edge_mask{}, no_edge_mask{};
    array<int, FULL + 1> possible{}, forced{}, count{}, single_state{};

    Tables() {
        single_state.fill(-1);
        for (int a = 0; a < 7; ++a) {
            single_state[1 << a] = a;
            for (int d = 0; d < 4; ++d) {
                if (SHAPES[a] & DIRS[d]) edge_mask[d] |= 1 << a;
            }
        }
        for (int d = 0; d < 4; ++d) no_edge_mask[d] = FULL ^ edge_mask[d];
        for (int mask = 0; mask <= FULL; ++mask) {
            for (int a = 0; a < 7; ++a) {
                if (mask & (1 << a)) states[mask].push_back(a);
            }
            count[mask] = static_cast<int>(states[mask].size());
            for (int d = 0; d < 4; ++d) {
                if (mask & edge_mask[d]) possible[mask] |= DIRS[d];
                if (mask && !(mask & no_edge_mask[d])) forced[mask] |= DIRS[d];
            }
        }
    }
};

const Tables& tables() {
    static const Tables value;
    return value;
}

double monotonic_seconds() {
    return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();
}

struct Timeout {};
struct RestartSearch {};

struct PearlConstraint {
    vector<int> scope;
    vector<vector<int>> patterns;
};

class MasyuSolver {
public:
    explicit MasyuSolver(const vector<string>& input, double limit = DEFAULT_TIME_LIMIT)
        : start(monotonic_seconds()), time_limit(limit), deadline(start + limit),
          phase_deadline(deadline), improvement_deadline(deadline), grid(input), t(tables()),
          rows(static_cast<int>(input.size())),
          cols(rows ? static_cast<int>(input[0].size()) : 0), size(rows * cols),
          nbr(size), domains(size, FULL), best_len(size + 1),
          pearl_neighbors(size, 0), watchers(size) {
        for (int i = 0; i < size; ++i) {
            nbr[i].fill(-1);
            int y = i / cols, x = i % cols;
            if (y) nbr[i][0] = i - cols;
            if (x < cols - 1) nbr[i][1] = i + 1;
            if (y < rows - 1) nbr[i][2] = i + cols;
            if (x) nbr[i][3] = i - 1;
            for (int d = 0; d < 4; ++d) {
                if (nbr[i][d] < 0) domains[i] &= t.no_edge_mask[d];
            }
            char p = grid[y][x];
            if (p == 'W') domains[i] &= STRAIGHT;
            if (p == 'B') domains[i] &= TURN;
            if (p == 'W' || p == 'B') pearls.emplace_back(i, p);
        }
        for (int i = 0; i < size; ++i) {
            for (int d : {1, 2}) {
                if (nbr[i][d] >= 0) edges.push_back({i, nbr[i][d], d});
            }
            for (int j : nbr[i]) {
                if (j >= 0 && (grid[j / cols][j % cols] == 'W'
                               || grid[j / cols][j % cols] == 'B')) {
                    ++pearl_neighbors[i];
                }
            }
        }
        // A white pearl has two patterns per orientation: which neighbor turns.
        for (auto [i, p] : pearls) {
            PearlConstraint constraint;
            constraint.scope.push_back(i);
            for (int j : nbr[i]) {
                if (j >= 0) constraint.scope.push_back(j);
            }
            for (int a : t.states[domains[i]]) {
                vector<int> ds;
                for (int d = 0; d < 4; ++d) {
                    if (SHAPES[a] & DIRS[d]) ds.push_back(d);
                }
                for (int variant = 0; variant < (p == 'B' ? 1 : 2); ++variant) {
                    int turn_at = p == 'B' ? -1 : variant;
                    vector<int> pattern(constraint.scope.size(), FULL);
                    pattern[0] = 1 << a;
                    for (int pos = 0; pos < static_cast<int>(ds.size()); ++pos) {
                        int d = ds[pos];
                        int mask = p == 'B' ? 1 << (d % 2 == 0 ? 1 : 2)
                                           : t.edge_mask[(d + 2) % 4];
                        if (pos == turn_at) mask &= TURN;
                        auto it = find(constraint.scope.begin(), constraint.scope.end(), nbr[i][d]);
                        pattern[it - constraint.scope.begin()] = mask;
                    }
                    constraint.patterns.push_back(std::move(pattern));
                }
            }
            int ci = static_cast<int>(constraints.size());
            for (int j : constraint.scope) watchers[j].push_back(ci);
            constraints.push_back(std::move(constraint));
        }
    }

    vector<string> run() {
        if (size == 0) return {};
        bool timed_out = false;
        try {
            seed_rectangle();
            array<double, 4> phase_limits = {
                min(0.025, time_limit * 0.15), min(0.075, time_limit * 0.35),
                min(0.175, time_limit * 0.6), time_limit
            };
            for (strategy = 0; strategy < 4; ++strategy) {
                if (best_len == 4) break;  // No grid loop can be shorter.
                phase_deadline = start + phase_limits[strategy];
                try {
                    dfs(domains);
                    break;
                } catch (const RestartSearch&) {
                    continue;
                }
            }
        } catch (const Timeout&) {
            timed_out = true;
        }
        if (best.empty()) {
            if (timed_out && rows >= 2 && cols >= 2) {
                // Matches Python's last-resort geometric fallback. This loop
                // need not satisfy the pearls and must never prune the search.
                vector<string> fallback(rows, string(cols, '.'));
                fallback[0][0] = 'F'; fallback[0][1] = '7';
                fallback[1][0] = 'L'; fallback[1][1] = 'J';
                return fallback;
            }
            return {};  // Python's None.
        }
        vector<string> result(rows, string(cols, '.'));
        for (int i = 0; i < size; ++i) result[i / cols][i % cols] = CHARS[t.single_state[best[i]]];
        return result;
    }

private:
    double start, time_limit, deadline, phase_deadline, improvement_deadline;
    const vector<string>& grid;
    const Tables& t;
    int rows, cols, size;
    vector<array<int, 4>> nbr;
    vector<int> domains, best;
    int best_len;
    int strategy = 0;
    vector<pair<int, char>> pearls;
    vector<array<int, 3>> edges;
    vector<int> pearl_neighbors;
    vector<vector<int>> watchers;
    vector<PearlConstraint> constraints;

    void check_timeout() const {
        double now = monotonic_seconds();
        if (now >= deadline || now >= improvement_deadline) throw Timeout{};
        if (best.empty() && now >= phase_deadline) throw RestartSearch{};
    }

    void save_solution(vector<int> candidate, int length) {
        if (best.empty()) {
            // Start this budget only once: repeated improvements must not keep
            // a valid answer waiting until the judge terminates the process.
            improvement_deadline = min(deadline, monotonic_seconds() + IMPROVEMENT_TIME_LIMIT);
        }
        best = std::move(candidate);
        best_len = length;
    }

    void seed_rectangle() {
        if (rows < 2 || cols < 2) return;
        vector<array<int, 4>> bounds;
        if (pearls.empty()) {
            bounds.push_back({0, 1, 0, 1});
        } else {
            int top = rows, bottom = -1, left = cols, right = -1;
            for (auto [i, p] : pearls) {
                (void)p;
                top = min(top, i / cols); bottom = max(bottom, i / cols);
                left = min(left, i % cols); right = max(right, i % cols);
            }
            set<int> tops = {0, top, max(0, top - 1), max(0, top - 2)};
            set<int> bottoms = {rows - 1, bottom, min(rows - 1, bottom + 1), min(rows - 1, bottom + 2)};
            set<int> lefts = {0, left, max(0, left - 1), max(0, left - 2)};
            set<int> rights = {cols - 1, right, min(cols - 1, right + 1), min(cols - 1, right + 2)};
            for (int a : tops) for (int b : bottoms) {
                for (int l : lefts) for (int h : rights) {
                    if (a < b && l < h) bounds.push_back({a, b, l, h});
                }
            }
            sort(bounds.begin(), bounds.end(), [](const auto& a, const auto& b) {
                return make_pair(a[1] - a[0] + a[3] - a[2], a)
                     < make_pair(b[1] - b[0] + b[3] - b[2], b);
            });
        }
        for (auto [top, bottom, left, right] : bounds) {
            check_timeout();
            bool valid = true;
            for (auto [i, p] : pearls) {
                int y = i / cols, x = i % cols;
                bool horizontal = y == top || y == bottom;
                bool vertical = x == left || x == right;
                if (p == 'B') {
                    valid = horizontal && vertical && bottom - top >= 2 && right - left >= 2;
                } else {
                    valid = (horizontal && !vertical && (x == left + 1 || x == right - 1))
                         || (vertical && !horizontal && (y == top + 1 || y == bottom - 1));
                }
                if (!valid) break;
            }
            if (!valid) continue;
            vector<int> candidate(size, 1);
            for (int x = left + 1; x < right; ++x) {
                candidate[top * cols + x] = candidate[bottom * cols + x] = 1 << 2;
            }
            for (int y = top + 1; y < bottom; ++y) {
                candidate[y * cols + left] = candidate[y * cols + right] = 1 << 1;
            }
            candidate[top * cols + left] = 1 << 5;
            candidate[top * cols + right] = 1 << 6;
            candidate[bottom * cols + left] = 1 << 3;
            candidate[bottom * cols + right] = 1 << 4;
            save_solution(std::move(candidate), 2 * (bottom - top + right - left));
            return;
        }
    }

    bool propagate(vector<int>& dom, int changed) {
        deque<int> queue;
        vector<unsigned char> queued(size, changed < 0);
        if (changed < 0) {
            for (int i = 0; i < size; ++i) queue.push_back(i);
        } else {
            queue.push_back(changed); queued[changed] = true;
        }
        auto narrow = [&](int i, int mask) {
            int value = dom[i] & mask;
            if (!value) return false;
            if (value != dom[i]) {
                dom[i] = value;
                if (!queued[i]) { queue.push_back(i); queued[i] = true; }
            }
            return true;
        };
        while (true) {
            int updates = 0;
            while (!queue.empty()) {
                if (updates++ % 64 == 0) check_timeout();
                int i = queue.front(); queue.pop_front(); queued[i] = false;
                if (!dom[i]) return false;
                for (int d = 0; d < 4; ++d) {
                    int j = nbr[i][d];
                    if (j < 0) continue;
                    int opposite = (d + 2) % 4;
                    if (!(dom[i] & t.edge_mask[d])) {
                        if (!narrow(j, t.no_edge_mask[opposite])) return false;
                    } else if (!(dom[i] & t.no_edge_mask[d])) {
                        if (!narrow(j, t.edge_mask[opposite])) return false;
                    }
                }
                for (int ci : watchers[i]) {
                    const auto& constraint = constraints[ci];
                    const auto& scope = constraint.scope;
                    array<int, 5> supports{};
                    for (const auto& pattern : constraint.patterns) {
                        bool supported = true;
                        for (size_t k = 0; k < scope.size(); ++k) {
                            if (!(dom[scope[k]] & pattern[k])) { supported = false; break; }
                        }
                        if (supported) {
                            for (size_t k = 0; k < scope.size(); ++k) supports[k] |= pattern[k];
                        }
                    }
                    for (size_t k = 0; k < scope.size(); ++k) {
                        if (!narrow(scope[k], supports[k])) return false;
                    }
                }
            }

            // Join mandatory edges, including those at undecided path ends.
            vector<int> parent(size), counts(size, 1), forced_edges(size);
            iota(parent.begin(), parent.end(), 0);
            auto root = [&](int i) {
                while (parent[i] != i) { parent[i] = parent[parent[i]]; i = parent[i]; }
                return i;
            };
            int cycle = -1;
            for (int i = 0; i < size; ++i) forced_edges[i] = t.forced[dom[i]];
            for (auto [i, j, d] : edges) {
                if (!(forced_edges[i] & DIRS[d])) continue;
                int a = root(i), b = root(j);
                if (a == b) { cycle = i; continue; }
                if (counts[a] < counts[b]) swap(a, b);
                parent[b] = a; counts[a] += counts[b];
            }
            vector<int> roots(size), required;
            for (int i = 0; i < size; ++i) {
                roots[i] = root(i);
                if (!(dom[i] & 1)) required.push_back(i);
            }
            if (cycle >= 0) {
                int component = roots[cycle];
                for (int i : required) if (roots[i] != component) return false;
                for (int i = 0; i < size; ++i) if (roots[i] != component) dom[i] = 1;
                return true;
            }
            for (auto [i, j, d] : edges) {
                if (!(forced_edges[i] & DIRS[d]) && (dom[i] & t.edge_mask[d])
                    && roots[i] == roots[j] && counts[roots[i]] < static_cast<int>(required.size())) {
                    if (!narrow(i, t.no_edge_mask[d])) return false;
                    if (!narrow(j, t.no_edge_mask[(d + 2) % 4])) return false;
                }
            }
            if (!queue.empty()) continue;

            // Required cells must remain connected through possible edges.
            if (!required.empty()) {
                vector<unsigned char> seen(size, false);
                vector<int> stack = {required[0]}; seen[required[0]] = true;
                while (!stack.empty()) {
                    int i = stack.back(); stack.pop_back();
                    int possible = t.possible[dom[i]];
                    for (int d = 0; d < 4; ++d) {
                        int j = nbr[i][d];
                        if ((possible & DIRS[d]) && !seen[j]) {
                            seen[j] = true; stack.push_back(j);
                        }
                    }
                }
                for (int i : required) if (!seen[i]) return false;
                for (int i = 0; i < size; ++i) {
                    if (!seen[i] && !narrow(i, 1)) return false;
                }
            }
            if (queue.empty()) return true;
        }
    }

    void check(const vector<int>& dom) {
        int used = 0, first = -1;
        for (int i = 0; i < size; ++i) {
            if (dom[i] != 1) { ++used; if (first < 0) first = i; }
        }
        if (!used || used >= best_len) return;
        for (auto [i, p] : pearls) { (void)p; if (dom[i] == 1) return; }
        vector<unsigned char> seen(size, false);
        int current = first, previous = -1, visited = 0;
        while (!seen[current]) {
            seen[current] = true; ++visited;
            int shape = SHAPES[t.single_state[dom[current]]];
            int next = -1;
            for (int d = 0; d < 4; ++d) {
                if ((shape & DIRS[d]) && nbr[current][d] != previous) { next = nbr[current][d]; break; }
            }
            if (next < 0) return;
            previous = current; current = next;
        }
        if (current == first && visited == used) save_solution(dom, used);
    }

    void dfs(vector<int> dom, int changed = -1) {
        check_timeout();
        if (!propagate(dom, changed)) return;
        int forced = 0;
        for (int v : dom) if (!(v & 1)) ++forced;
        if (forced >= best_len) return;
        int chosen = -1;
        tuple<int, int, int, int> best_key;
        for (int i = 0; i < size; ++i) {
            if (t.count[dom[i]] <= 1) continue;
            int adjacent_required = 0;
            for (int j : nbr[i]) if (j >= 0 && !(dom[j] & 1)) ++adjacent_required;
            auto key = make_tuple(strategy == 3 && (dom[i] & 1) ? 1 : 0,
                                  t.count[dom[i]], -adjacent_required, -pearl_neighbors[i]);
            if (chosen < 0 || key < best_key) { chosen = i; best_key = key; }
        }
        if (chosen < 0) { check(dom); return; }
        vector<int> options = t.states[dom[chosen]];
        auto option_key = [&](int a) {
            bool straight = a == 1 || a == 2;
            if (strategy == 0) return make_pair(a == 0, straight);
            if (strategy == 1) return make_pair(a != 0, !straight);
            return make_pair(a == 0, !straight);
        };
        stable_sort(options.begin(), options.end(), [&](int a, int b) { return option_key(a) < option_key(b); });
        for (int a : options) {
            vector<int> next = dom; next[chosen] = 1 << a;
            dfs(std::move(next), chosen);
        }
    }
};

}  // namespace

/*
 * Complete the 'solve' function below.
 * The function is expected to return a STRING_ARRAY.
 * The function accepts STRING_ARRAY grid as parameter.
 */
vector<string> solve(vector<string> grid) {
    return MasyuSolver(grid).run();
}

#ifndef MASYU_NO_MAIN
string ltrim(const string& str) {
    auto first = find_if_not(str.begin(), str.end(), [](unsigned char ch) { return isspace(ch); });
    return string(first, str.end());
}

string rtrim(const string& str) {
    auto last = find_if_not(str.rbegin(), str.rend(), [](unsigned char ch) { return isspace(ch); }).base();
    return string(str.begin(), last);
}

int main() {
    ofstream fout(getenv("OUTPUT_PATH"));
    string grid_count_temp;
    getline(cin, grid_count_temp);
    int grid_count = stoi(ltrim(rtrim(grid_count_temp)));
    vector<string> grid(grid_count);
    for (int i = 0; i < grid_count; ++i) getline(cin, grid[i]);
    vector<string> result = solve(grid);
    for (size_t i = 0; i < result.size(); ++i) {
        fout << result[i];
        if (i != result.size() - 1) fout << '\n';
    }
    fout << '\n';
    return 0;
}
#endif
