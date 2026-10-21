#!/bin/python3

import math
import os
import random
import re
import sys



#
# Complete the 'pack_squares' function below.
#
# The function is expected to return a 2D_INTEGER_ARRAY.
# The function accepts INTEGER_ARRAY squares as parameter.
#


from bisect import bisect_left
from dataclasses import dataclass
from functools import reduce
from math import exp, gcd, isfinite, isqrt
from operator import index as integer_index
from random import Random
from time import perf_counter
from typing import Iterable


@dataclass(frozen=True)
class Square:
    """A square's top-left corner: x increases downward, y to the right."""

    x: int
    y: int
    side: int


@dataclass(frozen=True)
class Packing:
    # Squares stay in the same order as the input side lengths.
    squares: tuple[Square, ...]
    width: int
    height: int

    @property
    def area(self) -> int:
        return self.width * self.height


# Free rectangles use (top, left, bottom, right) coordinates.
Rectangle = tuple[int, int, int, int]


def _split_free_space(
        free_rectangles: list[Rectangle], square: Square
) -> list[Rectangle]:
    """Remove a placed square from every free rectangle it intersects."""
    x, y, side = square.x, square.y, square.side
    bottom, right = x + side, y + side
    remaining = []

    for top, left, free_bottom, free_right in free_rectangles:
        if bottom <= top or x >= free_bottom or right <= left or y >= free_right:
            remaining.append((top, left, free_bottom, free_right))
            continue

        # The resulting free rectangles may overlap each other; that is allowed.
        if x > top:
            remaining.append((top, left, x, free_right))
        if bottom < free_bottom:
            remaining.append((bottom, left, free_bottom, free_right))
        if y > left:
            remaining.append((top, left, free_bottom, y))
        if right < free_right:
            remaining.append((top, right, free_bottom, free_right))

    # A containing rectangle must have at least as much area. Processing large
    # rectangles first avoids comparing against every smaller rectangle.
    remaining = sorted(
        set(remaining), key=lambda r: (r[2] - r[0]) * (r[3] - r[1]), reverse=True
    )
    maximal = []
    for rectangle in remaining:
        top, left, bottom, right = rectangle
        for a, b, c, d in maximal:
            if a <= top and b <= left and c >= bottom and d >= right:
                break
        else:
            maximal.append(rectangle)
    return maximal


def _pack_at_width(
        sides: tuple[int, ...],
        order: list[int],
        width: int,
        height: int,
        strategy: str = "short_side",
        deadline: float = float("inf"),
) -> Packing | None:
    free_rectangles = [(0, 0, height, width)]
    placed = {}
    used_width = used_height = 0

    for index in order:
        if perf_counter() >= deadline:
            return None
        side = sides[index]
        best = None
        for top, left, bottom, right in free_rectangles:
            if top + side <= bottom and left + side <= right:
                dx, dy = bottom - top - side, right - left - side
                if strategy == "bottom_left":
                    score = (top, left)
                elif strategy == "area":
                    score = ((bottom - top) * (right - left), min(dx, dy))
                elif strategy == "bounding_area":
                    score = (
                        max(used_height, top + side) * max(used_width, left + side),
                        top, left,
                    )
                else:
                    score = (min(dx, dy), max(dx, dy))
                candidate = (score, top, left)
                if best is None or candidate < best:
                    best = candidate

        if best is None:
            return None

        _, x, y = best
        square = Square(x, y, side)
        placed[index] = square
        used_height = max(used_height, x + side)
        used_width = max(used_width, y + side)
        if len(placed) < len(sides):
            free_rectangles = _split_free_space(free_rectangles, square)

    squares = tuple(placed[index] for index in range(len(sides)))
    return Packing(
        squares,
        used_width,
        used_height,
    )


def _search_integer_box(
        sides: tuple[int, ...], width: int, height: int, budget: list[int],
        deadline: float = float("inf"),
) -> Packing | None:
    """Search an integer box; budget limits visited states across all boxes.

    At the first empty cell, either start a square or leave one cell unused.
    Both choices are needed: forcing every square into a corner misses layouts.
    A skyline records occupied/wasted cells from the top of each column.
    """
    sizes = sorted(set(sides), reverse=True)
    initial_counts = tuple(sides.count(side) for side in sizes)
    failed = set()
    # A difficult impossible box must not consume the entire search budget.
    local_budget = [min(20_000, budget[0])]

    def visit(skyline, counts, remaining_area):
        if remaining_area == 0:
            return []
        if local_budget[0] <= 0 or budget[0] <= 0:
            return None
        if budget[0] % 64 == 0 and perf_counter() >= deadline:
            local_budget[0] = 0
            return None
        local_budget[0] -= 1
        budget[0] -= 1

        # Mirror-image states have the same feasibility.
        key = (min(skyline, skyline[::-1]), counts)
        if key in failed:
            return None
        x = min(skyline)
        y = skyline.index(x)
        if x >= height:
            return None

        for index, side in enumerate(sizes):
            if not counts[index] or x + side > height or y + side > width:
                continue
            if any(level != x for level in skyline[y:y + side]):
                continue
            next_skyline = skyline[:y] + (x + side,) * side + skyline[y + side:]
            next_counts = list(counts)
            next_counts[index] -= 1
            result = visit(next_skyline, tuple(next_counts), remaining_area - side**2)
            if result is not None:
                return [(side, x, y)] + result

        if width * height - sum(skyline) > remaining_area:
            next_skyline = skyline[:y] + (x + 1,) + skyline[y + 1:]
            result = visit(next_skyline, counts, remaining_area)
            if result is not None:
                return result
        failed.add(key)
        return None

    layout = visit((0,) * width, initial_counts, sum(side**2 for side in sides))
    if layout is None:
        return None
    positions = {side: [] for side in sizes}
    for side, x, y in layout:
        positions[side].append(Square(x, y, side))
    squares = tuple(positions[side].pop() for side in sides)
    return Packing(
        squares,
        max(square.y + square.side for square in squares),
        max(square.x + square.side for square in squares),
    )


def _pack_best_fit(
        sides: tuple[int, ...], width: int, height: int, strategy: int,
        deadline: float = float("inf"),
) -> Packing | None:
    """Choose both the next square and its free rectangle by fit quality.

    A fixed descending order can leave gaps that the smaller squares almost
    fill. Comparing all unplaced squares lets an exact fit take priority.
    """
    free_rectangles = [(0, 0, height, width)]
    remaining = list(range(len(sides)))
    squares = [None] * len(sides)
    while remaining:
        if perf_counter() >= deadline:
            return None
        best = None
        for top, left, bottom, right in free_rectangles:
            rectangle_height, rectangle_width = bottom - top, right - left
            for index in remaining:
                side = sides[index]
                if side > rectangle_height or side > rectangle_width:
                    continue
                dx, dy = rectangle_height - side, rectangle_width - side
                short, long = (dx, dy) if dx < dy else (dy, dx)
                if strategy == 0:
                    score = (short, long, -side)
                elif strategy == 1:
                    score = (rectangle_height * rectangle_width - side**2, short, -side)
                elif strategy == 2:
                    score = (top, left, -side)
                elif strategy == 3:
                    score = (short, -side, long)
                elif strategy == 4:
                    score = (short / side, long / side, -side)
                else:
                    score = (long, short, -side)
                candidate = (score, top, left, index)
                if best is None or candidate < best:
                    best = candidate

        if best is None:
            return None
        _, x, y, index = best
        square = Square(x, y, sides[index])
        squares[index] = square
        remaining.remove(index)
        if remaining:
            free_rectangles = _split_free_space(free_rectangles, square)

    return Packing(
        tuple(squares),
        max(square.y + square.side for square in squares),
        max(square.x + square.side for square in squares),
    )


def _refine_packing(
        sides: tuple[int, ...], initial: Packing, minimum_area: int,
        deadline: float = float("inf"),
) -> Packing:
    """Improve orders and box shapes with simulated annealing until expiry.

    Occasional uphill moves escape greedy local minima. Cache only costs to
    keep memory bounded; retain coordinates for the best complete layout.
    Finite deadlines allow additional restarts beyond the initial eight.
    """
    best = initial
    reference = initial.area
    total, largest = sum(sides), max(sides)
    root = isqrt(sum(side**2 for side in sides))
    # Include neighbouring integer widths around the preferred aspect ratios.
    start_width_min = max(largest, 3 * root // 4 - 1)
    start_width_max = max(start_width_min, root + 2)
    width_limit = max(start_width_max, isqrt(reference) + largest // 10)
    width_step = max(8, root // 20)
    order = tuple(sorted(range(len(sides)), key=lambda index: -sides[index]))
    strategies = ("bottom_left", "short_side", "area", "bounding_area")
    rng = Random(0)
    costs = {}
    best_state = None

    def evaluate(state):
        nonlocal best, best_state
        if state in costs:
            return costs[state]
        ordering, width, strategy, mode = state
        height = total if mode == 0 else (reference * (95 + 5 * mode) // 100) // width
        packing = _pack_at_width(
            sides, ordering, width, height, strategies[strategy], deadline
        )
        cost = None if packing is None else packing.area
        if len(costs) >= 25_000:
            costs.clear()
        costs[state] = cost
        if packing is not None and cost < best.area:
            best, best_state = packing, state
        return cost

    restart = 0
    while restart < 8 or isfinite(deadline):
        if perf_counter() >= deadline:
            return best
        if best_state is not None and restart % 3:
            ordering, width = list(best_state[0]), best_state[1]
        else:
            ordering = list(order)
            rng.shuffle(ordering)
            width = rng.randint(start_width_min, start_width_max)
        state = (tuple(ordering), width, rng.randrange(len(strategies)), 0)
        cost = evaluate(state)
        for step in range(3000):
            if best.area <= minimum_area or perf_counter() >= deadline:
                return best
            ordering, width, strategy, mode = state
            ordering = list(ordering)
            action = rng.randrange(10)
            if action < 6:
                i, j = rng.sample(range(len(sides)), 2)
                if action < 3:
                    ordering[i], ordering[j] = ordering[j], ordering[i]
                else:
                    ordering.insert(j, ordering.pop(i))
            elif action < 8:
                width = max(largest, min(width_limit, width + rng.randint(-width_step, width_step)))
            elif action == 8:
                strategy = rng.randrange(len(strategies))
            else:
                mode = rng.randrange(4)
            candidate = (tuple(ordering), width, strategy, mode)
            next_cost = evaluate(candidate)
            if next_cost is None:
                continue
            delta = next_cost - cost
            temperature = 0.025 * 0.02**(step / 3000)
            if delta <= 0 or rng.random() < exp(-(delta / reference) / temperature):
                state, cost = candidate, next_cost
        restart += 1
    return best


def _refine_sequence_pair(
        sides: tuple[int, ...], initial: Packing, minimum_area: int,
        deadline: float = float("inf"),
) -> Packing:
    """Search relative positions without committing to greedy free rectangles.

    Two permutations encode a valid packing: squares in the same order in
    both are separated horizontally; opposite orders separate them vertically.
    Longest paths give the smallest coordinates satisfying those separations.
    All distances are sums of integer side lengths, so coordinates stay integral.
    Continue new restarts until a finite deadline; without one, use 16 restarts.
    """
    count = len(sides)
    indices = list(range(count))
    rng = Random(0)
    best_cost = float("inf")
    best_state = None
    # Reduce work as inputs grow. This polynomial search complements the
    # backtracking and MaxRects refinement used for the smaller instances.
    steps = max(1000, min(20_000, 20_000 * 22**2 // count**2))

    def evaluate(first, second, coordinates=False):
        rank = [0] * count
        for position, index in enumerate(second):
            rank[index] = position

        # Each array stores prefix maxima of the longest-path distances.
        # Entries are monotone, so stop updating once a larger value is met.
        horizontal = [0] * (count + 1)
        vertical = [0] * (count + 1)
        positions = [None] * count if coordinates else None
        for index in first:
            position = rank[index]
            reverse = count - 1 - position
            y, x = horizontal[position], vertical[reverse]
            side = sides[index]
            if coordinates:
                positions[index] = Square(x, y, side)
            right, bottom = y + side, x + side
            j = position + 1
            while j <= count and horizontal[j] < right:
                horizontal[j] = right
                j += 1
            j = reverse + 1
            while j <= count and vertical[j] < bottom:
                vertical[j] = bottom
                j += 1

        if coordinates:
            return Packing(tuple(positions), horizontal[count], vertical[count])
        return horizontal[count] * vertical[count]

    restart = 0
    while restart < 16 or isfinite(deadline):
        if perf_counter() >= deadline:
            break
        if best_state is not None and restart % 3:
            first, second = map(list, best_state)
        else:
            first, second = indices.copy(), indices.copy()
            rng.shuffle(first)
            rng.shuffle(second)
        cost = evaluate(first, second)
        for step in range(steps):
            if step % 32 == 0 and perf_counter() >= deadline:
                break
            next_first, next_second = first.copy(), second.copy()
            i, j = rng.sample(indices, 2)
            action = rng.randrange(5)
            if action == 0:
                next_first[i], next_first[j] = next_first[j], next_first[i]
            elif action == 1:
                next_second[i], next_second[j] = next_second[j], next_second[i]
            elif action == 2:
                # Swap square identities in both permutations together.
                a, b = next_first.index(i), next_first.index(j)
                c, d = next_second.index(i), next_second.index(j)
                next_first[a], next_first[b] = next_first[b], next_first[a]
                next_second[c], next_second[d] = next_second[d], next_second[c]
            elif action == 3:
                next_first.insert(j, next_first.pop(i))
            else:
                next_second.insert(j, next_second.pop(i))

            next_cost = evaluate(next_first, next_second)
            temperature = 0.025 * 0.004**(step / steps)
            if next_cost <= cost or rng.random() < exp(
                    (cost - next_cost) / (cost * temperature)
            ):
                first, second, cost = next_first, next_second, next_cost
            if next_cost < best_cost:
                best_cost = next_cost
                best_state = (next_first, next_second)
                if best_cost <= minimum_area:
                    return evaluate(*best_state, coordinates=True)
        restart += 1

    if best_cost < initial.area:
        return evaluate(*best_state, coordinates=True)
    return initial


def pack_squares(
        side_lengths: Iterable[int], width_samples: int = 64, *, time_limit: float = 8.0
) -> list[tuple[int, int]]:
    """Return top-left (X, Y) corners in the same order as the side lengths.

    X increases downward and Y increases to the right. Every input side length
    must be a positive integer. Integer-valued floats are also accepted.
    Empty input returns an empty list. Output coordinates are always integers.
    Edges stay parallel to the axes. Squares may touch but cannot overlap.
    Increasing width_samples searches more trial widths. The search uses
    integer box dimensions and bounded backtracking for small instances.
    Up to 128 squares, bounded best-fit and local searches also improve layouts.
    time_limit is the search budget in seconds (default 8.0). Increase it for
    better packing when the judge allows more time. Zero returns a simple row.
    The budget is checked within searches; validation and final output take
    additional time. The best complete, valid layout is retained on expiry.
    Refinement keeps restarting while time remains, unless a lower bound is met.

    The result is approximate: minimum-area square packing is NP-hard.
    """
    started = perf_counter()
    if isinstance(time_limit, bool) or not isinstance(time_limit, (int, float)):
        raise ValueError("time_limit must be a finite nonnegative number")
    if not isfinite(time_limit) or time_limit < 0:
        raise ValueError("time_limit must be a finite nonnegative number")
    deadline = started + time_limit
    if isinstance(width_samples, bool) or not isinstance(width_samples, int):
        raise ValueError("width_samples must be an integer of at least 2")
    if width_samples < 2:
        raise ValueError("width_samples must be an integer of at least 2")

    values = []
    for side in side_lengths:
        try:
            value = integer_index(side)
        except TypeError:
            number = float(side)
            if not isfinite(number) or not number.is_integer():
                raise ValueError("Every side length must be a positive integer")
            value = int(number)
        if value <= 0:
            raise ValueError("Every side length must be a positive integer")
        values.append(value)
    sides = tuple(values)
    if not sides:
        return []

    # A common integer scale reduces the backtracking grid without changing
    # attainable layouts or their score. Restore this scale in the output.
    scale = reduce(gcd, sides)
    sides = tuple(side // scale for side in sides)

    total = sum(sides)
    largest = max(sides)
    lower_bound = sum(side * side for side in sides)

    # A single row supplies a feasible baseline and an upper bound on area.
    row = []
    y = 0
    for side in sides:
        row.append(Square(0, y, side))
        y += side
    best = Packing(tuple(row), total, largest)
    if perf_counter() >= deadline:
        return [(square.x * scale, square.y * scale) for square in best.squares]
    order = sorted(range(len(sides)), key=lambda index: sides[index], reverse=True)
    descending = [sides[index] for index in order]

    # If every pair in a group has side_i + side_j > width, their horizontal
    # projections intersect, so they must stack vertically. The heaviest such
    # group is a prefix of the descending side lengths.
    prefix_lengths = [0]
    for side in descending:
        prefix_lengths.append(prefix_lengths[-1] + side)
    negative_pair_sums = [-(a + b) for a, b in zip(descending, descending[1:])]

    def height_bound(width):
        count = bisect_left(negative_pair_sums, -width) + 1
        area_height = (lower_bound + width - 1) // width
        return max(largest, area_height, prefix_lengths[count])

    # An optimal rectangle can be rotated so its width <= sqrt(baseline area).
    max_width = isqrt(best.area)
    widths = {
        largest + (max_width - largest) * i // (width_samples - 1)
        for i in range(width_samples)
    }
    widths.update((largest, isqrt(lower_bound), max_width))

    # Compaction gives an integer-coordinate optimum for integer squares.
    # Enumerate all widths when affordable; otherwise retain sampled widths.
    if max_width - largest <= max(256, width_samples * 4):
        integer_widths = list(range(largest, max_width + 1))
        widths.update(integer_widths)
        lower_bound_area = min(
            width * max(width, height_bound(width)) for width in integer_widths
        )
    else:
        lower_bound_area = lower_bound

    # Prefix sums include widths at which the largest squares fit side by side.
    prefix = 0
    for index in order:
        prefix += sides[index]
        if prefix > max_width:
            break
        widths.add(prefix)

    def consider(candidate):
        nonlocal best
        if candidate is None:
            return
        if (candidate.area, candidate.width + candidate.height) < (
                best.area, best.width + best.height
        ):
            best = candidate

    strategies = ("bottom_left", "short_side", "bounding_area", "area")
    ranked_widths = sorted(widths, key=lambda width: (width * height_bound(width), width))
    # Keep the initial sweep short so larger budgets primarily fund refinement.
    greedy_deadline = min(deadline, started + min(time_limit * 0.25, 0.75))
    width_costs = {}
    for width in ranked_widths:
        if best.area <= lower_bound_area or perf_counter() >= greedy_deadline:
            break
        if width * height_bound(width) >= best.area:
            continue
        for strategy in strategies:
            candidate = _pack_at_width(sides, order, width, total, strategy, greedy_deadline)
            if candidate is not None:
                width_costs[width] = min(width_costs.get(width, candidate.area), candidate.area)
            consider(candidate)

    # Different insertion orders avoid committing to one greedy arrangement.
    # Keep this stage focused on promising widths, rather than every sample.
    rng = Random(0)
    orders = [list(range(len(sides))), order[::-1]]
    for _ in range(4):
        orders.append(sorted(order, key=lambda index: -sides[index] * rng.randint(60, 140)))
    for alternative in orders:
        if best.area <= lower_bound_area or perf_counter() >= greedy_deadline:
            break
        for width in ranked_widths[:12]:
            if width * height_bound(width) >= best.area:
                continue
            for strategy in strategies:
                consider(_pack_at_width(
                    sides, alternative, width, total, strategy, greedy_deadline
                ))

    # With ten to twelve squares, exploring relative positions is cheap and
    # can improve a layout before fixed-box searches spend time on infeasible
    # targets. Reserve the final part of the budget for MaxRects refinement.
    # Smaller instances retain their early exact search for perfect packings.
    if 10 <= len(sides) <= 12 and best.area > lower_bound_area:
        sequence_deadline = min(deadline, started + time_limit * 0.7)
        best = _refine_sequence_pair(sides, best, lower_bound_area, sequence_deadline)

    # Backtracking tries smaller boxes in increasing area order. Large squares
    # need not make this search difficult: recursion places one whole square
    # or skips one empty cell. Bound skyline width and wasted cells instead of
    # total square area, so larger perfect/near-perfect packings are considered.
    max_search_width = 256
    max_wasted_cells = 256
    if len(sides) <= 12 and largest <= max_search_width and best.area > lower_bound_area:
        exact_deadline = min(deadline, started + time_limit * 0.4)
        boxes = []
        area_limit = min(best.area - 1, lower_bound + max_wasted_cells)
        for width in range(largest, min(max_search_width, isqrt(area_limit)) + 1):
            if perf_counter() >= exact_deadline:
                break
            for height in range(
                    max(width, height_bound(width)), area_limit // width + 1
            ):
                if height_bound(height) <= width:
                    boxes.append((width * height, width, height))
        budget = [100_000]
        for area, width, height in sorted(boxes):
            if area >= best.area or budget[0] <= 0 or perf_counter() >= exact_deadline:
                break
            consider(_search_integer_box(sides, width, height, budget, exact_deadline))

    # A fixed height changes which free rectangles are the tightest fits.
    # Trying actual target boxes can succeed where a tall strip and limited
    # backtracking both fail. Keep the extra search deterministic and bounded.
    fit_deadline = min(deadline, started + min(time_limit * 0.65, 2.0))
    if len(sides) <= 12 and best.area > lower_bound_area and perf_counter() < fit_deadline:
        target_boxes = []
        for width in ranked_widths:
            if perf_counter() >= fit_deadline:
                break
            if width * width >= best.area:
                continue
            min_height = max(width, height_bound(width))
            max_height = (best.area - 1) // width
            if min_height > max_height:
                continue
            # Sampling prevents huge side lengths from creating huge ranges.
            height_step = max(1, (max_height - min_height + 64) // 64)
            heights = set(range(min_height, max_height + 1, height_step))
            heights.add(max_height)
            for height in heights:
                if height_bound(height) <= width:
                    target_boxes.append((width * height, width, height))

        tight_rng = Random(0)
        trial_orders = [order, list(range(len(sides))), order[::-1]]
        for _ in range(32):
            trial_orders.append(sorted(
                order, key=lambda index: -sides[index] * tight_rng.randint(40, 160)
            ))
        # Equal-size squares are interchangeable during the search.
        unique_orders = {}
        for trial_order in trial_orders:
            unique_orders.setdefault(tuple(sides[index] for index in trial_order), trial_order)

        attempts_left = 30_000
        for area, width, height in sorted(target_boxes):
            if (area >= best.area or attempts_left <= 0 or best.area <= lower_bound_area
                    or perf_counter() >= fit_deadline):
                break
            for trial_order in unique_orders.values():
                if area >= best.area or attempts_left <= 0 or perf_counter() >= fit_deadline:
                    break
                for box_width, box_height in ((width, height), (height, width)):
                    for strategy in strategies:
                        if attempts_left <= 0 or area >= best.area or perf_counter() >= fit_deadline:
                            break
                        attempts_left -= 1
                        consider(_pack_at_width(
                            sides, trial_order, box_width, box_height, strategy, fit_deadline
                        ))

    # Try improving boxes near the successful greedy widths first. Starting
    # from the theoretical minimum spends most of a short budget on boxes
    # that cannot accommodate the squares, before reaching useful dimensions.
    if (12 < len(sides) <= 128 and best.area > lower_bound_area
            and perf_counter() < fit_deadline):
        preferred = min(best.width, best.height)
        near_widths = [preferred]
        for offset in range(1, 5):
            near_widths.extend((preferred - offset, preferred + offset))
        promising = sorted(width_costs, key=lambda width: (width_costs[width], width))
        fit_widths = list(dict.fromkeys(near_widths + promising + ranked_widths))
        tried = set()
        for width in fit_widths:
            if best.area <= lower_bound_area or perf_counter() >= fit_deadline:
                break
            if width < largest:
                continue
            height = (best.area - 1) // width
            if height < height_bound(width) or height_bound(height) > width:
                continue
            for box_width, box_height in ((width, height), (height, width)):
                if (box_width, box_height) in tried:
                    continue
                tried.add((box_width, box_height))
                for strategy in range(6):
                    if perf_counter() >= fit_deadline:
                        break
                    consider(_pack_best_fit(
                        sides, box_width, box_height, strategy, fit_deadline
                    ))

        # With a larger time allowance, also explore boxes near the lower
        # bound. Keep both the call limit and the shared wall-clock deadline.
        target_boxes = []
        for width in ranked_widths:
            if perf_counter() >= fit_deadline:
                break
            if width * width >= best.area:
                continue
            min_height = max(width, height_bound(width))
            max_height = (best.area - 1) // width
            if min_height > max_height:
                continue
            height_step = max(1, (max_height - min_height + 64) // 64)
            heights = set(range(min_height, max_height + 1, height_step))
            heights.add(max_height)
            for height in heights:
                if height_bound(height) <= width:
                    target_boxes.append((width * height, width, height))

        attempts_left = max(64, min(6000, 6000 * 34**3 // len(sides)**3))
        for area, width, height in sorted(target_boxes):
            if (area >= best.area or attempts_left <= 0 or best.area <= lower_bound_area
                    or perf_counter() >= fit_deadline):
                break
            for box_width, box_height in ((width, height), (height, width)):
                for strategy in range(6):
                    if (attempts_left <= 0 or area >= best.area
                            or perf_counter() >= fit_deadline):
                        break
                    attempts_left -= 1
                    consider(_pack_best_fit(
                        sides, box_width, box_height, strategy, fit_deadline
                    ))

    if 2 <= len(sides) <= 12 and best.area > lower_bound_area:
        best = _refine_packing(sides, best, lower_bound_area, deadline)
    elif 12 < len(sides) <= 128 and best.area > lower_bound_area:
        best = _refine_sequence_pair(sides, best, lower_bound_area, deadline)

    return [(int(square.x * scale), int(square.y * scale)) for square in best.squares]


if __name__ == '__main__':
    fptr = open(os.environ['OUTPUT_PATH'], 'w')

    squares_count = int(input().strip())

    squares = []

    for _ in range(squares_count):
        squares_item = int(input().strip())
        squares.append(squares_item)

    result = pack_squares(squares)

    fptr.write('\n'.join([' '.join(map(str, x)) for x in result]))
    fptr.write('\n')

    fptr.close()
