#!/usr/bin/env python3
"""Recompute the arithmetic and finite integer tables in the small-order proof.

Python 3.11+; standard library only. This checks integer statements, not
Gallai's theorems, the planarity bounds, or completeness of graph reductions.
The separate computations/ programs reproduce the finite graph checks.
"""
from __future__ import annotations

import argparse
import itertools
import json
from math import comb
from pathlib import Path
from typing import Iterator


def require(condition: bool, message: str) -> None:
    """Do not use assertions that disappear under python -O."""
    if not condition:
        raise RuntimeError(message)


def gallai(k: int, n: int) -> int:
    if not (k + 2 <= n <= 2 * k - 1):
        raise ValueError(f"Gallai range violated: k={k}, n={n}")
    return comb(n, 2) - (n - k) ** 2 - 1


def budget(n: int) -> int:
    if n < 3:
        raise ValueError("The 6n-12 edge bound is used only for n >= 3")
    return 6 * n - 12


def triple_bound(n: int, t: int) -> int:
    s = n - 3 - t
    if s < 0:
        raise ValueError("A critical subgraph cannot have more vertices than G-I")
    return 27 + gallai(9, t) + 6 * s - comb(s, 2)


def factor_orders(total: int, length: int, lower: int = 1) -> Iterator[tuple[int, ...]]:
    """Sorted partitions into singletons and odd integers at least five."""
    if length == 0:
        if total == 0:
            yield ()
        return
    for n in range(lower, total // length + 1):
        if n != 1 and not (n >= 5 and n % 2 == 1):
            continue
        for tail in factor_orders(total - n, length - 1, n):
            yield (n,) + tail


def complement_bound(parts: tuple[int, ...]) -> int:
    """Maximize sum floor(n_i*w_i/2), with singleton contribution zero."""
    choices = [(1,) if n == 1 else tuple(range(2, (n - 1) // 2 + 1)) for n in parts]
    values = [
        sum(0 if n == 1 else n * w // 2 for n, w in zip(parts, weights))
        for weights in itertools.product(*choices)
        if sum(weights) <= 8
    ]
    if not values:
        raise ValueError(f"No feasible clique bounds for {parts}")
    return max(values)


def q15_patterns() -> list[dict]:
    """Necessary critical join-factor data for chi=9, order=15.

    Nontrivial complement components satisfy n_i >= 2q_i-1 and q_i>=3.
    A 3-critical component is an odd cycle. Other internal edge bounds use
    Gallai where applicable, and the minimum-degree bound elsewhere.
    The single indecomposable factor is excluded by Gallai decomposition.
    """
    items: list[tuple[int, int, int]] = [(1, 1, 0)]
    for q in range(3, 10):
        for n in range(2 * q - 1, 16):
            if q == 3:
                if n % 2 == 0:
                    continue
                edges = n
            elif q + 2 <= n <= 2 * q - 1:
                edges = gallai(q, n)
            else:
                edges = ((q - 1) * n + 1) // 2
            items.append((n, q, edges))
    items.sort()
    rows: list[dict] = []

    def visit(start: int, ns: int, qs: int, chosen: tuple[tuple[int, int, int], ...]) -> None:
        if ns == 15 and qs == 9:
            if len(chosen) < 2:
                return
            cross = (15**2 - sum(n**2 for n, _, _ in chosen)) // 2
            raw = cross + sum(e for _, _, e in chosen)
            # At 30 edges the 12-vertex, 6-critical factor would be
            # 5-regular, contrary to Brooks. Only this row needs correction.
            brooks = any(n == 12 and q == 6 and e == 30 for n, q, e in chosen)
            rows.append({
                "factors": [list(item) for item in chosen],
                "component_orders": [n for n, _, _ in chosen],
                "raw_edge_bound": raw,
                "brooks_corrected_bound": raw + int(brooks),
            })
            return
        for i in range(start, len(items)):
            n, q, _ = items[i]
            if ns + n <= 15 and qs + q <= 9:
                visit(i, ns + n, qs + q, chosen + (items[i],))

    visit(0, 0, 0, ())
    return rows


def explicit_dense17_obstruction() -> dict:
    sizes = (4, 4, 3, 3, 3)
    part = [i for i, size in enumerate(sizes) for _ in range(size)]
    all_pairs = set(itertools.combinations(range(17), 2))
    f_edges = {(u, v) for u, v in all_pairs if (part[u] - part[v]) % 5 in (1, 4)}
    h_edges = all_pairs - f_edges
    cone = h_edges | {(v, 17) for v in range(17)}
    obstruction = {
        (u, v) for u, v in h_edges if part[u] != part[v]
    } | {(v, 17) for v in range(17) if part[v] in (0, 1)}
    require(obstruction <= cone, "Obstruction not contained in cone complement")
    require(len(f_edges) == 58, "Wrong 17-vertex complement size")
    require(len(obstruction) == 65, "Wrong triangle-free obstruction size")
    for u, v, w in itertools.combinations(range(18), 3):
        require(not {(u, v), (u, w), (v, w)} <= obstruction, "Obstruction contains a triangle")
    require(len(obstruction) > 4 * 18 - 8, "No density contradiction")
    return {
        "complement_cycle_sizes": list(sizes),
        "complement_edges": len(f_edges),
        "cone_edges": len(cone),
        "obstruction_edge_count": len(obstruction),
        "triangle_free_biplanar_budget": 4 * 18 - 8,
        "obstruction_edges": [list(e) for e in sorted(obstruction)],
    }


def check() -> dict:
    small = [{"n": n, "critical_lower": gallai(10, n), "biplanar_upper": budget(n)}
             for n in range(12, 16)]
    require([r["critical_lower"] for r in small] == [61, 68, 74, 79], "Small-order table changed")
    require(all(r["critical_lower"] > r["biplanar_upper"] for r in small), "Small-order gap failed")

    expected_triples = {
        16: [88, 89, 88],
        17: [92, 94, 94, 92],
        18: [95, 98, 99, 98, 95],
        19: [97, 101, 103, 103, 101, 97],
    }
    triples = []
    for n, expected in expected_triples.items():
        ts = list(range(11, n - 2))
        values = [triple_bound(n, t) for t in ts]
        require(values == expected, f"Independent-triple table mismatch at {n}")
        triples.append({"n": n, "t": ts, "bounds": values, "minimum": min(values)})
    require([t for t in range(11, 16) if triple_bound(18, t) <= 96] == [11, 15],
            "Order-18 branch reduction failed")

    expected_parts = {
        16: {(1, 1, 1, 13): 32, (1, 1, 5, 9): 23, (1, 1, 7, 7): 20, (1, 5, 5, 5): 15},
        17: {(1, 1, 15): 45, (1, 5, 11): 32, (1, 7, 9): 28, (5, 5, 7): 20},
    }
    complement_rows = []
    for n, expected in expected_parts.items():
        observed = {p: complement_bound(p) for p in factor_orders(n, 20 - n)}
        require(observed == expected, f"Complement table mismatch at order {n}")
        require(comb(n, 2) - max(observed.values()) > budget(n), f"No alpha-two contradiction at {n}")
        complement_rows.extend({"n": n, "parts": list(p), "complement_upper": e}
                               for p, e in observed.items())
    parts18 = list(factor_orders(18, 2))
    require(parts18 == [(1, 17), (5, 13), (7, 11), (9, 9)], "Order-18 factor list changed")
    require(all(a * b > 64 for a, b in parts18 if a != 1), "Bipartite join screen failed")

    q15 = q15_patterns()
    require(len(q15) == 10, "Expected ten order-15 factor patterns")
    require([r["raw_edge_bound"] for r in q15] == [78, 75, 72, 86, 69, 84, 68, 83, 85, 90],
            "Order-15 factor edge table mismatch")
    require([r["component_orders"] for r in q15 if r["brooks_corrected_bound"] <= 69] == [[1, 1, 13]],
            "Order-15 reduction did not leave exactly K2 join R")

    proper7 = {t: gallai(7, t) + 6 * (13 - t) - comb(13 - t, 2) for t in range(9, 13)}
    require(list(proper7.values()) == [49, 50, 49, 46], "Proper critical-subgraph table mismatch")
    independent13 = {t: 18 + gallai(6, t) + 3 * (10 - t) - comb(10 - t, 2) for t in (8, 9, 10)}
    require(list(independent13.values()) == [46, 47, 46], "Order-13 triple table mismatch")

    slack = [list(s) for s in itertools.product(range(2), repeat=4) if sum(s) <= 1]
    require(len(slack) == 5, "Expected exactly five one-unit-slack patterns")
    return {
        "status": "passed",
        "small_orders": small,
        "independent_triple_bounds": triples,
        "complement_component_bounds": complement_rows,
        "order18_factor_orders": [list(p) for p in parts18],
        "Q15_factor_bounds": q15,
        "proper_critical7_bounds": proper7,
        "critical6_after_triple_bounds": independent13,
        "one_unit_slack_patterns": slack,
        "dense17_obstruction": explicit_dense17_obstruction(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, metavar="PATH", help="also write the complete checked tables to PATH")
    args = parser.parse_args()
    result = check()
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS: critical-edge tables; independent-triple tables; complement partitions;")
    print("      clique allocations; order-15 join patterns; one-unit slack;")
    print("      explicit 65-edge triangle-free obstruction.")


if __name__ == "__main__":
    main()
