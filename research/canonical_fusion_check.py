#!/usr/bin/env python3
"""Exact finite checks for the canonical graph-fusion cover argument.

No external packages or solver are used. The checks concern canonical
semi-filters, not unrestricted circuit complexity. Run from the repo root:
    python3 research/canonical_fusion_check.py
"""

from itertools import product
import json


def instance(n, graph):
    outside = [e for e in product(range(n), repeat=2)
               if not (graph >> (e[0] * n + e[1])) & 1]
    rows = [sum(1 << i for i, e in enumerate(outside) if e[0] == u)
            for u in range(n)]
    columns = [sum(1 << i for i, e in enumerate(outside) if e[1] == v)
               for v in range(n)]
    edges = [(u, v) for u, v in product(range(n), repeat=2)
             if (graph >> (u * n + v)) & 1 and rows[u] and columns[v]]
    pairs = [(sum(rows[u] for u in range(n) if (r >> u) & 1),
              sum(columns[v] for v in range(n) if (c >> v) & 1))
             for r, c in product(range(1 << n), repeat=2)]
    return outside, rows, columns, edges, pairs


def subset(a, b):
    return a & b == a


def accepts(generators, a):
    return any(subset(g, a) for g in generators)


def fails(generators, pair):
    a, b = pair
    return (accepts(generators, a) and accepts(generators, b)
            and not accepts(generators, a & b))


def saturate(generators, pairs):
    """Least upward family containing generators and preserving all pairs."""
    generators = set(generators)
    while True:
        added = {a & b for a, b in pairs
                 if accepts(generators, a) and accepts(generators, b)}
        enlarged = generators | added
        minimal = {g for g in enlarged
                   if not any(h != g and subset(h, g) for h in enlarged)}
        if minimal == generators:
            return minimal
        generators = minimal


def greedy_cover(rows, columns, edges, pairs):
    uncovered = set(edges)
    chosen = []
    while uncovered:
        pair = max(pairs, key=lambda p: sum(
            fails((rows[u], columns[v]), p) for u, v in uncovered))
        removed = {e for e in uncovered
                   if fails((rows[e[0]], columns[e[1]]), pair)}
        assert removed
        chosen.append(pair)
        uncovered -= removed
    return chosen


def main():
    checked_graphs = checked_edges = 0
    minimum = None
    richer_witness = None
    max_greedy = {}
    for n in range(1, 4):
        maximum = 0
        for graph in range(1 << (n * n)):
            checked_graphs += 1
            outside, rows, columns, edges, pairs = instance(n, graph)
            for u, v in edges:
                checked_edges += 1
                good = sum(fails((rows[u], columns[v]), p) for p in pairs)
                assert 16 * good >= len(pairs)
                if minimum is None or good * minimum[1] < minimum[0] * len(pairs):
                    minimum = (good, len(pairs), n, graph, [u, v])
                # Independently check all colorings satisfying the four-bit event.
                u2 = next(x for x in range(n) if (x, v) in outside)
                v2 = next(y for y in range(n) if (u, y) in outside)
                forced = 0
                for index, (r, c) in enumerate(product(range(1 << n), repeat=2)):
                    event = ((r >> u) & 1 and not (r >> u2) & 1
                             and (c >> v) & 1 and not (c >> v2) & 1)
                    if event:
                        forced += 1
                        assert fails((rows[u], columns[v]), pairs[index])
                assert 16 * forced == len(pairs)
            cover = greedy_cover(rows, columns, edges, pairs)
            maximum = max(maximum, len(cover))
            for u, v in edges:
                assert any(fails((rows[u], columns[v]), p) for p in cover)
                closure = saturate((rows[u], columns[v]), cover)
                if 0 not in closure and richer_witness is None:
                    # Check every subset, so this certificate does not rely on
                    # the implementation of saturation to check preservation.
                    accepted = [a for a in range(1 << len(outside))
                                if accepts(closure, a)]
                    assert accepted and 0 not in accepted
                    assert all(b in accepted for a in accepted
                               for b in range(1 << len(outside)) if subset(a, b))
                    assert rows[u] in accepted and columns[v] in accepted
                    assert all(not fails(closure, p) for p in cover)
                    richer_witness = dict(n=n, graph_mask=graph, outside=outside,
                        edge=[u, v], pairs=cover, generators=sorted(closure))
        max_greedy[n] = maximum
    assert 4 * 15 ** 32 < 16 ** 32
    print(json.dumps(dict(checked_graphs=checked_graphs,
        checked_canonical_edges=checked_edges,
        minimum_failure_fraction=minimum,
        max_greedy_cover_size=max_greedy,
        surviving_noncanonical_filter=richer_witness), indent=2))


if __name__ == "__main__":
    main()
