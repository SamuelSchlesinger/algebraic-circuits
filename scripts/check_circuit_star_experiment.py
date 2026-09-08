#!/usr/bin/env python3
"""Independent small-state checks for the circuit-star SAT experiment.

Run from the repository root. This first enumerates shared semantic DAG states
on two inputs without using the SAT encoding, then checks the complete saved
three-input experiment with a second solver and verifies its provenance.
"""

from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from pysat.solvers import Solver

from circuit_star_experiment import Encoding, check, input_tables


def semantic_minima(width: int) -> list[int]:
    """BFS on sets of available truth tables; every prior value remains reusable."""
    full = (1 << (1 << width)) - 1
    initial = frozenset(input_tables(width))
    frontier, seen = {initial}, {initial}
    costs = {value: 0 for value in initial}
    size = 0
    while len(costs) < full + 1:
        size += 1
        following = set()
        for state in frontier:
            results = {0, full} | {value ^ full for value in state}
            for left, right in combinations(state, 2):
                results.add(left & right)
                results.add(left | right)
            # Identity and duplicate-valued gates do not change available semantics.
            for value in results - state:
                costs.setdefault(value, size)
                extended = state | {value}
                if extended not in seen:
                    seen.add(extended)
                    following.add(extended)
        frontier = following
        if not frontier and len(costs) < full + 1:
            raise AssertionError("Semantic enumeration exhausted before reaching every function")
    return [costs[value] for value in range(full + 1)]


def check_two_inputs() -> None:
    costs = semantic_minima(2)
    assert costs == [1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 0, 2, 0, 2, 1, 1], costs
    for size in range(1, max(costs) + 1):
        encoding = Encoding(2, size)
        with Solver(name="glucose4", bootstrap_with=encoding.clauses) as solver:
            for target, cost in enumerate(costs):
                assert solver.solve(assumptions=encoding.assumptions(target)) == (cost <= size), (size, target)
    print("All two-input SAT queries agree with independent shared-state enumeration.", flush=True)


def check_provenance(path: Path) -> None:
    result = json.loads(path.read_text())
    assert result["schema"] == 1
    assert result["script_sha256"] == sha256(Path("scripts/circuit_star_experiment.py").read_bytes()).hexdigest()
    assert len(result["witnesses"]) == len(result["costs"])
    for search in result["searches"]:
        size = search["size"]
        encoding = Encoding(result["width"], size)
        assert search["cnf_sha256"] == sha256(json.dumps(encoding.clauses).encode()).hexdigest()
        assert search["variables"] == encoding.pool.top
        assert search["clauses"] == len(encoding.clauses)
        assert search["sat"] == [f for f, cost in enumerate(result["costs"]) if cost == size]
        assert search["unsat"] == [f for f, cost in enumerate(result["costs"]) if cost > size]
    histogram = {str(size): result["costs"].count(size) for size in sorted(set(result["costs"]))}
    assert result["cost_histogram"] == histogram
    print("Saved source hash, CNF hashes, search outcomes, and histogram agree.", flush=True)


def check_faces(path: Path) -> None:
    result = json.loads(path.read_text())
    count = len(result["costs"])
    full = count - 1
    for link in result["links"]:
        for support in range(count):
            direct_birth = max(result["costs"][subset ^ (full if link["center"] else 0)]
                               for subset in range(count) if subset & support == subset)
            assert link["births"][support] == direct_birth
        for level in link["levels"]:
            faces = {s for s in range(count) if link["births"][s] <= level["budget"]}
            minimal = {s for s in range(count) if s not in faces and
                       all(t in faces for t in range(count) if t != s and t & s == t)}
            assert minimal == set(level["minimal_missing"])
            dual = {s for s in range(count) if full ^ s not in faces}
            facets = {s for s in dual if not any(t != s and t & s == s for t in dual)}
            assert facets == set(level["dual_facets"])
    print("Direct subset maxima, all proper nonface tests, and independent dual facets agree.", flush=True)


if __name__ == "__main__":
    check_two_inputs()
    path = Path("research/circuit-stars/n3.json")
    check_provenance(path)
    check_faces(path)
    check(path, "glucose4")
