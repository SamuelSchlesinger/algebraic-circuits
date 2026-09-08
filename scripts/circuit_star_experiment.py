#!/usr/bin/env python3
"""Exact native-circuit searches and finite circuit-star geometry.

Requires python-sat. SAT minima are experimental evidence, not Lean proofs.
The encoding includes constants, identity, arbitrary sharing and free outputs.
"""

from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from math import comb
from pathlib import Path
import platform
import time

import pysat
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def input_tables(width: int) -> list[int]:
    return [sum(((row >> i) & 1) << row for row in range(1 << width)) for i in range(width)]


def evaluate(width: int, circuit: list[list], output: int | None = None) -> int:
    """Evaluate stored circuits directly as bitwise truth tables."""
    full = (1 << (1 << width)) - 1
    wires = input_tables(width)
    for gate in circuit:
        op, *args = gate
        if any(not isinstance(i, int) or not 0 <= i < len(wires) for i in args):
            raise ValueError(f"Invalid backward wire references: {gate}")
        if op == "false" and not args:
            value = 0
        elif op == "true" and not args:
            value = full
        elif op == "id" and len(args) == 1:
            value = wires[args[0]]
        elif op == "not" and len(args) == 1:
            value = wires[args[0]] ^ full
        elif op == "and" and len(args) == 2:
            value = wires[args[0]] & wires[args[1]]
        elif op == "or" and len(args) == 2:
            value = wires[args[0]] | wires[args[1]]
        else:
            raise ValueError(f"Invalid native gate: {gate}")
        wires.append(value)
    selected = len(wires) - 1 if output is None else output
    if not 0 <= selected < len(wires):
        raise ValueError("Invalid output wire")
    return wires[selected]


class Encoding:
    """Choose one instruction per gate and enforce every truth-table row."""

    def __init__(self, width: int, size: int):
        assert width > 0 and size > 0
        self.width, self.size = width, size
        self.pool = IDPool()
        self.clauses: list[list[int]] = []
        rows = 1 << width
        self.values = [[self.pool.id(("value", w, x)) for x in range(rows)]
                       for w in range(width + size)]
        self.instructions: list[list[tuple[int, list]]] = []
        for w in range(width):
            for x in range(rows):
                self.clauses.append([self.values[w][x] * (1 if x >> w & 1 else -1)])
        for g in range(size):
            available = width + g
            operations = [["false"], ["true"]]
            operations += [[op, a] for op in ("id", "not") for a in range(available)]
            # Equal binary arguments are represented by an identity instruction.
            operations += [[op, a, b] for op in ("and", "or")
                           for a, b in combinations(range(available), 2)]
            choices = [(self.pool.id(("choice", g, j)), gate) for j, gate in enumerate(operations)]
            self.instructions.append(choices)
            self.clauses.extend(CardEnc.equals([c for c, _ in choices], 1,
                                              vpool=self.pool, encoding=EncType.seqcounter).clauses)
            for c, gate in choices:
                for x in range(rows):
                    z = self.values[available][x]
                    op, *args = gate
                    a = self.values[args[0]][x] if args else None
                    b = self.values[args[1]][x] if len(args) == 2 else None
                    if op == "false":
                        equations = [[-z]]
                    elif op == "true":
                        equations = [[z]]
                    elif op == "id":
                        equations = [[-z, a], [z, -a]]
                    elif op == "not":
                        equations = [[-z, -a], [z, a]]
                    elif op == "and":
                        equations = [[-z, a], [-z, b], [z, -a, -b]]
                    else:
                        equations = [[z, -a], [z, -b], [-z, a, b]]
                    self.clauses.extend([[-c] + eq for eq in equations])

    def assumptions(self, target: int) -> list[int]:
        return [v if target >> x & 1 else -v for x, v in enumerate(self.values[-1])]

    def witness(self, model: list[int]) -> list[list]:
        positive = {literal for literal in model if literal > 0}
        result = []
        for choices in self.instructions:
            chosen = [gate for variable, gate in choices if variable in positive]
            if len(chosen) != 1:
                raise ValueError("Model did not select exactly one gate")
            result.append(chosen[0])
        return result


def rank_f2(columns: list[int]) -> int:
    pivots: dict[int, int] = {}
    for column in columns:
        while column:
            pivot = column.bit_length() - 1
            if pivot in pivots:
                column ^= pivots[pivot]
            else:
                pivots[pivot] = column
                break
    return len(pivots)


def reduced_betti(faces: set[int], vertices: int) -> dict[int, int]:
    """Augmented simplicial chains over F2; degree -1 records the empty face."""
    by_size = [[s for s in sorted(faces) if s.bit_count() == k] for k in range(vertices + 1)]
    ranks = [0] * (vertices + 2)
    for k in range(1, vertices + 1):
        lower = {s: i for i, s in enumerate(by_size[k - 1])}
        columns = []
        for s in by_size[k]:
            column = 0
            for i in range(vertices):
                if s >> i & 1:
                    column ^= 1 << lower[s ^ (1 << i)]
            columns.append(column)
        ranks[k] = rank_f2(columns)
    return {k - 1: len(by_size[k]) - ranks[k] - ranks[k + 1]
            for k in range(vertices + 1)}


def geometry(width: int, costs: list[int]) -> dict:
    vertices, count = 1 << width, len(costs)
    full = count - 1
    first = []
    links = []
    for center in (0, 1):
        births = [costs[s ^ (full if center else 0)] for s in range(count)]
        for i in range(vertices):
            for s in range(count):
                if s >> i & 1:
                    births[s] = max(births[s], births[s ^ (1 << i)])
        levels = []
        for budget in range(max(costs) + 1):
            faces = {s for s, birth in enumerate(births) if birth <= budget}
            missing = [s for s in range(count) if s not in faces and
                       all(s ^ (1 << i) in faces for i in range(vertices) if s >> i & 1)]
            higher = [s for s in missing if s.bit_count() >= 3]
            if higher and not any(w["center"] == center for w in first):
                support = min(higher, key=lambda s: (s.bit_count(), s))
                first.append({"center": center, "budget": budget, "support": support,
                              "cardinality": support.bit_count(),
                              "corner_cost": costs[support ^ (full if center else 0)]})
            dual = {s for s in range(count) if (full ^ s) not in faces}
            betti, dual_betti = reduced_betti(faces, vertices), reduced_betti(dual, vertices)
            # Augmented degrees include the empty/full cases, which are also recorded.
            for degree, dimension in betti.items():
                dual_degree = vertices - degree - 3
                assert dimension == dual_betti.get(dual_degree, 0), (center, budget, degree)
            levels.append({"budget": budget,
                           "face_counts_by_cardinality": [sum(s.bit_count() == k for s in faces)
                                                          for k in range(vertices + 1)],
                           "minimal_missing": missing,
                           "reduced_betti": betti, "dual_reduced_betti": dual_betti,
                           "dual_facets": sorted(full ^ s for s in missing)})
        links.append({"center": center, "births": births, "levels": levels})
    neighborhoods = []
    for budget in range(max(costs) + 1):
        easy = [f for f, c in enumerate(costs) if c <= budget]
        distances = [min((f ^ g).bit_count() for g in easy) for f in range(count)]
        neighborhoods.append({"budget": budget, "easy_count": len(easy), "distances": distances,
                              "volumes": [sum(d <= r for d in distances) for r in range(vertices + 1)],
                              "union_bounds": [min(count, len(easy) * sum(comb(vertices, j)
                                                   for j in range(r + 1)))
                                               for r in range(vertices + 1)]})
    return {"links": links, "first_higher_obstructions": first, "neighborhoods": neighborhoods}


def run(width: int, output: Path, solver_name: str, max_size: int) -> None:
    count = 1 << (1 << width)
    costs: list[int | None] = [None] * count
    witnesses: list[dict | None] = [None] * count
    for i, target in enumerate(input_tables(width)):
        costs[target] = 0
        witnesses[target] = {"gates": [], "output": i}
    searches = []
    started = time.monotonic()
    for size in range(1, max_size + 1):
        encoding = Encoding(width, size)
        sat, unsat = [], []
        with Solver(name=solver_name, bootstrap_with=encoding.clauses) as solver:
            for target in range(count):
                if costs[target] is not None:
                    continue
                if solver.solve(assumptions=encoding.assumptions(target)):
                    gates = encoding.witness(solver.get_model())
                    assert evaluate(width, gates) == target
                    costs[target] = size
                    witnesses[target] = {"gates": gates, "output": width + size - 1}
                    sat.append(target)
                else:
                    unsat.append(target)
                print(f"size={size} target={target} result={'SAT' if costs[target] is not None else 'UNSAT'}",
                      flush=True)
        searches.append({"size": size, "sat": sat, "unsat": unsat,
                         "variables": encoding.pool.top, "clauses": len(encoding.clauses),
                         "cnf_sha256": sha256(json.dumps(encoding.clauses).encode()).hexdigest()})
        checkpoint = {"width": width, "costs": costs, "witnesses": witnesses, "searches": searches}
        output.with_suffix(".partial.json").write_text(json.dumps(checkpoint) + "\n")
        print(f"Completed size {size}: {len(sat)} new functions; {len(unsat)} remain", flush=True)
        if all(c is not None for c in costs):
            break
    if any(c is None for c in costs):
        raise RuntimeError("Search limit reached; partial result retained, no exact dataset claimed")
    result = {"schema": 1, "width": width, "basis": "native De Morgan, all gates unit cost",
              "python": platform.python_version(), "python_sat": pysat.__version__, "solver": solver_name,
              "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
              "elapsed_seconds": round(time.monotonic() - started, 3),
              "costs": costs, "witnesses": witnesses, "searches": searches,
              "cost_histogram": dict(sorted(Counter(costs).items())), **geometry(width, costs)}
    output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    output.with_suffix(".partial.json").unlink()
    print(json.dumps({"cost_histogram": result["cost_histogram"],
                      "first_higher_obstructions": result["first_higher_obstructions"]}, indent=2))


def check(path: Path, solver_name: str) -> None:
    result = json.loads(path.read_text())
    width, costs = result["width"], result["costs"]
    assert len(costs) == 1 << (1 << width)
    for target, witness in enumerate(result["witnesses"]):
        assert len(witness["gates"]) == costs[target]
        assert evaluate(width, witness["gates"], witness["output"]) == target
    zero = set(input_tables(width))
    assert {f for f, cost in enumerate(costs) if cost == 0} == zero
    for size in sorted({c - 1 for c in costs if c > 1}):
        encoding = Encoding(width, size)
        with Solver(name=solver_name, bootstrap_with=encoding.clauses) as solver:
            for target, cost in enumerate(costs):
                if cost == size + 1:
                    assert not solver.solve(assumptions=encoding.assumptions(target)), (target, cost)
        print(f"Verified lower bounds at size {size}", flush=True)
    computed = geometry(width, costs)
    for key, value in computed.items():
        assert json.loads(json.dumps(value)) == result[key], key
    print("All witnesses, minimum-size lower queries, and geometric statistics verified.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--width", type=int, default=3)
    parser.add_argument("--max-size", type=int, default=8)
    parser.add_argument("--solver", default="cadical195")
    parser.add_argument("--output", type=Path, default=Path("research/circuit-stars/n3.json"))
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    if args.check:
        check(args.check, args.solver)
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        run(args.width, args.output, args.solver, args.max_size)


if __name__ == "__main__":
    main()
