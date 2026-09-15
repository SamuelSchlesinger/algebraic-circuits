#!/usr/bin/env python3
"""Check complete library/test imports and the elementary dependency boundaries."""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent


def imports(source: str) -> list[str]:
    """Read the Lean header, skipping line comments and nested block comments."""
    result = []
    offset = 0
    while offset < len(source):
        if source[offset].isspace():
            offset += 1
        elif source.startswith("--", offset):
            end = source.find("\n", offset)
            offset = len(source) if end < 0 else end + 1
        elif source.startswith("/-", offset):
            depth = 1
            offset += 2
            while offset < len(source) and depth:
                if source.startswith("/-", offset):
                    depth += 1
                    offset += 2
                elif source.startswith("-/", offset):
                    depth -= 1
                    offset += 2
                else:
                    offset += 1
            if depth:
                raise ValueError("unterminated Lean header comment")
        else:
            declaration = re.match(
                r"(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([\w.']+)",
                source[offset:],
            )
            marker = re.match(r"(?:module|prelude)\b", source[offset:])
            if declaration:
                result.append(declaration.group(1))
                offset += declaration.end()
            elif marker:
                offset += marker.end()
            else:
                break
    return result


def closure(graph: dict[str, list[str]], root: str) -> set[str]:
    """Include external imports as leaves so forbidden direct imports are visible."""
    seen = set()
    pending = [root]
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(graph.get(name, []))
    return seen


def check(root: Path) -> list[str]:
    files = {}
    for namespace in ("Algebraic", "AlgebraicTests"):
        paths = [root / f"{namespace}.lean", *(root / namespace).rglob("*.lean")]
        files.update({".".join(p.relative_to(root).with_suffix("").parts): p for p in paths})
    graph = {name: imports(path.read_text()) for name, path in files.items()}
    errors = []
    for name, dependencies in graph.items():
        for dependency in dependencies:
            if dependency.split(".")[0] in ("Algebraic", "AlgebraicTests"):
                if dependency not in files:
                    errors.append(f"{name} imports missing local module {dependency}")
            if name.split(".")[0] == "Algebraic" and dependency.split(".")[0] == "AlgebraicTests":
                errors.append(f"Library module {name} imports test module {dependency}")
    for namespace in ("Algebraic", "AlgebraicTests"):
        reached = closure(graph, namespace)
        for name in sorted(files):
            if name.split(".")[0] == namespace and name not in reached:
                errors.append(f"{namespace}.lean does not reach {name}")
    boundaries = {
        "Algebraic.Core": (
            "Algebraic.Basis", "Algebraic.LowerBound", "Algebraic.MassProduction",
            "Algebraic.Applications",
        ),
        "Algebraic.Basis.DeMorgan.Completeness": (
            "Algebraic.LowerBound", "Algebraic.MassProduction", "Algebraic.Complexity",
            "Algebraic.Basis.DeMorgan.Complexity",
        ),
        "Algebraic.Basis.DeMorgan.Complexity": (
            "Algebraic.LowerBound", "Algebraic.MassProduction",
        ),
    }
    for entry, forbidden in boundaries.items():
        if entry not in graph:
            errors.append(f"Missing dependency-boundary module {entry}")
        for dependency in sorted(closure(graph, entry)):
            if any(dependency == prefix or dependency.startswith(prefix + ".")
                   for prefix in forbidden):
                errors.append(f"{entry} unexpectedly depends on {dependency}")
            if dependency.startswith(("Cslib.Computability.Circuit.Boolean.Lupanov",
                                      "Cslib.Computability.Circuit.Boolean.Shannon")):
                errors.append(f"{entry} unexpectedly depends on sharp synthesis/counting: {dependency}")
    return errors


if __name__ == "__main__":
    errors = check(ROOT)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        sys.exit(1)
    print("Library/test import coverage and elementary dependency boundaries passed.")
