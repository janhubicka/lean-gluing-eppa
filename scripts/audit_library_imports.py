#!/usr/bin/env python3
"""Audit the local Lean import DAG and recommend a smaller umbrella import list.

Purely structural: no Lean proof is accepted on this evidence. The CI Lean
build and the separate named-axiom audit remain authoritative.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*$")


def inspect() -> dict:
    files = sorted((ROOT / "GluingEPPA").rglob("*.lean"))
    paths = {
        "GluingEPPA." + ".".join(p.relative_to(ROOT / "GluingEPPA").with_suffix("").parts): p
        for p in files
    }
    graph = {}
    for mod, path in paths.items():
        text = path.read_text(encoding="utf8")
        graph[mod] = [name for name in IMPORT.findall(text) if name.startswith("GluingEPPA.")]
    umbrella = IMPORT.findall((ROOT / "GluingEPPA.lean").read_text(encoding="utf8"))
    known = set(paths)
    bad = {
        path: [name for name in deps if name not in known]
        for path, deps in graph.items()
        if any(name not in known for name in deps)
    }
    missing_root = [x for x in umbrella if x.startswith("GluingEPPA.") and x not in known]
    if bad or missing_root:
        raise ValueError(f"Unknown local imports: {bad}; umbrella: {missing_root}")
    state = {}  # 1 visiting, 2 complete
    reached = {}

    def descendants(mod: str) -> set[str]:
        if state.get(mod) == 1:
            raise ValueError(f"Import cycle through {mod}")
        if state.get(mod) == 2:
            return reached[mod]
        state[mod] = 1
        out = {mod}
        for dep in graph[mod]:
            out |= descendants(dep)
        reached[mod] = out
        state[mod] = 2
        return out

    for mod in graph:
        descendants(mod)
    root_imports = [x for x in umbrella if x in known]
    root_closure = set().union(*(descendants(x) for x in root_imports))
    uncovered = sorted(known - root_closure)
    minimal = [
        x for x in root_imports
        if not any(x in descendants(y) for y in root_imports if x != y)
    ]
    minimal_closure = set().union(*(descendants(x) for x in minimal))
    if set(minimal_closure) != set(root_closure):
        raise ValueError("Suggested import reduction does not preserve reachable modules")
    duplicates = sorted(x for x, n in Counter(umbrella).items() if n > 1)
    lines = sum(p.read_text(encoding="utf8").count("\n") + 1 for p in files)
    stats = {
        "status": "PASS" if not uncovered and not duplicates else "FAIL",
        "lean_modules": len(known),
        "source_lines": lines,
        "umbrella_imports": len(umbrella),
        "umbrella_duplicate_imports": duplicates,
        "umbrella_uncovered_modules": uncovered,
        "suggested_minimal_umbrella_imports": minimal,
        "suggested_minimal_import_count": len(minimal),
        "local_module_import_edges": sum(len(deps) for deps in graph.values()),
        "source_level_only": True,
    }
    return stats


def main() -> int:
    try:
        result = inspect()
    except (ValueError, OSError) as exc:
        print(f"FAILED STRUCTURAL IMPORT AUDIT: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
