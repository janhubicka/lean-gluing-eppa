#!/usr/bin/env python3
"""Check navigation and relative file links in the source-controlled wiki.

This checks documentation sources, not the existence of a GitHub Wiki
remote and not the validity of any Lean theorem.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]
WIKI = ROOT / "docs" / "wiki"
LINK = re.compile(r"(?<!!)\[[^]]+\]\(([^)\n]+)\)")
REQUIRED = {
    "README.md", "_Sidebar.md", "Publishing.md",
    "Using-the-library.md", "Published-statements.md",
    "Proof-architecture.md", "Finite-relational-EPPA.md",
    "Sparsening-construction.md", "Auxiliary-lemmas.md",
    "Adversarial-referee-record.md", "Development-and-audit.md",
}


def main() -> int:
    pages = sorted(WIKI.glob("*.md"))
    present = {p.name for p in pages}
    errors = [f"Missing wiki page: {x}" for x in sorted(REQUIRED - present)]
    relative_links = 0
    for page in pages:
        text = page.read_text(encoding="utf-8")
        if page.name != "_Sidebar.md" and not text.lstrip().startswith("# "):
            errors.append(f"{page.name}: first-level title missing")
        if "\\" + chr(96) in text:
            errors.append(f"{page.name}: escaped inline-code backticks")
        for match in LINK.finditer(text):
            raw = match.group(1).strip().split()[0]
            if raw.startswith(("#", "https://", "http://", "mailto:", "data:")):
                continue
            path = unquote(raw.split("#", 1)[0])
            if not path:
                continue
            target = (page.parent / path).resolve()
            relative_links += 1
            if not target.is_relative_to(ROOT.resolve()) or not target.exists():
                errors.append(f"{page.name}: unresolved relative link {raw}")
    sidebar = WIKI / "_Sidebar.md"
    if sidebar.exists():
        src = sidebar.read_text(encoding="utf-8")
        for page in sorted(REQUIRED - {"_Sidebar.md"}):
            if f"({page})" not in src:
                errors.append(f"Sidebar does not list {page}")
    result = {
        "status": "PASS" if not errors else "FAIL",
        "wiki_pages": len(pages),
        "relative_links_checked": relative_links,
        "required_pages": len(REQUIRED),
        "problems": errors,
        "scope": "source Markdown and relative link validity only",
    }
    print(json.dumps(result, indent=2))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
