#!/usr/bin/env python3
"""Reject missing audit output and nonstandard axiom dependencies."""
import re
import sys
from pathlib import Path
text = Path(sys.argv[1]).read_text()
entries = re.findall(r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms", text)
expected = len(re.findall(r'^#print axioms ', Path('scripts/CheckAxioms.lean').read_text(), re.M))
if len(entries) != expected:
    raise SystemExit(f"Expected {expected} declarations, found {len(entries)}")
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for entry in entries:
    names = {x.strip() for x in entry.split(',') if x.strip()}
    if names - allowed:
        raise SystemExit(f"Unexpected axioms: {names - allowed}")
print(f'PASS: {len(entries)} declarations; only standard kernel axioms')
