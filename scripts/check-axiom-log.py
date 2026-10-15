#!/usr/bin/env python3
"""Match each audit declaration by name and reject nonstandard axioms.

Usage: check-axiom-log.py LOG [MANIFEST]
MANIFEST defaults to scripts/CheckAxioms.lean.
"""
import re
import sys
from pathlib import Path

if len(sys.argv) not in (2, 3):
    raise SystemExit(__doc__)
text = Path(sys.argv[1]).read_text(encoding='utf-8')
manifest = Path(sys.argv[2] if len(sys.argv) == 3 else 'scripts/CheckAxioms.lean')
expected = re.findall(r'^#print axioms\s+(\S+)\s*$', manifest.read_text(encoding='utf-8'), re.M)
if not expected or len(expected) != len(set(expected)):
    raise SystemExit('Audit manifest is empty or repeats declarations')
entries = re.findall(
    r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    text, re.M)
actual = [name for name, _ in entries]
if actual != expected:
    raise SystemExit(f'Audit declaration mismatch: expected {len(expected)}, found {len(actual)}; '
                     f'missing={sorted(set(expected) - set(actual))}; '
                     f'unexpected={sorted(set(actual) - set(expected))}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, entry in entries:
    names = {x.strip() for x in entry.split(',') if x.strip()}
    if names - allowed:
        raise SystemExit(f'Unexpected axioms for {name}: {names - allowed}')
print(f'PASS: {len(entries)} declarations matched by name; only standard kernel axioms')
