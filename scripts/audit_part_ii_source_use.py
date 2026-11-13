#!/usr/bin/env python3
"""Conservative Part II source-use inventory, not a semantic Lean proof audit.

Reports modules outside named proof-construction roots and declarations with
no lexical uses outside their definition. A declaration can be used through
field notation, elaboration, instances or automation; no candidate is deleted
or declared dead automatically. All.lean and #print axioms are NOT proof roots.
The checked kernel and separate axiom audit remain authoritative.
"""
from __future__ import annotations
import argparse
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'GluingEPPA.Steiner.ChainValuation.'
PROOF_ROOTS = [PREFIX + x for x in (
    'HistoricalInterfaceEquivalence', 'CoverRightAction', 'ChainTests',
    'AugmentedLinks', 'ComponentReflection', 'ChainEndpointIterate',
    'CycleUnwindingCore')]


def uncomment(text: str) -> str:
    """Erase nested Lean comments and string contents, preserving line numbers."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            if text[i] == '\\' and i + 1 < len(text):
                out.extend('  ')
                i += 2
            elif text[i] == '"':
                quoted = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0:
                out.extend(' ' * (len(text) - i))
                break
            out.extend(' ' * (end - i))
            i = end
        elif text[i] == '"':
            quoted = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or quoted:
        raise ValueError('Unterminated block comment or string')
    return ''.join(out)


def inspect() -> dict:
    paths = {'GluingEPPA.' + '.'.join(p.relative_to(ROOT / 'GluingEPPA').with_suffix('').parts): p
             for p in (ROOT / 'GluingEPPA').rglob('*.lean')}
    source = {m: uncomment(p.read_text()) for m, p in paths.items()}
    graph = {m: re.findall(r'^\s*import\s+(GluingEPPA\.[\w.]+)\s*$', s, re.M)
             for m, s in source.items()}
    missing_roots = [m for m in PROOF_ROOTS if m not in paths]
    if missing_roots:
        raise ValueError(f'Missing explicit roots: {missing_roots}')
    for m, deps in graph.items():
        unknown = set(deps) - paths.keys()
        if unknown:
            raise ValueError(f'Unknown imports in {m}: {sorted(unknown)}')

    def closure(roots):
        reached, stack = set(), list(roots)
        while stack:
            m = stack.pop()
            if m not in reached:
                reached.add(m)
                stack.extend(graph[m])
        return reached

    reached = closure(PROOF_ROOTS)
    local = {m for m in paths if m.startswith(PREFIX)}
    lexical_counts = Counter(re.findall(r"[\w']+", '\n'.join(source.values())))
    declarations, admissions, repeated = [], [], []
    pattern = re.compile(r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive)\s+([\w.']+)", re.M)
    for m in sorted(local):
        s = source[m]
        for match in pattern.finditer(s):
            short = match[2].rsplit('.', 1)[-1]
            if lexical_counts[short] <= 1:
                declarations.append({'module': m, 'declaration': match[2],
                    'line': s.count('\n', 0, match.start()) + 1,
                    'classification': 'no other lexical production use found; manual review required'})
        for match in re.finditer(r'\b(?:sorry|admit)\b|^\s*axiom\s', s, re.M):
            admissions.append({'module': m, 'line': s.count('\n', 0, match.start()) + 1})
        lines = s.splitlines()
        for i in range(1, len(lines)):
            if lines[i].strip().startswith('change ') and lines[i].strip() == lines[i-1].strip():
                repeated.append({'module': m, 'line': i + 1, 'tactic': lines[i].strip()})
    return {
        'status': 'INVENTORY_ONLY',
        'source_level_only': True,
        'semantic_declaration_dependency_check': False,
        'proof_roots': PROOF_ROOTS,
        'all_import_is_not_a_proof_root': True,
        'chain_modules': len(local),
        'modules_outside_selected_roots': sorted(local - reached - {PREFIX + 'All'}),
        'lexical_unused_candidates': declarations,
        'explicit_admission_tokens': admissions,
        'consecutive_duplicate_change_tactics': repeated,
        'unresolved_manuscript_obligations': [
            'all-length normalized M-component classification with edge/fixed-point reflection',
            'actual equivariant covers of every new separated-chain test',
            'simultaneous recursive augmented-Link/action construction',
            'instantiate the moving-endpoint contradiction for every bounded coset cycle',
            'set-valued structure transfer and all-copy local sections',
            'Part III path-closed amalgamation and girth-transfer assembly'],
        'interpretation': 'Import closure measures available infrastructure; lexical references are not kernel dependency edges. No unused-candidate count is a completion percentage.'
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = inspect()
    text = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text)
    return 1 if result['explicit_admission_tokens'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
