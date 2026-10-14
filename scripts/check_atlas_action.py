#!/usr/bin/env python3
"""Finite affine-atlas regressions, using actual union-find quotient classes.
These computations are supplementary tests, not a proof of sparsening.
"""
from __future__ import annotations
import argparse
import itertools as it
import json
from pathlib import Path


def run_case(n, charts, outputs, exhaustive_delta=True):
    charts = tuple(frozenset(s) for s in charts)
    edges = tuple(it.combinations(range(len(charts)), 2))
    eindex = {e: i for i, e in enumerate(edges)}
    nval = 1 << len(edges)
    nodes = [(s, c, x) for s, C in enumerate(charts) for c in range(nval) for x in sorted(C)]
    index = {p: i for i, p in enumerate(nodes)}
    parents = list(range(len(nodes)))
    def find(i):
        while parents[i] != i:
            parents[i] = parents[parents[i]]
            i = parents[i]
        return i
    def union(a, b):
        a, b = find(a), find(b)
        if a != b:
            parents[b] = a
    for ei, (s, t) in enumerate(edges):
        for x in charts[s] & charts[t]:
            for c in range(nval):
                union(index[s, c, x], index[t, c ^ (1 << ei), x])
    cls = [find(i) for i in range(len(nodes))]
    representatives = {}
    for p, i in index.items():
        representatives.setdefault(cls[i], p)
    qs = tuple(representatives)
    def qcopy(s, c, x):
        return cls[index[s, c, x]]
    fibres = {}
    for (s, c, x), i in index.items():
        assert outputs[x] <= charts[s], 'old chart not closed'
        vals = {qcopy(s, c, y) for y in outputs[x]}
        if cls[i] in fibres:
            assert fibres[cls[i]] == vals
        fibres[cls[i]] = vals
    binary, ternary = set(), set()
    for s, C in enumerate(charts):
        for c in range(nval):
            for x, y in it.product(C, repeat=2):
                a, b = qcopy(s, c, x), qcopy(s, c, y)
                binary.add((a, b))
                ternary.add((a, b, a))
    perms, push, cp = [], {}, {}
    for h in it.permutations(range(n)):
        image = [frozenset(h[x] for x in C) for C in charts]
        if any(C not in charts for C in image):
            continue
        if any({h[y] for y in outputs[x]} != outputs[h[x]] for x in range(n)):
            continue
        perms.append(h)
        cp[h] = tuple(charts.index(C) for C in image)
        ep = [eindex[tuple(sorted((cp[h][s], cp[h][t])))] for s, t in edges]
        push[h] = [sum(1 << ep[i] for i in range(len(edges)) if c >> i & 1) for c in range(nval)]
    deltas = tuple(range(nval)) if exhaustive_delta else tuple(sorted({0, nval-1, *[1 << i for i in range(len(edges))]}))
    actions = {}
    stats = {'valid_occurrences': len(nodes), 'quotient_vertices': len(qs), 'actions': 0,
             'descent_checks': 0, 'inverse_checks': 0, 'unary_fibre_checks': 0,
             'binary_tuple_checks': 0, 'repeated_ternary_checks': 0, 'composition_checks': 0,
             'nullary_checks': 0, 'negative_controls_detected': 0,
             'endpoint_checks': 0, 'coherent_compositions': 0}
    for h, d in it.product(perms, deltas):
        m = {}
        for (s, c, x), i in index.items():
            z = qcopy(cp[h][s], push[h][c] ^ d, h[x])
            q = cls[i]
            assert q not in m or m[q] == z
            m[q] = z
            stats['descent_checks'] += 1
        assert len(set(m.values())) == len(qs)
        actions[h, d] = m
        stats['actions'] += 1
        for q in qs:
            assert {m[z] for z in fibres[q]} == fibres[m[q]]
            stats['unary_fibre_checks'] += 1
        for a, b in binary:
            assert (m[a], m[b]) in binary
            stats['binary_tuple_checks'] += 1
        for a, b, c in ternary:
            assert (m[a], m[b], m[c]) in ternary
            stats['repeated_ternary_checks'] += 1
        for truth in (False, True):
            assert (bool(charts) and truth) == (bool({cp[h][s] for s in range(len(charts))}) and truth)
            stats['nullary_checks'] += 1
        inv = tuple(h.index(i) for i in range(n))
        invd = push[inv][d]
        for q in qs:
            t, b, y = representatives[m[q]]
            assert qcopy(cp[inv][t], push[inv][b] ^ invd, inv[y]) == q
            stats['inverse_checks'] += 1
    pairs = list(actions)
    for k, (h, d) in enumerate(pairs):
        g, e = pairs[(37*k+11) % len(pairs)]
        gh = tuple(g[h[x]] for x in range(n))
        combined = e ^ push[g][d]
        for q, (s, c, x) in representatives.items():
            assert actions[g, e][actions[h, d][q]] == qcopy(cp[gh][s], push[gh][c] ^ combined, gh[x])
            stats['composition_checks'] += 1
    # Negative control: do not permute edge coordinates.
    bad_descent = False
    for h in perms:
        seen = {}
        for (s, c, x), i in index.items():
            q, z = cls[i], qcopy(cp[h][s], c, h[x])
            if q in seen and seen[q] != z:
                bad_descent = True
                break
            seen[q] = z
        if bad_descent:
            break
    assert bad_descent, 'unpermuted-coordinate fault was not detected'
    stats['negative_controls_detected'] += 1
    # Negative control: fail to pull back the inverse translation.
    bad_inverse = False
    for h, d in actions:
        inv = tuple(h.index(i) for i in range(n))
        if push[inv][d] == d:
            continue
        for q in qs:
            t, b, y = representatives[actions[h, d][q]]
            if qcopy(cp[inv][t], push[inv][b] ^ d, inv[y]) != q:
                bad_inverse = True
                break
        if bad_inverse:
            break
    assert bad_inverse, 'wrong inverse-translation fault was not detected'
    stats['negative_controls_detected'] += 1
    root = frozenset(range(n))
    if root in charts and all(frozenset(D) in charts for k in range(n+1) for D in it.combinations(range(n), k)):
        ri = charts.index(root)
        def eta(si):
            return 0 if si == ri else 1 << eindex[tuple(sorted((ri, si)))]
        partials = []
        for k in range(n+1):
            for dom in it.combinations(range(n), k):
                for ran in it.combinations(range(n), k):
                    for targets in it.permutations(ran):
                        f = dict(zip(dom, targets))
                        h = list(range(n))
                        restD, restR = sorted(set(range(n))-set(dom)), sorted(set(range(n))-set(ran))
                        for a, b in it.chain(f.items(), zip(restD, restR)):
                            h[a] = b
                        h = tuple(h)
                        if h not in perms:
                            continue
                        di, rr = charts.index(frozenset(dom)), charts.index(frozenset(ran))
                        d = eta(rr) ^ push[h][eta(di)]
                        partials.append((frozenset(dom), frozenset(ran), f, h, d))
                        for x in dom:
                            assert qcopy(cp[h][ri], d, h[x]) == qcopy(ri, 0, f[x])
                            stats['endpoint_checks'] += 1
        for D, R, f, h, d in partials:
            for R2, T, g, k, e in partials:
                if R != R2:
                    continue
                gf = {x: g[f[x]] for x in D}
                choices = [a for a in partials if a[0] == D and a[1] == T and a[2] == gf]
                assert len(choices) == 1
                hh, dd = choices[0][3:]
                assert hh == tuple(k[h[x]] for x in range(n))
                assert dd == e ^ push[k][d]
                for q, (s, c, x) in representatives.items():
                    p = qcopy(cp[hh][s], push[hh][c] ^ dd, hh[x])
                    first = qcopy(cp[h][s], push[h][c] ^ d, h[x])
                    t, b, y = representatives[first]
                    assert qcopy(cp[k][t], push[k][b] ^ e, k[y]) == p
                    stats['coherent_compositions'] += 1
    return stats


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases = {
        'two_points_all_subcharts': run_case(2, [[], [0], [1], [0, 1]], [{0}, {1}]),
        'two_closed_cyclic_blocks': run_case(4, [[], [0, 1], [2, 3], [0, 1, 2, 3]], [{0, 1}, {0, 1}, {2, 3}, {2, 3}]),
        'triangle_and_proper_charts': run_case(3, [[], [0, 1], [1, 2], [0, 2], [0, 1, 2]], [set(), set(), set()], False),
    }
    total = {key: sum(v[key] for v in cases.values()) for key in next(iter(cases.values()))}
    result = {'status': 'PASS', 'method': 'union-find on valid supported occurrences, not record classification', 'cases': cases, 'totals': total}
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+'\n')
    print(text)


if __name__ == '__main__':
    main()
