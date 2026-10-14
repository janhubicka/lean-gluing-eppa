#!/usr/bin/env python3
"""Exhaustive small orbit-atlas tests, independent of Lean/record equality.
Quotients are built by union-find on supported occurrence walks. Old automorphisms
and the canonical set of closed subcharts are enumerated from finite data.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path


def check_case(name: str, n: int, root: frozenset[int],
               outputs: tuple[tuple[frozenset[int], ...], ...]) -> dict:
    points = range(n)
    def im(h, s): return frozenset(h[x] for x in s)
    autos = tuple(h for h in itertools.permutations(points)
                  if all(im(h, out[x]) == out[h[x]] for out in outputs for x in points))
    identity = tuple(points)
    def inverse(h): return tuple(h.index(x) for x in points)
    def compose(h, g): return tuple(g[h[x]] for x in points)
    def closed(s): return all(out[x] <= s for out in outputs for x in s)
    assert closed(root)
    all_sets = tuple(frozenset(x for x in points if bits >> x & 1)
                     for bits in range(1 << n))
    full = {im(h, root) for h in autos}
    charts = tuple(sorted((s for s in all_sets if closed(s) and any(s <= t for t in full)),
                          key=lambda s: (len(s), tuple(sorted(s)))))
    assert frozenset() in charts and root in charts
    index = {s: i for i, s in enumerate(charts)}
    m = len(charts)
    edges = tuple(itertools.combinations(range(m), 2))
    ei = {e: i for i, e in enumerate(edges)}
    count = 1 << len(edges)
    def spoke(s, t): return 0 if s == t else 1 << ei[tuple(sorted((s, t)))]
    cp = {h: tuple(index[im(h, s)] for s in charts) for h in autos}
    ep = {h: tuple(ei[tuple(sorted((cp[h][s], cp[h][t])))] for s, t in edges)
          for h in autos}
    def vector(h, bits):
        return sum(1 << ep[h][e] for e in range(len(edges)) if bits >> e & 1)
    chart_compositions = edge_compositions = 0
    for h, g in itertools.product(autos, repeat=2):
        gh = compose(h, g)
        assert gh in cp
        for s in range(m):
            assert cp[gh][s] == cp[g][cp[h][s]]
            chart_compositions += 1
        for e in range(len(edges)):
            assert ep[gh][e] == ep[g][ep[h][e]]
            edge_compositions += 1
    for h in autos:
        assert sorted(cp[h]) == list(range(m))
        for s, chart in enumerate(charts):
            assert closed(chart) and im(h, chart) == charts[cp[h][s]]
        for e, (s, t) in enumerate(edges):
            assert set(edges[ep[h][e]]) == {cp[h][s], cp[h][t]}
    occurrences = tuple((s, b, x) for s, chart in enumerate(charts)
                        for b in range(count) for x in sorted(chart))
    ids = {q: i for i, q in enumerate(occurrences)}
    parent = list(range(len(occurrences)))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    def union(a, b):
        a, b = find(a), find(b)
        if a != b: parent[b] = a
    for e, (s, t) in enumerate(edges):
        for x in charts[s] & charts[t]:
            for b in range(count): union(ids[s, b, x], ids[t, b ^ (1 << e), x])
    cls = tuple(find(i) for i in range(len(occurrences)))
    def q(s, b, x): return cls[ids[s, b, x]]
    reps = {}
    for o, c in zip(occurrences, cls): reps.setdefault(c, o)
    def action(h, delta, o):
        s, b, x = o
        return q(cp[h][s], vector(h, b) ^ delta, h[x])
    action_checks = 0
    action_tables = {}
    for h in autos:
        for delta in range(count):
            tab = {}
            for o, c in zip(occurrences, cls):
                d = action(h, delta, o)
                assert c not in tab or tab[c] == d
                tab[c] = d
                action_checks += 1
            assert len(set(tab.values())) == len(reps)
            action_tables[h, delta] = tab
    root_id = index[root]
    root_points = {q(root_id, 0, x) for x in root}
    movements = 0
    for s, chart in enumerate(charts):
        h = next(h for h in autos if chart <= im(h, root))
        t = cp[h][root_id]
        back = inverse(h)
        for b in range(count):
            psi = b ^ spoke(s, t)
            delta = vector(back, psi)
            tab = action_tables[back, delta]
            for x in chart:
                assert q(s, b, x) == q(t, psi, x)
                assert tab[q(s, b, x)] == q(root_id, 0, back[x])
                assert tab[q(s, b, x)] in root_points
                movements += 1
    extensions = tuple((h, s, cp[h][s]) for h in autos for s, chart in enumerate(charts)
                       if chart <= root and charts[cp[h][s]] <= root)
    def correction(h, s, t): return spoke(root_id, t) ^ vector(h, spoke(root_id, s))
    root_movers = point_extensions = 0
    for h, s, t in extensions:
        if cp[h][root_id] != root_id and charts[s]: root_movers += 1
        delta = correction(h, s, t)
        tab = action_tables[h, delta]
        for x in charts[s]:
            assert tab[q(root_id, 0, x)] == q(root_id, 0, h[x])
            point_extensions += 1
    compositions = quotient_compositions = 0
    for (h, s, t), (g, t2, u) in itertools.product(extensions, repeat=2):
        if t != t2: continue
        gh = compose(h, g)
        d, e = correction(h, s, t), correction(g, t, u)
        assert correction(gh, s, u) == e ^ vector(g, d)
        th, tg, tgh = action_tables[h, d], action_tables[g, e], action_tables[gh, correction(gh,s,u)]
        for c in reps:
            assert tg[th[c]] == tgh[c]
            quotient_compositions += 1
        compositions += 1
    for s, chart in enumerate(charts):
        if chart <= root:
            assert correction(identity, s, s) == 0
    bad_frozen = sum(1 for h in autos for s, chart in enumerate(charts)
                     for x in chart if h[x] not in chart)
    if len(full) > 1: assert bad_frozen > 0
    return dict(name=name, points=n, old_automorphisms=len(autos), charts=m,
                full_charts=len(full), edges=len(edges), valid_occurrences=len(occurrences),
                quotient_vertices=len(reps), chart_compositions=chart_compositions,
                edge_compositions=edge_compositions, affine_occurrence_checks=action_checks,
                chart_movement_points=movements, extensions=len(extensions),
                nonempty_root_moving_extensions=root_movers, point_extensions=point_extensions,
                endpoint_compositions=compositions, quotient_compositions=quotient_compositions,
                frozen_chart_mutation_failures=bad_frozen)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases = [
        ('empty-root', 2, frozenset(), ()),
        ('singleton-orbit', 3, frozenset({0}), ()),
        ('all-subsets-two-points', 2, frozenset({0,1}), ()),
        ('branching-pairs', 4, frozenset({0,1}),
         ((frozenset({0,1}),frozenset({0,1}),frozenset({2,3}),frozenset({2,3})),)),
        ('shared-closed-sink', 3, frozenset({0,2}),
         ((frozenset({2}),frozenset({2}),frozenset({2})),
          (frozenset({0,2}),frozenset({1,2}),frozenset({2}))))]
    result = [check_case(*case) for case in cases]
    summary = {'cases': result, 'totals': {k:sum(c[k] for c in result)
               for k in result[0] if k != 'name'}}
    text = json.dumps(summary, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text)

if __name__ == '__main__': main()
