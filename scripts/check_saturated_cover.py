#!/usr/bin/env python3
"""Independent finite checks of the proposed saturated Boolean sparsening step.

Union-find computes the actual quotient. A separate linear-algebra invariant
classifies its vertices. Exhaustive clique search and cycle lifting do not use
the proposed mathematical proof. These are finite regression tests, not proofs
of the general sparsening theorem and not independent human/LLM referees.
"""
from __future__ import annotations
from itertools import combinations, permutations
from math import comb
import argparse
import json
import random
from pathlib import Path


def build(bags, edges=None):
    bags = tuple(frozenset(b) for b in bags)
    edges = tuple(combinations(range(len(bags)), 2)) if edges is None else tuple(edges)
    size = 1 << len(edges)
    parent = {}
    for a, bag in enumerate(bags):
        for chi in range(size):
            for x in bag:
                key = (a, chi, x)
                parent[key] = key
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    def join(a,b):
        a,b = find(a),find(b)
        if a != b:
            parent[b] = a
    for e,(a,b) in enumerate(edges):
        for chi in range(size):
            for x in bags[a] & bags[b]:
                join((a,chi,x),(b,chi^(1<<e),x))
    classes, representatives, projection = {}, {}, {}
    for key in parent:
        root = find(key)
        v = classes.setdefault(root,len(classes))
        representatives[key] = v
        projection[v] = key[2]
    atlas = set()
    adj = {v:set() for v in classes.values()}
    for a,bag in enumerate(bags):
        for chi in range(size):
            row = frozenset(representatives[a,chi,x] for x in bag)
            assert len(row) == len(bag)
            atlas.add(row)
            for x,y in combinations(row,2):
                adj[x].add(y)
                adj[y].add(x)
    return bags,edges,adj,atlas,projection,representatives


def maximal_cliques(adj):
    def search(r,p,x):
        if not p and not x:
            yield frozenset(r)
            return
        pivot = max(p|x,key=lambda u: len(p&adj[u])) if p|x else None
        for v in tuple(p-(adj[pivot] if pivot is not None else set())):
            yield from search(r|{v},p&adj[v],x&adj[v])
            p.remove(v)
            x.add(v)
    yield from search(set(),set(adj),set())


def boundary(chi,edges):
    result = 0
    for e,(a,b) in enumerate(edges):
        if (chi>>e)&1:
            result ^= (1<<a)|(1<<b)
    return result


def check_classification(data):
    bags,edges,adj,atlas,projection,rep = data
    universe = set().union(*bags)
    internal = {x:sum(1<<i for i,(a,b) in enumerate(edges)
                       if x in bags[a] and x in bags[b]) for x in universe}
    allmask = (1<<len(edges))-1
    key_to_vertex,vertex_to_key = {},{}
    for (a,chi,x),vertex in rep.items():
        key = (x, boundary(chi,edges)^(1<<a), chi&(allmask^internal[x]))
        assert key_to_vertex.setdefault(key,vertex) == vertex, ('incomplete invariant',bags,key)
        assert vertex_to_key.setdefault(vertex,key) == key, ('noninvariant',bags,vertex)
    return len(adj)


def check_cliques(data):
    bags,edges,adj,atlas,projection,rep = data
    count = 0
    for q in maximal_cliques(adj):
        assert q in atlas, ('uncovered maximal clique',bags,q)
        count += 1
    return count


def base_graph(bags):
    adj = {x:set() for b in bags for x in b}
    for b in bags:
        for x,y in combinations(b,2):
            adj[x].add(y); adj[y].add(x)
    return adj


def chordless_cycles(adj):
    vertices = sorted(adj)
    for k in range(4,len(vertices)+1):
        for subset in combinations(vertices,k):
            a,*rest = subset
            for tail in permutations(rest):
                c=(a,)+tail
                if c[1]>c[-1]:
                    continue
                if all(c[(i+1)%k] in adj[c[i]] for i in range(k)) and all(
                    (c[j] in adj[c[i]]) == ((j-i)%k in (1,k-1))
                    for i in range(k) for j in range(i+1,k)):
                    yield c


def check_cycle_projection(data):
    bags,edges,adj,atlas,projection,rep=data
    count=0
    for cycle in chordless_cycles(base_graph(bags)):
        count += 1
        for start in adj:
            if projection[start] != cycle[0]:
                continue
            frontier={start}
            for label in cycle[1:]:
                frontier={w for v in frontier for w in adj[v] if projection[w]==label}
            assert not any(start in adj[v] for v in frontier), ('cycle lifted',bags,cycle)
    return count


def rectangle():
    # Three differently indexed copies through u, and three through v.
    # The repeated rows are legitimate distinct automorphism charts.
    bags=[{0,1,2},{0,2,3},{0,2,3},{1,2,3},{1,2,3}]
    data=build(bags)
    _,edges,adj,atlas,projection,rep=data
    edge_index={e:i for i,e in enumerate(edges)}
    parity=lambda es: sum(1<<edge_index[tuple(sorted(e))] for e in es)
    alpha=parity([(0,1),(1,2),(2,0)])
    beta=parity([(0,3),(3,4),(4,0)])
    cycle=[rep[0,0,0],rep[0,0,1],rep[0,beta,0],rep[0,alpha,1]]
    assert len(set(cycle))==4
    assert all(cycle[(i+1)%4] in adj[cycle[i]] for i in range(4))
    assert cycle[2] not in adj[cycle[0]] and cycle[3] not in adj[cycle[1]]
    assert rep[0,alpha,0]==rep[0,0,0]
    assert rep[0,beta,1]==rep[0,0,1]
    return {'chart_bags':[sorted(b) for b in bags], 'edges':edges,
            'alpha':alpha,'beta':beta,'quotient_vertices':len(adj),
            'induced_cycle':cycle,'projection':[projection[v] for v in cycle]}


def incomplete_support_regression():
    # Two disjoint triangles: a remote parity cycle has zero boundary but
    # cannot be realized by a walk in the root's component.
    bags=[{0} for _ in range(6)]
    edges=[(0,1),(1,2),(0,2),(3,4),(4,5),(3,5)]
    data=build(bags,edges)
    remote=(1<<3)|(1<<4)|(1<<5)
    assert boundary(remote,edges)==0
    assert data[5][0,0,0] != data[5][0,remote,0]
    return {'zero_boundary_remote_cycle':remote,
            'same_boundary_but_different_transport_classes':True}


def check_rank(max_n=20):
    def rank(m,e):
        return comb(m,3)+(m-1)+comb(m,2)-e
    count=0
    for m in range(1,max_n+1):
        for e in range(comb(m,2)+1):
            for m2 in range(1,m):
                assert rank(m2,0) < rank(m,e)
                count+=1
            if e < comb(m,2):
                assert rank(m,e+1)<rank(m,e)
                count+=1
        assert rank(m,0) == comb(m+1,3)+m-1
    return count


def run(exhaustive=False):
    cases=[]
    if exhaustive:
        nonempty=[set(c) for k in range(1,5) for c in combinations(range(4),k)]
        for k in range(1,5):
            cases.extend(combinations(nonempty,k))
    else:
        cases.append([{0,1},{1,2},{2,3},{3,0}])
    rng=random.Random(20261014)
    triples=[set(c) for c in combinations(range(6),3)]
    for _ in range(150):
        cases.append(rng.sample(triples,4))
    cases.extend([[{0,1,2}]*k for k in range(1,5)])
    cases.extend([[set()],[set()]*4])
    cases.extend([[{i,(i+1)%n} for i in range(n)] for n in (4,5,6)])
    stats={'atlas_cases':0,'quotient_vertices_checked':0,'maximal_cliques_checked':0,
           'base_chordless_cycles_checked':0}
    for bags in cases:
        data=build(bags)
        stats['atlas_cases']+=1
        stats['quotient_vertices_checked']+=check_classification(data)
        stats['maximal_cliques_checked']+=check_cliques(data)
        stats['base_chordless_cycles_checked']+=check_cycle_projection(data)
    stats['rank_comparisons']=check_rank()
    stats['saturation_negative_regression']=incomplete_support_regression()
    stats['persistent_rectangle_seed']=rectangle()
    stats['scope']='Finite regressions only; no general theorem or independent referee approval inferred.'
    return stats


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--exhaustive',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=run(args.exhaustive)
    text=json.dumps(result,indent=2)
    if args.output:
        args.output.write_text(text+'\n')
    print(text)
