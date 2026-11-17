# Actual bounded chain restriction, 17 November 2026

## Exact endpoint

`GluingEPPA/Steiner/ChainValuation/ChainRestrictionNormalForm.lean` proves
`GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.chain_restriction`.
Its input is a literal `SeparatedChains D N S old L` test, a proper mask
`M` below `S`, and any vertex of the original test. Its conclusion concerns
the entire component reachable from that vertex by genuine `M`-edges.

There are two alternatives:

- an equivalence from the actual earlier Cayley group `old M` onto that
  whole component, preserving and reflecting every genuine `M`-edge;
- an actual smaller `SeparatedChains` test, using `smallerOld` and
  `smallerLinks`, with the same bound `N` and block count at most the
  original test's block count, together with the same exact labelled
  equivalence onto the whole component.

`chain_restriction_completed_actions` proves that the corresponding
equivalences intertwine every completed letter action for letters in
`M`. Absence of a genuine edge, and hence a fixed point introduced by the
partial-matching completion, is included in this statement.

## Why the source is an actual test

The proof starts from the finite chart induction on the actual original
chain, retaining an exact `NormalizedChainTrace` and its block bound.
The full/proper decision is made on that same trace. In the full case,
an embedded full-mask block is saturated under every `M`-letter, and
reachability makes its image the whole component. In the proper case,
the trace is reconstructed by the literal smaller chain builder.

The reconstruction uses the concrete triple-mask group reparameterization,
both pointwise attaching squares, and the exact ordered-build certificate.
It produces `NormalizedChainTrace.testEquiv` to the actual smaller test
with genuine-edge equivalence. The final wrapper composes its inverse
with the component chart, retaining the exact trace-length bound.

The canonical history is finally forgotten using
`coveredBuildNonempty_original_state`, an equality of the complete
dependent `SomeState`. Thus the final statement refers to
`chainState ... c` for the original input test, rather than to a separate
historical approximation of that state.

## Assumptions and manuscript correspondence

The theorem assumes the earlier `Data` records and their actual `Link`
records. `Link` packages both inclusion/deletion data and endpoint
replacement. The manuscript's induction setup therefore assumes earlier
requirements (a) and (b). The geometry does not introduce a new
conclusion-assuming component chart, equivariant cover, fixed-point
condition, or normalized separation hypothesis at the public endpoint.

The theorem covers the restriction lemma for every actual nonempty
bounded separated chain. An empty restriction alphabet is allowed; the
full-group alternative handles it. The result is stronger than the stated
bound of at most `N` blocks because it bounds the smaller source by the
original chain's own block count.

This closes the geometric normal-form statement of
`lem:chain-restriction`. It does not complete `lem:chain-exact-properties`
or the main Part II theorem. In particular, arbitrary old `Data` and
`Link` records are not assumed to contain the smaller test coordinates.
The simultaneous augmented recursive record must still be constructed,
or supplied with an explicit verified certificate recording those
actions, before the geometric theorem can establish that record's word
kernel compatibility. Cycle assembly and the local tree realization
statement retain their separate obligations.

## Validation

The exact final wrapper compiled on Lean 4.35.0-rc3 with exit code 0 and
no warnings on 17 November 2026. The durable manifest
`scripts/CheckChainRestrictionNormalFormAxioms.lean` audits the following
five declarations by their complete names:

- `ComponentNormalForm.mono`;
- `ComponentChart.normalForm`;
- `coveredBuildNonempty_original_state`;
- `chain_restriction`;
- `chain_restriction_completed_actions`.

The exact-name checker passed all five entries. Their dependencies are
only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`
or new axiom. The matched-step and finite/trace manifests were rerun on
the final sources and passed all seven and eight entries respectively.
`git diff --check` is clean, and the six new chart/trace/restriction source
files contain no `sorry`, `admit`, or `axiom` declarations.

The three supporting manifests are
`CheckMatchedComponentLastChartAxioms.lean`,
`CheckComponentTraceDichotomyAxioms.lean`, and
`CheckNormalizedTraceSeparatedTestAxioms.lean`, covering the actual matched
step, bounded finite induction and trace dichotomy, and literal smaller
test reconstruction respectively. No remote CI result or completion of
the main theorem is asserted here.
