# Bounded finite component-chart induction, 17 November 2026

## Checked finite endpoint

`ComponentChartInduction.lean` proves
`coveredBuildNonempty_componentsCharted` for every nonempty separated
original list and every proper restriction mask `M`.

The result concerns the literal chain state in the canonical
`coveredNamedAlignedBuildNonempty` history. For every actual component
root it supplies a `ComponentChart` with an equivalence onto the whole
reachable component and preservation and reflection of genuine edges
for every letter in `M`. Components meeting the original last block
also receive the stronger `ComponentLastChart` with exact translated
last coordinates and entry-coordinate containment.

Both chart types now carry a `NormalizedChainTrace` indexed by their
exact source `ChainState`. Thus the source is certified to start with
one actual restricted earlier Cayley block and to grow only through
literal separated normalized attachments. It is not an arbitrary graph
or an independently postulated component normal form.

The endpoint also proves

```
chart.trace.length ≤ atoms.length.
```

An unmatched new component starts with one block. A matched extension
adds one block. An unmatched old component keeps its source and its
block count. These bounds are retained through the actual finite tail
recursion, including changes in the component root.

## Why two chart invariants are needed

If an old component misses a newly attached block `B`, its source's last
mask stays unchanged while the original chain's last mask becomes `B`.
A last-block chart cannot correctly be retained with this new index.
The plain chart therefore stores its source mask independently, while
the live last-block chart retains the stronger pointwise identity used
at the next matched attachment.

The next normalized shift is proved to exist from the checked
`LastMaskCoset` invariant and the current last-coordinate equation.
The old and new unmatched cases use the existing exact unmatched
component equivalences and their genuine-edge reflection. In
particular, no unproved fixed-point equivariance is assumed.

## Source provenance

`NormalizedChainTrace.lean` is checked. Its `single` and `attach`
constructors retain the actual original masks, normalized shifts,
separation proofs, and resulting states. It exposes positive block
count and, when all recorded masks restrict properly in `M`, the exact
ordered `NormalizedProperSource` list with identical masks and length.
The unused last shift is supplied as an argument; a subsequent
attachment supplies the preceding list's terminal shift directly.

## Completed bridge to the actual smaller test

`NormalizedProperAttachmentEquiv.lean` reparameterizes the common group
indices `M ∩ (A ∩ B)` and `(M ∩ A) ∩ (M ∩ B)` using a concrete group
equivalence and both pointwise attaching squares. It transports the
actual attachment quotient and reflects every genuine labelled edge.
`OrderedBuildTrace.lean` identifies a finite succession of literal
attachments with the literal nonempty chain builder.
`NormalizedTraceSeparatedTest.lean` therefore realizes this same source
trace as an actual smaller `SeparatedChains` test, with exact ordered
source atoms, equal length, a whole-state equivalence, genuine-edge
reflection, and completed-action conjugacy.

`ChainRestrictionNormalForm.lean` then combines the proper realization
with the full alternative below, transports the canonical history to the
original test's exact dependent state, and proves `chain_restriction`.
The source uses the same bound `N`, with block count at most that of the
original test. Its completed-letter corollary includes fixed points.

The remaining construction issue is the simultaneous augmented recursive
family: the old record must record all smaller chain-test actions before
the chain restriction theorem can transfer its word kernel. This is not
a missing component-chart or source-builder identification lemma.

## Checked full-or-proper trace dichotomy

`NormalizedTraceBlocks.lean` proves that every mask retained by the trace
has an injective genuine-edge embedding of its restricted Cayley group
into the exact final source state. `ComponentTraceDichotomy.lean` then
proves `ComponentChart.full_or_proper`:

- either the actual earlier Cayley group `old M` is equivalent to the
  entire original component, preserving and reflecting every genuine
  `M`-edge;
- or every mask in this same construction trace restricts properly in
  `M`, supplying exactly the hypothesis of `trace.sources`.

For a full-mask block, composing its trace embedding with the actual
component chart gives an image with an internal neighbour for every
`M`-letter. Matching uniqueness makes this image saturated. Every target
component vertex is connected to the image of the identity, so the image
is the entire component. This avoids a separate source-connectedness
assumption and avoids matching the trace's choices against an independent
historical normalization.

## Validation

`NormalizedChainTrace.lean`, the trace-enriched
`MatchedComponentLastChart.lean`, `ComponentChartInduction.lean`,
`NormalizedTraceBlocks.lean`, and `ComponentTraceDichotomy.lean`
compiled locally on Lean 4.35.0-rc3 with exit code 0 on 17 November 2026.
The finite induction, block embedding, and dichotomy modules produced no
warnings. The durable
`scripts/CheckComponentTraceDichotomyAxioms.lean` manifest gives an
eight-endpoint `#print axioms` audit, including source-list
identities, block embeddings, matched extension, derived shift existence,
the bounded finite endpoint, and both full-block/dichotomy theorems,
reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no
`sorry` or `admit` declarations. The final wrapper's separate validation
is recorded in `part-ii-chain-restriction-20261117.md`; this manifest does
not assert completion of the main Part II theorem or a remote CI result.
