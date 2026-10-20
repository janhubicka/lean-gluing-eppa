# Validation of the current recursive gluing manuscript

## Target and fidelity rule

The target is `janhubicka/Otto-simplified`, `steiner_recursive_gluing_valuations.tex`,
first committed to main as `e5fbd413ebe7b8fa432efe0b5732007bc734a8fd` (v7).
Validate this text and its construction, not just the same EPPA statement.
Fix and improve the manuscript as discrepancies are found, keeping a record.
No manuscript TeX belongs in the Lean repository.

This branch starts at Lean main `d6fb12b6a816fc8630e5b04c02e51c32697b801d`.
The older Steiner PR #64 is a source of reusable lemmas, NOT a certificate
for this draft. Its group and quotient theorems are not imported here.

## Reused ingredient

`GluingEPPA/Steiner/WalkValues.lean` is reused unchanged (blob
`b9a8787afcc90171c54b6795387eef067f841641`). Its `WalkValue` is an inductive
predicate on actual named-edge walks. It supplies concatenation, reversal,
monotonicity, and evaluation under group homomorphisms. It assumes no
recursion, synchronization, or EPPA conclusion.

## Current submitted step

Code checkpoint: `0fe1ef3c44dfdc2bde83866e0aed95bcefd93f6f`.
Current check: [Actions #301](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/39477594824).
Status at this checkpoint: in progress; no completed axiom-audited certificate yet.

- `CayleyLift.lean` defines actual lifted walks, one step at a time, with
  exactly the rule `(u,g) -> (v,g*a_e)` from manuscript equation (4).
  An M-walk retains the ambient group. It proves lifting and projection
  with exact value `g^-1*h`, concatenation, reversal and deck invariance.
- `CayleyComponents.lean` defines C_M from connected components of those
  walks. It proves the quotient equality criterion, finiteness, deck
  translations, and the right action `c(u,g) h = c(u,h^-1*g)` in equation (9).
- Distinct distinguished components are proved under precisely the
  value-one hypothesis which the induction must supply. That hypothesis
  is not silently assumed to hold in the final construction.
- `CheckCayleyComponentsAxioms.lean` checks 18 exact declaration names.

The initial [Actions #300](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/39476414633)
compiled `CayleyLift.lean` but stopped on one elaboration error in
`CayleyComponents.component_eq_iff`: Lean did not infer the intended
setoid for `Quotient.sound`. The current checkpoint supplies that setoid
explicitly. No mathematical definition or manuscript statement changed.
The downloaded failed-run artifact and its SHA256 manifest were checked;
its recorded test-merge commit is `887284a38b0e63188735a1a7e53c23c36167d74a`.

## Remaining manuscript correspondence

| Current text | Status |
| --- | --- |
| Section 2: survey-style set-valued functions and closed Steiner systems | Reuse candidates exist; exact correspondence not yet certified here |
| Section 3: binary diagram and edges paired with reverse tuples | Adapter to named edges not yet formalized |
| Section 3: Boolean lift and support lemma | Existing parity infrastructure; manuscript interface still to check |
| Section 4: actual Cayley lift, C_T, and deck-induced right action | New submitted definitions and proofs listed above |
| Section 4: tau_e^T (internal deck action / outside transposition) | Next target |
| Lemma 4.1: j_N^T, its injectivity, and the two invariant actions | Must be proved for these actual component sets |
| Theorem 4.2: direct-record simultaneous recursion (I)-(II) and naturality | Not yet validated for this draft |
| Remark 4.3: Boolean quotient | Not yet validated for this draft |
| Corollary 4.4: exact component intersection | Not yet validated for this draft |
| Lemma 5.1: genuine point quotient and closed induced free realization | Not yet validated for this draft |
| Section 6 and Theorem 1.1: labelled bipartite inclusion diagram and coherent extensions | Not yet validated for this draft |

## Reuse boundary

Any reuse of an older transport-quotient presentation must first exhibit
its equivalence with these actual connected components and verify the
component permutations and group-action conventions. The direct valuation
record must still be instantiated for the current manuscript. An abstract
existence theorem for another finite group is not that verification.

The main theorem has no Lean-verified marker. A passed elementary component
module is not a completed compatibility lemma or an unconditional EPPA theorem.
