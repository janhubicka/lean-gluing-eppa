import GluingEPPA.Steiner.ChainValuation.CoupledHistoryOriginalCorrespondence

/-!
# Actual finite-chain source masks and adjacent boundary masks agree

The same finite coupled history has both the source-named Cayley
blocks and the genuine witnessed interfaces. We prove directly
that the source-mask list is the input sequence, and hence that the
adjacent mask pairs of its named blocks are *exactly* the mask pairs
of its stored true historical boundaries.

Unlike a comparison of independent hypothetical histories, both
sides here are fields of one proof-carrying original LinkChain state.
This still does not identify the full normalized M-component with
a smaller-mask quotient or reflect completed letter actions.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

/-- The actual coupled tail appends exactly its new original source
masks, never changing the masks of previous historical blocks. -/
theorem coupledHistoryBuildTail_sources
    (M : Proper S) (p c : Atom S old)
    (H : CoupledNamedBoundaryHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (coupledHistoryBuildTail D S old L M p c H hp hc rest hsep).
        named.sourceMasks =
      H.named.sourceMasks ++ rest.map (fun a => a.1) := by
  induction rest generalizing p c H with
  | nil =>
      simp only [coupledHistoryBuildTail, List.map_nil, List.append_nil]
  | cons z zs ih =>
      have hstep :
          (match H.named.data.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coupledHistoryStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      change
        (coupledHistoryBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).named.sourceMasks =
          H.named.sourceMasks ++ (z :: zs).map (fun a => a.1)
      rw [ih c z HN hnp hnc hsep.2]
      have hHN : HN.named.sourceMasks = H.named.sourceMasks ++ [z.1] := rfl
      rw [hHN]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-- Every source block in the original finite input appears at
the corresponding index of the coupled named historical chart
list, even when the same mask occurs more than once. -/
theorem coupledHistoryBuildNonempty_sourceMasks
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coupledHistoryBuildNonempty D S old L M atoms hne hsep).
        named.sourceMasks =
      atoms.map (fun a => a.1) := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          rfl
      | cons y ys =>
          let H0 := coupledHistoryInitial D S old L M x
          let H1 := coupledHistoryStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          change
            (coupledHistoryBuildTail D S old L M x y H1
              hp hc ys hsep).named.sourceMasks =
              (x :: y :: ys).map (fun a => a.1)
          rw [coupledHistoryBuildTail_sources
            D S old L M x y H1 hp hc ys hsep]
          have hfirst : H1.named.sourceMasks = [x.1, y.1] := rfl
          rw [hfirst]
          simp only [List.map_cons, List.cons_append,
            List.singleton_append, List.nil_append]

/-- The *same actual coupled realization* carries one true
historical boundary for each consecutive pair of original
Cayley blocks, in precisely the same order. -/
theorem coupledHistoryBuildNonempty_boundaryPairs
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coupledHistoryBuildNonempty D S old L M atoms hne hsep).
        boundary.boundaries.map (fun T => (T.leftMask, T.rightMask)) =
      adjacentMaskPairs S
        (coupledHistoryBuildNonempty D S old L M atoms hne hsep).
          named.sourceMasks := by
  calc
    (coupledHistoryBuildNonempty D S old L M atoms hne hsep).
        boundary.boundaries.map (fun T => (T.leftMask, T.rightMask)) =
      (boundaryHistoryBuildNonempty D S old L M atoms hne hsep).
        boundaries.map (fun T => (T.leftMask, T.rightMask)) := by
          rw [coupledHistoryBuildNonempty_boundary_eq D S old L M
            atoms hne hsep]
    _ = consecutiveSourceMaskPairs S old atoms :=
      boundaryHistoryBuildNonempty_sourcePairs D S old L M atoms hne hsep
    _ = adjacentMaskPairs S
          (coupledHistoryBuildNonempty D S old L M atoms hne hsep).
            named.sourceMasks := by
      rw [coupledHistoryBuildNonempty_sourceMasks D S old L M
        atoms hne hsep]
      exact (adjacentMaskPairs_atoms S old atoms).symm

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
