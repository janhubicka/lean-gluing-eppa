import GluingEPPA.Steiner.ChainValuation.LinkedAlignedBoundaryHistory

/-!
# Every actual finite separated chain has literally linked boundary charts

The one-step linked-history invariant is iterated through precisely
the original one-, two- and many-block LinkChain construction. At
each stage the forgotten aligned history is the previously checked
original-boundary enrichment, not a fresh or reindexed quotient.

In the final actual finite separated Link chain, the right named
Cayley block of boundary i and the left named Cayley block of
boundary i+1 are literally the SAME dependent historical chart.
Thus any two genuine interface witnesses of a fixed M-component
at these boundaries can be compared inside one actual K_A group,
and the unique K_(M∩A) displacement theorem applies.

This result does not itself select all component interface
parameters or build their normalized chain. -/

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

/-- Iteration of the linked named-boundary history through every
remaining genuine separated LinkChain atom. -/
noncomputable def linkedAlignedBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : LinkedAlignedHistory D S old L M)
    (hp : H.data.boundaryHistory.chain.previous = some p)
    (hc : H.data.boundaryHistory.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    LinkedAlignedHistory D S old L M := by
  induction rest generalizing p c H with
  | nil => exact H
  | cons z zs ih =>
      have hstep :
          (match H.data.boundaryHistory.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.boundaryHistory.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := linkedAlignedStep D S old L M H z hstep
      have hnp : HN.data.boundaryHistory.chain.previous = some c := by
        change some H.data.boundaryHistory.chain.current = some c
        rw [hc]
      have hnc : HN.data.boundaryHistory.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- The entire original nonempty separated LinkChain receives
the literal linked historical boundary list. -/
noncomputable def linkedAlignedBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    LinkedAlignedHistory D S old L M := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => exact linkedAlignedInitial D S old L M x
      | cons y ys =>
          let H0 := linkedAlignedInitial D S old L M x
          let H1 := linkedAlignedStep D S old L M H0 y trivial
          have hp : H1.data.boundaryHistory.chain.previous = some x := rfl
          have hc : H1.data.boundaryHistory.chain.current = y := rfl
          exact linkedAlignedBuildTail D S old L M x y H1 hp hc ys hsep

/-- Forgetting the literal adjacency certificates from the
enriched tail gives exactly the prior aligned boundary-history
recursor on the same original dependent quotient state. -/
theorem linkedAlignedBuildTail_data_eq
    (M : Proper S) (p c : Atom S old)
    (H : LinkedAlignedHistory D S old L M)
    (hp : H.data.boundaryHistory.chain.previous = some p)
    (hc : H.data.boundaryHistory.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (linkedAlignedBuildTail D S old L M p c H hp hc rest hsep).data =
      alignedNamedBuildTail D S old L M p c
        H.data hp hc rest hsep := by
  induction rest generalizing p c H with
  | nil => rfl
  | cons z zs ih =>
      have hstep :
          (match H.data.boundaryHistory.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.boundaryHistory.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := linkedAlignedStep D S old L M H z hstep
      have hnp : HN.data.boundaryHistory.chain.previous = some c := by
        change some H.data.boundaryHistory.chain.current = some c
        rw [hc]
      have hnc : HN.data.boundaryHistory.chain.current = z := rfl
      change
        (linkedAlignedBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).data =
        alignedNamedBuildTail D S old L M c z
          HN.data hnp hnc zs hsep.2
      exact ih c z HN hnp hnc hsep.2

/-- The fully linked history forgets to the SAME original aligned
named-boundary history, including all source masks and actual
historical Cayley embeddings. -/
theorem linkedAlignedBuildNonempty_data_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (linkedAlignedBuildNonempty D S old L M atoms hne hsep).data =
      alignedNamedBuildNonempty D S old L M atoms hne hsep := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          let H0 := linkedAlignedInitial D S old L M x
          let H1 := linkedAlignedStep D S old L M H0 y trivial
          have hp : H1.data.boundaryHistory.chain.previous = some x := rfl
          have hc : H1.data.boundaryHistory.chain.current = y := rfl
          change
            (linkedAlignedBuildTail D S old L M x y H1
              hp hc ys hsep).data =
            alignedNamedBuildTail D S old L M x y
              H1.data hp hc ys hsep
          exact linkedAlignedBuildTail_data_eq D S old L M
            x y H1 hp hc ys hsep

/-- In the literal original finite chain, every two consecutive
historical boundaries share the *identical* named middle Cayley
chart. This is the missing global input to the unique interior
displacement lemma for arbitrary chosen active components. -/
theorem buildNonempty_has_linked_named_boundaries
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    ∃ H : AlignedNamedHistory D S old L M,
      (⟨H.boundaryHistory.chain.current,
         H.boundaryHistory.chain.state⟩ : SomeState S old) =
        buildNonempty D S old L atoms hne hsep ∧
      AlignedBoundaryList.Linked D S old L H.aligned := by
  let H := linkedAlignedBuildNonempty D S old L M atoms hne hsep
  refine ⟨H.data, ?_, H.linked⟩
  rw [linkedAlignedBuildNonempty_data_eq
    D S old L M atoms hne hsep]
  exact alignedNamedBuildNonempty_original
    D S old L M atoms hne hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
