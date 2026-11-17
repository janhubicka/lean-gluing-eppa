import GluingEPPA.Steiner.ChainValuation.CombinedHistoricalExactCharts
import GluingEPPA.Steiner.ChainValuation.LinkHistoryIntervalStep
import GluingEPPA.Steiner.ChainValuation.NamedHistoryFinite

/-!
# Consecutive support on the original source-NAMED finite history

The already verified historical interval theorem says that each
M-component meets a consecutive interval of the entire finite list
of Cayley blocks. However, its history record does not remember the
original source mask A of each K_A, whereas the exact boundary
charts do remember those masks.

This module carries the all-components-consecutive and last-chart
certificates through the *source-named* LinkChain recursion. We
identify the enriched record with the standalone named history,
whose source masks and genuine Cayley embeddings agree literally
with the original LinkChain.buildNonempty quotient.

The resulting named component support is consecutive in the same
order as the original atoms, including repeated source masks.
Together with the globally aligned historical boundary records,
this supplies the common geometric state for selecting the
proper-mask active interval.
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

open GluingEPPA.Steiner.ChainValuation

/-- One genuine source-named history retaining the interval support
of EVERY M-component and the last named chart in its correct position. -/
structure NamedIntervalHistory (M : Proper S) where
  data : NamedHistoryBuildResult D S old L M
  consecutive : AllComponentsConsecutive
    (block S old data.data.chain.current.1)
    data.data.chain.state M.val data.data.history
  lastChart : HasLastHistoricalChart
    (block S old data.data.chain.current.1)
    data.data.chain.state M.val data.data.history

/-- The original one-block source-named history satisfies both
invariants, with no arbitrary point-set replacement. -/
noncomputable def namedIntervalInitial
    (M : Proper S) (x : Atom S old) :
    NamedIntervalHistory D S old L M where
  data := namedHistoryInitial D S old L M x
  consecutive := historyInitial_allConsecutive D S old L M x
  lastChart := historyInitial_hasLast D S old L M x

/-- The exact named LinkChain step retains consecutive support of
every actual M-component, including components rooted in the new block. -/
noncomputable def namedIntervalStep
    (M : Proper S) (H : NamedIntervalHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.data.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.data.data.chain.current y) :
    NamedIntervalHistory D S old L M where
  data := namedHistoryStep D S old L M H.data y hsep
  consecutive := historyStep_allConsecutive
    D S old L M H.data.data y hsep H.consecutive H.lastChart
  lastChart := historyStep_hasLast D S old L M H.data.data y hsep

/-- Exactly the original separated-list tail induction, now with
the named component-support interval invariant retained. -/
noncomputable def namedIntervalBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : NamedIntervalHistory D S old L M)
    (hp : H.data.data.chain.previous = some p)
    (hc : H.data.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    NamedIntervalHistory D S old L M := by
  induction rest generalizing p c H with
  | nil => exact H
  | cons z zs ih =>
      have hstep :
          (match H.data.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := namedIntervalStep D S old L M H z hstep
      have hnp : HN.data.data.chain.previous = some c := by
        change some H.data.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- The entire finite nonempty separated chain, using its original
source-named historical Cayley chart list. -/
noncomputable def namedIntervalBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    NamedIntervalHistory D S old L M := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => exact namedIntervalInitial D S old L M x
      | cons y ys =>
          let H0 := namedIntervalInitial D S old L M x
          let H1 := namedIntervalStep D S old L M H0 y trivial
          have hp : H1.data.data.chain.previous = some x := rfl
          have hc : H1.data.data.chain.current = y := rfl
          exact namedIntervalBuildTail D S old L M x y
            H1 hp hc ys hsep

/-- Forgetting the interval certificates from a finite tail
recovers precisely the existing source-named historical builder. -/
theorem namedIntervalBuildTail_data_eq
    (M : Proper S) (p c : Atom S old)
    (H : NamedIntervalHistory D S old L M)
    (hp : H.data.data.chain.previous = some p)
    (hc : H.data.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (namedIntervalBuildTail D S old L M p c H hp hc rest hsep).data =
      namedHistoryBuildTail D S old L M p c H.data hp hc rest hsep := by
  induction rest generalizing p c H with
  | nil => rfl
  | cons z zs ih =>
      have hstep :
          (match H.data.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := namedIntervalStep D S old L M H z hstep
      have hnp : HN.data.data.chain.previous = some c := by
        change some H.data.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.data.chain.current = z := rfl
      change
        (namedIntervalBuildTail D S old L M c z
          HN hnp hnc zs hsep.2).data =
        namedHistoryBuildTail D S old L M c z
          HN.data hnp hnc zs hsep.2
      exact ih c z HN hnp hnc hsep.2

/-- Both finite original source-named constructions give identical
dependent history records, with no additional chart isomorphism. -/
theorem namedIntervalBuildNonempty_data_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (namedIntervalBuildNonempty D S old L M atoms hne hsep).data =
      namedHistoryBuildNonempty D S old L M atoms hne hsep := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          let H0 := namedIntervalInitial D S old L M x
          let H1 := namedIntervalStep D S old L M H0 y trivial
          have hp : H1.data.data.chain.previous = some x := rfl
          have hc : H1.data.data.chain.current = y := rfl
          change
            (namedIntervalBuildTail D S old L M x y
              H1 hp hc ys hsep).data =
            namedHistoryBuildTail D S old L M x y
              H1.data hp hc ys hsep
          exact namedIntervalBuildTail_data_eq
            D S old L M x y H1 hp hc ys hsep

/-- Every M-component meets a consecutive interval of the TRUE
original source-named historical Cayley blocks, not only the
forgotten heterogeneous history. The masks occur exactly in the
input chain's order, including any repeated masks. -/
theorem namedHistoryBuildNonempty_allConsecutive
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := namedHistoryBuildNonempty D S old L M atoms hne hsep
    AllComponentsConsecutive
      (block S old H.data.chain.current.1) H.data.chain.state
      M.val (H.named.map (fun T => T.toHistorical D S old L)) := by
  let H := namedHistoryBuildNonempty D S old L M atoms hne hsep
  let T := namedIntervalBuildNonempty D S old L M atoms hne hsep
  have hEq : T.data = H :=
    namedIntervalBuildNonempty_data_eq
      D S old L M atoms hne hsep
  have hConsecutive : AllComponentsConsecutive
      (block S old H.data.chain.current.1)
      H.data.chain.state M.val H.data.history := by
    rw [← hEq]
    exact T.consecutive
  change AllComponentsConsecutive
    (block S old H.data.chain.current.1)
    H.data.chain.state M.val
    (H.named.map (fun T => T.toHistorical D S old L))
  rw [H.forget]
  exact hConsecutive

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
