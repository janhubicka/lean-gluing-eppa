import GluingEPPA.Steiner.ChainValuation.MatchingActionEquiv
import GluingEPPA.Steiner.ChainValuation.PushoutReachBridge

/-!
# Completed letter actions on genuine reachable components

A component for the alphabet M is defined by paths in actual
matching edges. Every e-edge with e in M stays inside that
component, so restricting the genuine matchings yields their
original completed permutations, with the same fixed-point
behaviour.

Consequently an edge-reflecting equivalence from a normalized
component transports the completed *genuine* e-permutations for
every e in M. This is the action-theoretic half of the Part II
chain-restriction induction. The finite-history chart remains
to be constructed separately.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {E : Type u} {X : Type v} {U : Type w}

/-- A genuine M-connected component of a family of partial matchings. -/
abbrev MatchingReachComponent
    (P : E → Matching X) (M : Finset E) (q : X) :=
  {x : X // LabelReach (fun e => (P e).Rel) M q x}

/-- Restrict a letter matching to the actual M-component.
For letters outside M this is only the induced partial matching;
for letters inside M its completed permutation agrees with the
ambient permutation on every vertex of the component. -/
def reachComponentMatching
    (P : E → Matching X) (M : Finset E) (q : X) (e : E) :
    Matching (MatchingReachComponent P M q) where
  Rel x y := (P e).Rel x.val y.val
  symm := by
    intro x y hxy
    exact (P e).symm hxy
  unique := by
    intro x y z hxy hxz
    apply Subtype.ext
    exact (P e).unique hxy hxz

/-- The restriction cannot produce a spurious fixed point for an
M-letter: every genuine successor of a component vertex is still
in the same component, and an unmatched vertex stays unmatched. -/
theorem reachComponentMatching_perm_val
    (P : E → Matching X) (M : Finset E) (q : X)
    (e : E) (he : e ∈ M)
    (x : MatchingReachComponent P M q) :
    ((reachComponentMatching P M q e).perm x).val =
      (P e).perm x.val := by
  by_cases h : ∃ y : X, (P e).Rel x.val y
  · obtain ⟨y, hxy⟩ := h
    have hy : LabelReach (fun e => (P e).Rel) M q y :=
      LabelReach.trans x.property (LabelReach.edge e he hxy)
    let y' : MatchingReachComponent P M q := ⟨y, hy⟩
    have hxy' : (reachComponentMatching P M q e).Rel x y' := hxy
    calc
      ((reachComponentMatching P M q e).perm x).val =
          y'.val :=
        congrArg Subtype.val
          ((reachComponentMatching P M q e).perm_eq_of_rel hxy')
      _ = (P e).perm x.val :=
        ((P e).perm_eq_of_rel hxy).symm
  · have hn : ¬ ∃ y : MatchingReachComponent P M q,
        (reachComponentMatching P M q e).Rel x y := by
      rintro ⟨y, hy⟩
      exact h ⟨y.val, hy⟩
    calc
      ((reachComponentMatching P M q e).perm x).val = x.val :=
        congrArg Subtype.val
          ((reachComponentMatching P M q e).perm_fixed_of_none hn)
      _ = (P e).perm x.val :=
        ((P e).perm_fixed_of_none h).symm

/-- The precise action conclusion of an M-component chart.
Two-way reflection of genuine e-edges for e in M forces the
normalized completed action to agree with the original ambient
one, even at vertices fixed by the completion. -/
theorem componentChart_perm_val_of_edge_iff
    (P : E → Matching X) (M : Finset E) (q : X)
    (Q : E → Matching U)
    (F : U ≃ MatchingReachComponent P M q)
    (hRel : ∀ e ∈ M, ∀ x y : U,
      (Q e).Rel x y ↔ (P e).Rel (F x).val (F y).val)
    (e : E) (he : e ∈ M) (x : U) :
    (F ((Q e).perm x)).val = (P e).perm (F x).val := by
  have hchart : F ((Q e).perm x) =
      (reachComponentMatching P M q e).perm (F x) :=
    matching_perm_conjugate_of_rel_iff F (Q e)
      (reachComponentMatching P M q e)
      (fun a b => hRel e he a b) x
  exact (congrArg Subtype.val hchart).trans
    (reachComponentMatching_perm_val P M q e he (F x))

end GluingEPPA.Steiner.ChainValuation
