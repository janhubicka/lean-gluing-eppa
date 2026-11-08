import GluingEPPA.Steiner.ChainValuation.PushoutReachBridge

/-!
# Saturation and connectivity characterize an entire labelled component

The exact restricted-pushout construction describes the selected union
of the old M-component and one new M-coset. To identify this union
with the *entire* new component, it suffices that the union contains
the chosen basepoint, every selected point is M-reachable from it,
and no genuine M-edge can leave the union.

This lemma isolates that general graph-theoretic step, independently
of groups, pushouts, cosets, generators, or the current valuation stage.
It prevents the unjustified shortcut from surjectivity alone.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {X : Type v}

/-- A nonempty set containing root is exactly the full M-component
of root when it is M-edge saturated and every one of its points is
M-reachable from root. Works for arbitrary symmetric labelled edges. -/
theorem saturated_connected_set_eq_component
    (R : E → X → X → Prop) (M : Finset E) (root : X)
    (W : Set X)
    (hroot : root ∈ W)
    (hsymm : ∀ e x y, R e x y → R e y x)
    (hclosed : ∀ e, e ∈ M →
      ∀ x y, R e x y → x ∈ W → y ∈ W)
    (hconnected : ∀ x, x ∈ W → LabelReach R M root x) :
    W = {x | LabelReach R M root x} := by
  have hpreserve : ∀ {x y : X},
      LabelReach R M x y → (x ∈ W ↔ y ∈ W) := by
    intro x y hxy
    induction hxy with
    | refl x =>
        exact Iff.rfl
    | edge e he hr =>
        constructor
        · exact hclosed e he _ _ hr
        · exact hclosed e he _ _ (hsymm e _ _ hr)
    | symm h ih =>
        exact ih.symm
    | trans h k ih ik =>
        exact ih.trans ik
  ext x
  constructor
  · intro hx
    exact hconnected x hx
  · intro hreach
    exact (hpreserve hreach).mp hroot

end GluingEPPA.Steiner.ChainValuation
