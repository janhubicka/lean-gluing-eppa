import GluingEPPA.Steiner.ChainValuation.RegularComponentCover

/-!
# Actual restricted word components of a chain test

The geometric component relation induced by the completed involutive letter
permutations is exactly reachability under allowed words. This module gives
that relation its own Setoid, suitable for instantiating the generic
matching-gluing connectivity theorem of the independent PR #81.

Unlike a quotient defined using an arbitrary generated relation, the
component relation retains an explicit actual word witnessing each link.
No small-mask kernel equality is assumed.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u v
variable {E : Type u} {X : Type v} {S : Finset E}
variable (τ : E → Equiv.Perm X)

/-- Reversing a word of involutive letters reverses its action. -/
theorem testWordPerm_reverse_cancel
    (hinv : ∀ e ∈ S, Function.Involutive (τ e))
    (w : List E) (hw : ∀ e ∈ w, e ∈ S) (x : X) :
    testWordPerm τ w.reverse (testWordPerm τ w x) = x := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
      have he : e ∈ S := hw e (by simp)
      have htail : ∀ a ∈ w, a ∈ S :=
        fun a ha => hw a (by simp [ha])
      have hrest := ih htail (τ e x)
      calc
        testWordPerm τ (e :: w).reverse
            (testWordPerm τ (e :: w) x) =
          testWordPerm τ [e]
            (testWordPerm τ w.reverse (testWordPerm τ w (τ e x))) := by
              rw [List.reverse_cons, testWordPerm_append]
              rfl
        _ = testWordPerm τ [e] (τ e x) := by rw [hrest]
        _ = x := hinv e he x

/-- Witnessed word connectivity, with no dependence on a group action. -/
def wordConnected (x y : X) : Prop :=
  y ∈ wordReach τ (S := S) x

theorem wordConnected_refl (x : X) : wordConnected τ (S := S) x x := by
  exact ⟨[], by simp, rfl⟩

theorem wordConnected_symm
    (hinv : ∀ e ∈ S, Function.Involutive (τ e))
    {x y : X} (hxy : wordConnected τ (S := S) x y) :
    wordConnected τ (S := S) y x := by
  obtain ⟨w, hw, hwxy⟩ := hxy
  refine ⟨w.reverse, ?_, ?_⟩
  · intro e he
    exact hw e (by simpa using he)
  · calc
      testWordPerm τ w.reverse y =
          testWordPerm τ w.reverse (testWordPerm τ w x) := by rw [hwxy]
      _ = x := testWordPerm_reverse_cancel τ hinv w hw x

theorem wordConnected_trans
    {x y z : X}
    (hxy : wordConnected τ (S := S) x y)
    (hyz : wordConnected τ (S := S) y z) :
    wordConnected τ (S := S) x z := by
  obtain ⟨u, hu, hxy⟩ := hxy
  obtain ⟨v, hv, hyz⟩ := hyz
  refine ⟨u ++ v, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hu e he
    · exact hv e he
  · calc
      testWordPerm τ (u ++ v) x =
          testWordPerm τ v (testWordPerm τ u x) :=
        testWordPerm_append τ u v x
      _ = testWordPerm τ v y := by rw [hxy]
      _ = z := hyz

/-- The exact M-word component Setoid, built from completed letter
permutations. The assumption is only that each selected letter is
involutive, as proved for every chain test. -/
def wordComponentSetoid
    (hinv : ∀ e ∈ S, Function.Involutive (τ e)) : Setoid X where
  r := wordConnected τ (S := S)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · exact wordConnected_refl τ
    · intro x y hxy
      exact wordConnected_symm τ hinv hxy
    · intro x y z hxy hyz
      exact wordConnected_trans τ hxy hyz

theorem wordComponent_eq_iff
    (hinv : ∀ e ∈ S, Function.Involutive (τ e)) (x y : X) :
    Quotient.mk (wordComponentSetoid τ hinv) x =
        Quotient.mk (wordComponentSetoid τ hinv) y ↔
      wordConnected τ (S := S) x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
