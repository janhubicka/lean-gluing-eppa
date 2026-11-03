import GluingEPPA.Steiner.ChainValuation.ModelCoverAction

/-!
# Regular smaller-mask Cayley pieces cover their whole restricted component

The geometric part of the chain restriction becomes simpler when one of the
restricted block alphabets equals the full smaller mask M. The image of that
regular K_M coset is invariant under all M-letters and is M-connected.
Consequently it already covers the whole M-component of any of its points.

The equivariance of the actual block embedding is a hypothesis here; the
existing ChainState.old_edge_survives_perm / last_active lemmas must supply it.
This module does not construct the full chain-restriction cover for components
containing only proper restricted alphabets.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u v w z
variable {E : Type u} {X : Type v} {I : Type w} {Y : I → Type z}
variable {S : Finset E}
variable (τ : E → Equiv.Perm X)
variable (σ : ∀ i : I, E → Equiv.Perm (Y i))
variable (f : ∀ i : I, Y i → X)

/-- Points obtainable from x by allowed words in the actual completed test. -/
def wordReach (x : X) : Set X :=
  {z | ∃ w : List E, (∀ e ∈ w, e ∈ S) ∧ testWordPerm τ w x = z}

/-- A letter-equivariant model has M-invariant image, including closure under
arbitrary allowed word products, not just individual letters. -/
theorem equivariant_image_word_closed
    (hletter : ∀ i e, e ∈ S → ∀ y, f i ((σ i e) y) = τ e (f i y))
    (i : I) (y : Y i) (w : List E) (hw : ∀ e ∈ w, e ∈ S) :
    testWordPerm τ w (f i y) ∈ Set.range (f i) := by
  refine ⟨testWordPerm (σ i) w y, ?_⟩
  exact equivariantCover_word τ σ f hletter i w hw y

/-- If the model is transitive under its M-words, its image is **exactly**
one whole M-reachability class in the target. No injectivity is needed. -/
theorem equivariant_image_eq_wordReach
    (hletter : ∀ i e, e ∈ S → ∀ y, f i ((σ i e) y) = τ e (f i y))
    (i : I)
    (htrans : ∀ a b : Y i, ∃ w : List E,
      (∀ e ∈ w, e ∈ S) ∧ testWordPerm (σ i) w a = b)
    (y : Y i) :
    Set.range (f i) = wordReach τ (S := S) (f i y) := by
  ext z
  constructor
  · rintro ⟨y', rfl⟩
    obtain ⟨w, hw, hv⟩ := htrans y y'
    refine ⟨w, hw, ?_⟩
    calc
      testWordPerm τ w (f i y) =
          f i (testWordPerm (σ i) w y) :=
        (equivariantCover_word τ σ f hletter i w hw y).symm
      _ = f i y' := congrArg (f i) hv
  · rintro ⟨w, hw, hv⟩
    exact ⟨testWordPerm (σ i) w y,
      (equivariantCover_word τ σ f hletter i w hw y).trans hv⟩

/-- A regular Cayley diagram of an already constructed smaller-mask group
is connected under its allowed word transitions. -/
theorem regular_Cayley_word_transitive (A : Data E S)
    (a b : A.Carrier) :
    ∃ w : List E, (∀ e ∈ w, e ∈ S) ∧
      testWordPerm
        (fun e => (regularRightAction A.Carrier).perm (A.edge e))
        w a = b := by
  obtain ⟨w, hw, hv⟩ := A.generated (a⁻¹ * b)
  refine ⟨w, hw, ?_⟩
  rw [testWordPerm_of_rightAction (regularRightAction A.Carrier) A.edge w]
  change a * (w.map A.edge).prod = b
  rw [hv]
  group

/-- The regular coset case of chain restriction requires only an equivariant
map of the earlier group into the restricted chain. Its image is the entire
connected component of any image point. -/
theorem regular_cover_is_component
    (A : Data E S) (f₀ : A.Carrier → X)
    (hletter : ∀ e ∈ S, ∀ a : A.Carrier,
      f₀ (a * A.edge e) = τ e (f₀ a))
    (a : A.Carrier) :
    Set.range f₀ = wordReach τ (S := S) (f₀ a) := by
  let σ₀ : PUnit.{0} → E → Equiv.Perm A.Carrier :=
    fun _ e => (regularRightAction A.Carrier).perm (A.edge e)
  let f₁ : ∀ _ : PUnit.{0}, A.Carrier → X := fun _ => f₀
  have hl : ∀ (i : PUnit.{0}) e, e ∈ S → ∀ y : A.Carrier,
      f₁ i ((σ₀ i e) y) = τ e (f₁ i y) := by
    intro _ e he y
    exact hletter e he y
  exact equivariant_image_eq_wordReach τ σ₀ f₁ hl PUnit.unit
    (fun x y => regular_Cayley_word_transitive A x y) a

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
