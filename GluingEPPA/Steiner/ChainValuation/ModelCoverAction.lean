import GluingEPPA.Steiner.ChainValuation.EquivariantCover

/-!
# Word equality on a covered test from earlier group actions

A regular Cayley diagram and every previously recorded chain test have right
actions of the earlier group. Such a model automatically respects all word
equalities. A jointly surjective family of letter-equivariant maps from these
models therefore induces the required action on the new test.

This removes an unnecessary bijectivity obligation from the action-transfer
part of the chain-restriction proof. The geometry must still construct the
equivariant cover; this file assumes no chain-component classification.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u v w z
variable {E : Type u} {G : Type v} {X : Type w}
variable {I : Type z} {Y : I → Type w}
variable [Group G]

/-- The manuscript's left-to-right test word agrees exactly with the
permutation associated with the product in any right group action. -/
theorem testWordPerm_of_rightAction
    (R : RightAction G X) (a : E → G) (w : List E) :
    testWordPerm (fun e => R.perm (a e)) w =
      R.perm ((w.map a).prod) := by
  induction w with
  | nil =>
      ext x
      change x = R.act x 1
      exact (R.one x).symm
  | cons e w ih =>
      ext x
      change testWordPerm (fun e => R.perm (a e)) w (R.act x (a e)) =
        R.act x (a e * (w.map a).prod)
      rw [ih]
      exact R.mul x (a e) (w.map a).prod

/-- No restriction on word length is required: equality in the acting group
already gives equality of the entire permutation on its model. -/
theorem rightAction_model_word_kernel
    (R : RightAction G X) (a : E → G)
    (p q : List E)
    (h : (p.map a).prod = (q.map a).prod) :
    testWordPerm (fun e => R.perm (a e)) p =
      testWordPerm (fun e => R.perm (a e)) q := by
  rw [testWordPerm_of_rightAction R a p,
      testWordPerm_of_rightAction R a q, h]

/-- Multiplication gives the regular Cayley diagram the required right action. -/
def regularRightAction (G : Type v) [Group G] : RightAction G G where
  act := fun x g => x * g
  one := mul_one
  mul := by
    intro x g h
    exact mul_assoc x g h

theorem regularRightAction_letter (a : E → G) (e : E) (g : G) :
    (regularRightAction G).perm (a e) g = g * a e := rfl

variable {S : Finset E} (A : Data E S)
variable (τ : E → Equiv.Perm X)
variable (R : ∀ i : I, RightAction A.Carrier (Y i))
variable (f : ∀ i : I, Y i → X)

/-- A jointly surjective family of equivariant models induces the earlier
group action on the entire new test, not only on chosen representatives. -/
noncomputable def rightAction_of_modelCover
    (hcover : ∀ x : X, ∃ i : I, ∃ y : Y i, f i y = x)
    (hletter : ∀ i e, e ∈ S → ∀ y,
      f i ((R i).perm (A.edge e) y) = τ e (f i y)) :
    RightAction A.Carrier X :=
  rightAction_of_equivariantCover τ
    (fun i e => (R i).perm (A.edge e)) f A hcover hletter
    (fun i p q _ _ h => rightAction_model_word_kernel (R i) A.edge p q h)

/-- Its named generators act by the original chain's completed letter
permutations; no additional action is chosen. -/
theorem rightAction_of_modelCover_edge
    (hcover : ∀ x : X, ∃ i : I, ∃ y : Y i, f i y = x)
    (hletter : ∀ i e, e ∈ S → ∀ y,
      f i ((R i).perm (A.edge e) y) = τ e (f i y))
    (e : E) (he : e ∈ S) (x : X) :
    (rightAction_of_modelCover A τ R f hcover hletter).act
        x (A.edge e) = τ e x :=
  rightAction_of_equivariantCover_edge τ
    (fun i e => (R i).perm (A.edge e)) f A hcover hletter
    (fun i p q _ _ h => rightAction_model_word_kernel (R i) A.edge p q h)
    e he x

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
