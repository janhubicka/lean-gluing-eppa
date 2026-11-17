import GluingEPPA.Steiner.ChainValuation.ChainRestrictionNormalForm
import GluingEPPA.Steiner.ChainValuation.CoverRightAction

/-!
# Earlier-group actions on actual chain tests

An augmented record acts on each of its literal test coordinates by
projection. The component normal form then covers every larger chain
test by copies of the earlier Cayley action and earlier recorded chain
tests. This transfers word relations and supplies the extra actions
required by `AugmentedStep.link`.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord

namespace ChainValuation

universe u v
variable {E : Type u} {X : Type v} {S : Finset E}

/-- A compatible right action reads the same left-to-right test word. -/
theorem testWordPerm_eq_action
    (A : Data E S) (τ : E → Equiv.Perm X)
    (B : RightAction A.Carrier X)
    (hB : ∀ e ∈ S, ∀ x, B.act x (A.edge e) = τ e x)
    (word : List E) (hword : ∀ e ∈ word, e ∈ S) (x : X) :
    testWordPerm τ word x = B.act x ((word.map A.edge).prod) := by
  induction word generalizing x with
  | nil => exact (B.one x).symm
  | cons e rest ih =>
      have he := hword e (by simp)
      have hr : ∀ a ∈ rest, a ∈ S := fun a ha => hword a (by simp [ha])
      change testWordPerm τ rest (τ e x) =
        B.act x (A.edge e * (rest.map A.edge).prod)
      rw [ih hr, ← hB e he x, B.mul]

/-- Equality in the acting group forces equality of its completed test words. -/
theorem testWordPerm_eq_of_action
    (A : Data E S) (τ : E → Equiv.Perm X)
    (B : RightAction A.Carrier X)
    (hB : ∀ e ∈ S, ∀ x, B.act x (A.edge e) = τ e x)
    (p q : List E) (hp : ∀ e ∈ p, e ∈ S) (hq : ∀ e ∈ q, e ∈ S)
    (heq : (p.map A.edge).prod = (q.map A.edge).prod) :
    testWordPerm τ p = testWordPerm τ q := by
  ext x
  rw [testWordPerm_eq_action A τ B hB p hp,
    testWordPerm_eq_action A τ B hB q hq, heq]

end ChainValuation

namespace AugmentedStep

attribute [local instance] Classical.propDecidable

universe u
variable {V E J : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (X : J → Type u) [Finite J] [∀ j, Finite (X j)]
variable (τ : ∀ j, E → Equiv.Perm (X j))
variable (hτ : ∀ j e, τ j e * τ j e = 1)

/-- The actual appended permutation coordinate, with no kernel assumption. -/
noncomputable def recordedTestAction (j : J) :
    RightAction (data D S old X τ hτ).Carrier (X j) where
  act x g := MulOpposite.unop (g.val.2 j) x
  one _ := rfl
  mul _ _ _ := rfl

/-- The coordinate projection has exactly the recorded named generators. -/
theorem recordedTestAction_edge (j : J) (e : E) (he : e ∈ S) (x : X j) :
    (recordedTestAction D S old X τ hτ j).act x
      ((data D S old X τ hτ).edge e) = τ j e x := by
  change MulOpposite.unop
    ((AugmentedRecord.totalGenerator D
      (Step.sets S) (Step.groups S old) (Step.edges S old)
      (Step.involutions S old) X τ hτ (S : Set E) e).val.2 j) x = _
  rw [AugmentedRecord.totalGenerator_mem D
    (Step.sets S) (Step.groups S old) (Step.edges S old)
    (Step.involutions S old) X τ hτ (S : Set E) e he]
  rfl

/-- Word-kernel compatibility is a consequence of the literal record coordinate. -/
theorem recordedTest_kernel (j : J) (p q : List E)
    (hp : ∀ e ∈ p, e ∈ S) (hq : ∀ e ∈ q, e ∈ S)
    (heq : (p.map (data D S old X τ hτ).edge).prod =
      (q.map (data D S old X τ hτ).edge).prod) :
    ChainValuation.testWordPerm (τ j) p = ChainValuation.testWordPerm (τ j) q :=
  ChainValuation.testWordPerm_eq_of_action (data D S old X τ hτ) (τ j)
    (recordedTestAction D S old X τ hτ j)
    (recordedTestAction_edge D S old X τ hτ j) p q hp hq heq

end AugmentedStep

namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (N : Nat) (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))
variable (M : Proper S)

open GluingEPPA.Steiner.ChainValuation
open GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation

/-- The full Cayley model, or one of the actual bounded smaller tests. -/
abbrev RestrictionSource :=
  Option (SeparatedChains D N M.val (smallerOld S old M) (smallerLinks D S old L M))

noncomputable def restrictionSourceSpace (i : RestrictionSource D N S old L M) : Type u :=
  match i with
  | none => (old M).Carrier
  | some d => chainSpace D N M.val (smallerOld S old M) (smallerLinks D S old L M) d

noncomputable def restrictionSourcePerm (i : RestrictionSource D N S old L M)
    (e : E) : Equiv.Perm (restrictionSourceSpace D N S old L M i) :=
  match i with
  | none => ((block S old M).matching e).perm
  | some d => chainPerm D N M.val (smallerOld S old M) (smallerLinks D S old L M) d e

/-- The geometric classification supplies a genuine equivariant cover at
each target point; no action or kernel assumption enters this statement. -/
theorem chainTest_equivariant_cover (c : SeparatedChains D N S old L)
    (x : chainSpace D N S old L c) :
    ∃ i : RestrictionSource D N S old L M,
      ∃ f : restrictionSourceSpace D N S old L M i → chainSpace D N S old L c,
        (∃ y, f y = x) ∧
        ∀ e ∈ M.val, ∀ y,
          f (restrictionSourcePerm D N S old L M i e y) =
            chainPerm D N S old L c e (f y) := by
  rcases chain_restriction_completed_actions D S old L N M c x with
    ⟨F, hF⟩ | ⟨d, _hd, F, hF⟩
  · refine ⟨none, (fun y => (F y).val), ?_, ?_⟩
    · refine ⟨F.symm ⟨x, LabelReach.refl x⟩, ?_⟩
      exact congrArg Subtype.val (F.apply_symm_apply ⟨x, LabelReach.refl x⟩)
    · exact hF
  · refine ⟨some d, (fun y => (F y).val), ?_, ?_⟩
    · refine ⟨F.symm ⟨x, LabelReach.refl x⟩, ?_⟩
      exact congrArg Subtype.val (F.apply_symm_apply ⟨x, LabelReach.refl x⟩)
    · exact hF

variable
  (smallActions : ∀ d : SeparatedChains D N M.val
    (smallerOld S old M) (smallerLinks D S old L M),
    RightAction (old M).Carrier
      (chainSpace D N M.val (smallerOld S old M) (smallerLinks D S old L M) d))
  (hsmall : ∀ d e, e ∈ M.val → ∀ x,
    (smallActions d).act x ((old M).edge e) =
      chainPerm D N M.val (smallerOld S old M) (smallerLinks D S old L M) d e x)

/-- The full model uses ordinary right multiplication. The proper models
use only the already recorded actions on tests at M itself. -/
noncomputable def restrictionSourceAction (i : RestrictionSource D N S old L M) :
    RightAction (old M).Carrier (restrictionSourceSpace D N S old L M i) :=
  match i with
  | none =>
      show RightAction (old M).Carrier (old M).Carrier from
      { act := fun x g => x * g
        one := mul_one
        mul := mul_assoc }
  | some d => smallActions d

include hsmall

theorem restrictionSourceAction_edge (i : RestrictionSource D N S old L M)
    (e : E) (he : e ∈ M.val) (x : restrictionSourceSpace D N S old L M i) :
    (restrictionSourceAction D N S old L M smallActions i).act x ((old M).edge e) =
      restrictionSourcePerm D N S old L M i e x := by
  cases i with
  | none => exact ((block S old M).matching_perm he x).symm
  | some d => exact hsmall d e he x

/-- Earlier recorded test relations, together with the full Cayley model,
force every K_M relation on the entire actual S-chain test. -/
theorem chainTest_kernel (c : SeparatedChains D N S old L)
    (p q : List E) (hp : ∀ e ∈ p, e ∈ M.val) (hq : ∀ e ∈ q, e ∈ M.val)
    (heq : (p.map (old M).edge).prod = (q.map (old M).edge).prod) :
    testWordPerm (chainPerm D N S old L c) p =
      testWordPerm (chainPerm D N S old L c) q := by
  let idx : chainSpace D N S old L c → RestrictionSource D N S old L M :=
    fun x => Classical.choose (chainTest_equivariant_cover D N S old L M c x)
  let f : ∀ x : chainSpace D N S old L c,
      restrictionSourceSpace D N S old L M (idx x) → chainSpace D N S old L c :=
    fun x => Classical.choose
      (Classical.choose_spec (chainTest_equivariant_cover D N S old L M c x))
  have hprops (x : chainSpace D N S old L c) :
      (∃ y, f x y = x) ∧
      ∀ e ∈ M.val, ∀ y,
        f x (restrictionSourcePerm D N S old L M (idx x) e y) =
          chainPerm D N S old L c e (f x y) :=
    Classical.choose_spec
      (Classical.choose_spec (chainTest_equivariant_cover D N S old L M c x))
  apply coveredTest_kernel (old M)
    (fun x => restrictionSourceSpace D N S old L M (idx x))
    (fun x => restrictionSourcePerm D N S old L M (idx x))
    (chainPerm D N S old L c) f
    (fun x => by obtain ⟨y, hy⟩ := (hprops x).1; exact ⟨x, y, hy⟩)
    (fun x e he y => (hprops x).2 e he y) ?_ p q hp hq heq
  intro x a b ha hb hab
  exact testWordPerm_eq_of_action (old M)
    (restrictionSourcePerm D N S old L M (idx x))
    (restrictionSourceAction D N S old L M smallActions (idx x))
    (restrictionSourceAction_edge D N S old L M smallActions hsmall (idx x))
    a b ha hb hab

/-- The required old-group action on the actual current-stage chain test. -/
noncomputable def chainTestRightAction (c : SeparatedChains D N S old L) :
    RightAction (old M).Carrier (chainSpace D N S old L c) :=
  wordRightAction (old M) (chainPerm D N S old L c)
    (chainTest_kernel D N S old L M smallActions hsmall c)

/-- This is exactly the generator compatibility required by AugmentedStep.link. -/
theorem chainTestRightAction_edge (c : SeparatedChains D N S old L)
    (e : E) (he : e ∈ M.val) (x : chainSpace D N S old L c) :
    (chainTestRightAction D N S old L M smallActions hsmall c).act x ((old M).edge e) =
      chainPerm D N S old L c e x :=
  wordRightAction_edge (old M) (chainPerm D N S old L c)
    (chainTest_kernel D N S old L M smallActions hsmall c) e he x

theorem chainTestRightAction_word (c : SeparatedChains D N S old L)
    (word : List E) (hword : ∀ e ∈ word, e ∈ M.val)
    (x : chainSpace D N S old L c) :
    (chainTestRightAction D N S old L M smallActions hsmall c).act x
        ((word.map (old M).edge).prod) =
      testWordPerm (chainPerm D N S old L c) word x :=
  wordActionValue_word (old M) (chainPerm D N S old L c)
    (chainTest_kernel D N S old L M smallActions hsmall c) word hword x

end LinkChain

end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
