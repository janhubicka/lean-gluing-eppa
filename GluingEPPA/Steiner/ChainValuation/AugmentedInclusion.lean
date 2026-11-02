import GluingEPPA.Steiner.ChainValuation.AugmentedRecord
import GluingEPPA.Steiner.RecordInclusion

/-!
# Inclusion into an augmented recursive record

Extra test coordinates only need a compatible right action of the earlier
group.  Once that is supplied, the original direct-record inclusion extends
to the augmented image group.  Endpoint repair then follows by forgetting the
extra coordinates and invoking the already verified direct-record theorem.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace AugmentedRecord

attribute [local instance] Classical.propDecidable

universe u v w z q
variable {V : Type u} {E : Type v} {I : Type z} {J : Type q}
variable (D : EdgeGraph V E) (T : I → Set E) (K : I → Type w)
variable [∀ i, Group (K i)]
variable (a : ∀ i, E → K i) (ha : ∀ i e, e ∈ T i → a i e * a i e = 1)
variable (X : J → Type q) (τ : ∀ j, E → Equiv.Perm (X j))
variable (hτ : ∀ j e, τ j e * τ j e = 1)

variable (k : I)
variable (F : K k →* DirectRecord.Product D T K a ha)
variable (A : ∀ j, RightAction (K k) (X j))

/-- Append the test actions to the old coordinate homomorphism. -/
def coordinateHom : K k →* Product D T K a ha X where
  toFun g := (F g, fun j => MulOpposite.op ((A j).perm g))
  map_one' := by
    apply Prod.ext
    · exact map_one F
    · funext j
      apply MulOpposite.unop_injective
      ext x
      exact (A j).one x
  map_mul' g h := by
    apply Prod.ext
    · exact map_mul F g h
    · funext j
      apply MulOpposite.unop_injective
      ext x
      exact ((A j).mul x g h).symm

theorem coordinateHom_generator
    (hF : ∀ e ∈ T k, F (a k e) = DirectRecord.letter D T K a ha e)
    (hA : ∀ j e, e ∈ T k → ∀ x,
      (A j).act x (a k e) = τ j e x)
    (e : E) (he : e ∈ T k) :
    coordinateHom D T K a ha X τ k F A (a k e) =
      letter D T K a ha X τ e := by
  apply Prod.ext
  · exact hF e he
  · funext j
    apply MulOpposite.unop_injective
    ext x
    exact hA j e he x

theorem map_word
    (hF : ∀ e ∈ T k, F (a k e) = DirectRecord.letter D T K a ha e)
    (hA : ∀ j e, e ∈ T k → ∀ x,
      (A j).act x (a k e) = τ j e x)
    (w : List E) (hw : ∀ e ∈ w, e ∈ T k) :
    coordinateHom D T K a ha X τ k F A ((w.map (a k)).prod) =
      value D T K a ha X τ w := by
  induction w with
  | nil => simp only [List.map_nil, List.prod_nil, map_one, value_nil]
  | cons e w ih =>
      have he := hw e (by simp)
      have hw' : ∀ f ∈ w, f ∈ T k := fun f hf => hw f (by simp [hf])
      simp only [List.map_cons, List.prod_cons, map_mul, value_cons]
      rw [coordinateHom_generator D T K a ha X τ k F A hF hA e he,
        ih hw']

variable (S : Set E) (hTS : T k ⊆ S)
variable (hgen : ∀ g : K k, ∃ w : List E,
  (∀ e ∈ w, e ∈ T k) ∧ (w.map (a k)).prod = g)
variable (hF : ∀ e ∈ T k, F (a k e) = DirectRecord.letter D T K a ha e)
variable (hA : ∀ j e, e ∈ T k → ∀ x,
  (A j).act x (a k e) = τ j e x)

/-- The earlier group embeds into the augmented image whenever its generator
actions agree on every added test. -/
noncomputable def inclusion : K k →* imageGroup D T K a ha X τ hτ S where
  toFun g := ⟨coordinateHom D T K a ha X τ k F A g, by
    obtain ⟨w, hw, hv⟩ := hgen g
    refine ⟨w, fun e he => hTS (hw e he), ?_⟩
    simpa only [hv] using
      (map_word D T K a ha X τ k F A hF hA w hw).symm⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

theorem inclusion_word (w : List E) (hw : ∀ e ∈ w, e ∈ T k) :
    inclusion D T K a ha X τ hτ k F A S hTS hgen hF hA
        ((w.map (a k)).prod) =
      valuation D T K a ha X τ hτ S w (fun e he => hTS (hw e he)) := by
  apply Subtype.ext
  exact map_word D T K a ha X τ k F A hF hA w hw

theorem inclusion_injective (hFinj : Function.Injective F) :
    Function.Injective
      (inclusion D T K a ha X τ hτ k F A S hTS hgen hF hA) := by
  intro g h heq
  apply hFinj
  exact congrArg (fun z => z.val.1) heq

/-- Forgetting added tests recovers the old inclusion with the same first
coordinate. -/
theorem forget_inclusion (g : K k) :
    forget D T K a ha X τ hτ S
        (inclusion D T K a ha X τ hτ k F A S hTS hgen hF hA g) =
      DirectRecord.inclusion D T K a ha k F hF S hTS hgen g := by
  apply Subtype.ext
  rfl

/-- Endpoint repair is inherited from the old record coordinate.  The extra
tests affect equality only by making it finer. -/
theorem inclusion_replacement {u v : V} (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (p : D.WordWalk S u w v) (g : K k)
    (hval : valuation D T K a ha X τ hτ S w hw =
      inclusion D T K a ha X τ hτ k F A S hTS hgen hF hA g) :
    D.WalkValue (T k) (a k) u v g := by
  have hold :
      DirectRecord.valuation D T K a ha S w hw =
        DirectRecord.inclusion D T K a ha k F hF S hTS hgen g := by
    apply Subtype.ext
    exact congrArg (fun z => z.val.1) hval
  exact DirectRecord.inclusion_replacement D T K a ha k F hF S hTS hgen
    w hw p g hold

end AugmentedRecord
end EdgeGraph
end GluingEPPA.Steiner
