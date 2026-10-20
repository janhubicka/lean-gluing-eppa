import Mathlib

/-!
# Two right actions on complementary parts

The elementary gluing step in Lemma 4.1 of the current Steiner manuscript.
An action on X is transported to the image of an injection j : X -> Y;
an action on Y preserving that image is used on its complement. The result
is an action on every point of Y. No word relation is postulated.
-/

namespace GluingEPPA.Steiner

universe u v w z

/-- Right multiplication order, as used for permutations in the manuscript. -/
structure RightAction (G : Type u) [Group G] (X : Type v) where
  act : X → G → X
  one : ∀ x, act x 1 = x
  mul : ∀ x g h, act (act x g) h = act x (g * h)

namespace RightAction

attribute [local instance] Classical.propDecidable

variable {G : Type u} [Group G] {H : Type z} [Group H]
variable {X : Type v} {Y : Type w}

/-- Pull back a right action through a group homomorphism. -/
def comap (A : RightAction H X) (f : G →* H) : RightAction G X where
  act x g := A.act x (f g)
  one x := by simp only [map_one, A.one]
  mul x g h := by simp only [map_mul, A.mul]

/-- Each acting element gives a permutation; inversion gives its inverse. -/
def perm (A : RightAction G X) (g : G) : Equiv.Perm X where
  toFun x := A.act x g
  invFun x := A.act x g⁻¹
  left_inv x := by
    change A.act (A.act x g) g⁻¹ = x
    rw [A.mul, mul_inv_cancel, A.one]
  right_inv x := by
    change A.act (A.act x g⁻¹) g = x
    rw [A.mul, inv_mul_cancel, A.one]

@[simp] theorem perm_apply (A : RightAction G X) (g : G) (x : X) :
    A.perm g x = A.act x g := rfl

/-- The multiplication order is intentionally opposite to Lean's Perm product. -/
theorem perm_mul (A : RightAction G X) (g h : G) :
    A.perm (g * h) = (A.perm g).trans (A.perm h) := by
  ext x
  exact (A.mul x g h).symm

noncomputable def glueAct (A : RightAction G X) (B : RightAction G Y)
    (j : X → Y) (y : Y) (g : G) : Y :=
  if hy : y ∈ Set.range j then j (A.act (Classical.choose hy) g)
  else B.act y g

theorem glueAct_image (A : RightAction G X) (B : RightAction G Y)
    (j : X → Y) (hj : Function.Injective j) (x : X) (g : G) :
    glueAct A B j (j x) g = j (A.act x g) := by
  classical
  have hx : j x ∈ Set.range j := ⟨x, rfl⟩
  rw [glueAct, dif_pos hx]
  rw [hj (Classical.choose_spec hx)]

theorem glueAct_outside (A : RightAction G X) (B : RightAction G Y)
    (j : X → Y) {y : Y} (hy : y ∉ Set.range j) (g : G) :
    glueAct A B j y g = B.act y g := by
  classical
  simp only [glueAct, dif_neg hy]

/-- The two-part action, with invariance of the complement proved by hB. -/
noncomputable def glue (A : RightAction G X) (B : RightAction G Y)
    (j : X → Y) (hj : Function.Injective j)
    (hB : ∀ y g, B.act y g ∈ Set.range j ↔ y ∈ Set.range j) :
    RightAction G Y where
  act := glueAct A B j
  one y := by
    classical
    by_cases hy : y ∈ Set.range j
    · obtain ⟨x, rfl⟩ := hy
      rw [glueAct_image A B j hj, A.one]
    · rw [glueAct_outside A B j hy, B.one]
  mul y g h := by
    classical
    by_cases hy : y ∈ Set.range j
    · obtain ⟨x, rfl⟩ := hy
      rw [glueAct_image A B j hj, glueAct_image A B j hj,
        glueAct_image A B j hj, A.mul]
    · have hy' : B.act y g ∉ Set.range j := fun hz => hy ((hB y g).1 hz)
      rw [glueAct_outside A B j hy, glueAct_outside A B j hy',
        glueAct_outside A B j hy, B.mul]

theorem glue_apply_image (A : RightAction G X) (B : RightAction G Y)
    (j : X → Y) (hj : Function.Injective j)
    (hB : ∀ y g, B.act y g ∈ Set.range j ↔ y ∈ Set.range j)
    (x : X) (g : G) :
    (glue A B j hj hB).act (j x) g = j (A.act x g) :=
  glueAct_image A B j hj x g

theorem glue_apply_outside (A : RightAction G X) (B : RightAction G Y)
    (j : X → Y) (hj : Function.Injective j)
    (hB : ∀ y g, B.act y g ∈ Set.range j ↔ y ∈ Set.range j)
    {y : Y} (hy : y ∉ Set.range j) (g : G) :
    (glue A B j hj hB).act y g = B.act y g :=
  glueAct_outside A B j hy g

end RightAction
end GluingEPPA.Steiner
