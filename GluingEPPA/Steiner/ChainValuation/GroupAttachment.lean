import GluingEPPA.Steiner.ChainValuation.Pushout

/-!
# One group attachment in a chain

Two adjacent Cayley blocks are glued by a common subgroup. This file proves
that both block embeddings are injective and that every shared named
transition has the same endpoint in the pushout.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {K : Type u} {G : Type v} {H : Type w}
variable [Group K] [Group G] [Group H]

def attachLeft (h : G) (i : K →* G) : K → G :=
  fun k => h * i k

theorem attachLeft_injective (h : G) (i : K →* G)
    (hi : Function.Injective i) :
    Function.Injective (attachLeft h i) := by
  intro k l hkl
  apply hi
  exact mul_left_cancel hkl

/-- A shared generator gives the same next quotient vertex from either block. -/
theorem group_attachment_transition
    (h : G) (i : K →* G) (j : K →* H)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (k e : K) :
    pushoutInl (attachLeft h i) j (attachLeft_injective h i hi) hj
        (h * i k * i e) =
      pushoutInr (attachLeft h i) j (attachLeft_injective h i hi) hj
        (j k * j e) := by
  have ha := pushout_attachment (attachLeft h i) j
    (attachLeft_injective h i hi) hj (k * e)
  convert ha using 1 <;> simp [attachLeft, map_mul, mul_assoc]

/-- The actual overlap of the two embedded blocks is exactly the attached
subgroup, with no additional cross-block identifications. -/
theorem group_attachment_overlap_iff
    (h : G) (i : K →* G) (j : K →* H)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (x : G) (y : H) :
    pushoutInl (attachLeft h i) j (attachLeft_injective h i hi) hj x =
        pushoutInr (attachLeft h i) j (attachLeft_injective h i hi) hj y ↔
      ∃ k, h * i k = x ∧ j k = y :=
  pushoutInl_eq_inr_iff (attachLeft h i) j
    (attachLeft_injective h i hi) hj x y

end GluingEPPA.Steiner.ChainValuation
