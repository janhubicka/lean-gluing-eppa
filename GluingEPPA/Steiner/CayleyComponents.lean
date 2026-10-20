import GluingEPPA.Steiner.CayleyLift

/-!
# Components and their right action in the current manuscript

`Component` is defined from actual walks in the Cayley lift. In particular
it is not an alias for the earlier `Transport.Quot` construction.
The right action is exactly `c(u,g) * h = c(u,h⁻¹*g)` from Section 4.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

universe u v w
variable {V : Type u} {E : Type v} {G : Type w} [Group G]
variable (D : EdgeGraph V E) (M : Set E) (a : E → G)
variable (ha : ∀ e ∈ M, a e * a e = 1)

/-- Connectivity of the actual lift is an equivalence relation. -/
def cayleySetoid : Setoid (V × G) where
  r z z' := D.CayleyWalk M a z.1 z.2 z'.1 z'.2
  iseqv :=
    ⟨fun z => CayleyWalk.nil z.1 z.2,
     fun p => CayleyWalk.symm ha p,
     fun p q => CayleyWalk.trans p q⟩

/-- The set `C_M` of connected components of the literal `M`-lift. -/
def Component := Quotient (D.cayleySetoid M a ha)

instance [Finite V] [Finite G] : Finite (D.Component M a ha) := by
  unfold Component
  infer_instance

/-- The component `c_M(u,g)` of a specified lifted vertex. -/
def component (u : V) (g : G) : D.Component M a ha :=
  Quotient.mk (D.cayleySetoid M a ha) (u,g)

theorem component_eq_iff (u v : V) (g h : G) :
    D.component M a ha u g = D.component M a ha v h ↔
      D.CayleyWalk M a u g v h := by
  constructor
  · intro hp
    exact @Quotient.exact (V × G) (D.cayleySetoid M a ha) (u,g) (v,h) hp
  · intro hp
    exact @Quotient.sound (V × G) (D.cayleySetoid M a ha) (u,g) (v,h) hp

theorem component_eq_iff_value (u v : V) (g h : G) :
    D.component M a ha u g = D.component M a ha v h ↔
      D.WalkValue M a u v (g⁻¹ * h) := by
  rw [D.component_eq_iff, D.cayleyWalk_iff_value]

/-- The deck transformation induced by left multiplication. -/
def componentTranslation (k : G) : D.Component M a ha → D.Component M a ha :=
  Quotient.map (fun z : V × G => (z.1, k * z.2)) (by
    intro z z' p
    exact (D.cayleyWalk_left_mul M a k z.1 z'.1 z.2 z'.2).2 p)

@[simp] theorem componentTranslation_apply (k : G) (u : V) (g : G) :
    D.componentTranslation M a ha k (D.component M a ha u g) =
      D.component M a ha u (k * g) := rfl

@[simp] theorem componentTranslation_one (c : D.Component M a ha) :
    D.componentTranslation M a ha 1 c = c := by
  refine Quotient.inductionOn c ?_
  rintro ⟨u,g⟩
  change D.component M a ha u (1 * g) = D.component M a ha u g
  rw [one_mul]

theorem componentTranslation_mul (k l : G) (c : D.Component M a ha) :
    D.componentTranslation M a ha k (D.componentTranslation M a ha l c) =
      D.componentTranslation M a ha (k * l) c := by
  refine Quotient.inductionOn c ?_
  rintro ⟨u,g⟩
  change D.component M a ha u (k * (l * g)) =
    D.component M a ha u ((k * l) * g)
  rw [mul_assoc]

/-- The deck transformation as a permutation, with its explicit inverse. -/
def componentTranslationEquiv (k : G) :
    D.Component M a ha ≃ D.Component M a ha where
  toFun := D.componentTranslation M a ha k
  invFun := D.componentTranslation M a ha k⁻¹
  left_inv c := by
    rw [D.componentTranslation_mul, inv_mul_cancel, D.componentTranslation_one]
  right_inv c := by
    rw [D.componentTranslation_mul, mul_inv_cancel, D.componentTranslation_one]

/-- Inverse left translation gives the manuscript's right action. -/
def componentRightAction (c : D.Component M a ha) (h : G) :
    D.Component M a ha := D.componentTranslation M a ha h⁻¹ c

@[simp] theorem componentRightAction_apply (u : V) (g h : G) :
    D.componentRightAction M a ha (D.component M a ha u g) h =
      D.component M a ha u (h⁻¹ * g) := rfl

theorem componentRightAction_one (c : D.Component M a ha) :
    D.componentRightAction M a ha c 1 = c := by
  simp [componentRightAction]

theorem componentRightAction_mul (c : D.Component M a ha) (h k : G) :
    D.componentRightAction M a ha (D.componentRightAction M a ha c h) k =
      D.componentRightAction M a ha c (h * k) := by
  unfold componentRightAction
  rw [D.componentTranslation_mul, mul_inv_rev]

/-- The exact hypothesis supplied by earlier-stage property (II) with the empty set. -/
theorem distinguished_injective
    (hunit : ∀ u v, D.WalkValue M a u v 1 → u = v) :
    Function.Injective (fun u => D.component M a ha u 1) := by
  intro u v huv
  apply hunit u v
  simpa using (D.component_eq_iff_value M a ha u v 1 1).1 huv

end EdgeGraph
end GluingEPPA.Steiner
