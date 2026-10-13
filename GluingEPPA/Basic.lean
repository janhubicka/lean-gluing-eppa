import Mathlib

/-! Transport follows the orientation of an edge: (a,x) goes to (b,y).
A realization therefore satisfies rho b y = rho a x. -/
namespace GluingEPPA
universe u v w
variable {V : Type u} {A : Type v}

structure System (V : Type u) (A : Type v) where
  step : (V × A) → (V × A) → Prop
  reverse : ∀ {p q}, step p q → step q p

namespace System
variable (D : System V A)
abbrev Connected (p q : V × A) : Prop := Relation.ReflTransGen D.step p q

theorem connected_symm {p q : V × A} (h : D.Connected p q) : D.Connected q p := by
  induction h with
  | refl => exact .refl
  | @tail q r h e ih => exact (Relation.ReflTransGen.single (D.reverse e)).trans ih

def setoid : Setoid (V × A) where
  r := D.Connected
  iseqv := ⟨fun _ => .refl, D.connected_symm, fun h k => h.trans k⟩
abbrev Realization := Quotient D.setoid

def copy (a : V) (x : A) : D.Realization := Quotient.mk D.setoid (a, x)

theorem copy_eq_iff {a b : V} {x y : A} :
    D.copy a x = D.copy b y ↔ D.Connected (a, x) (b, y) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem copy_eq_of_step {a b : V} {x y : A} (h : D.step (a, x) (b, y)) :
    D.copy a x = D.copy b y := Quotient.sound (.single h)

structure Frame (U : Type w) where
  value : V → A → U
  injective : ∀ a, Function.Injective (value a)
  commute : ∀ {a b x y}, D.step (a, x) (b, y) → value a x = value b y

namespace Frame
variable {D} {U : Type w} (F : D.Frame U)

theorem path_value {p q : V × A} (h : D.Connected p q) :
    F.value p.1 p.2 = F.value q.1 q.2 := by
  induction h with
  | refl => rfl
  | tail _ e ih => exact ih.trans (F.commute e)

include F

theorem path_unique {a b : V} {x y z : A}
    (h : D.Connected (a, x) (b, y)) (k : D.Connected (a, x) (b, z)) : y = z :=
  F.injective b ((F.path_value h).symm.trans (F.path_value k))

theorem copy_injective (a : V) : Function.Injective (D.copy a) := by
  intro x y h
  exact F.injective a (F.path_value (Quotient.exact h))
end Frame
end System
end GluingEPPA
