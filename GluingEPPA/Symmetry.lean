import GluingEPPA.Relational

namespace GluingEPPA
universe u v w
namespace System
variable {V : Type u} {A : Type v} (D : System V A)

/-- A label-preserving vertex symmetry, expressed on its transport relation. -/
structure Symmetry where
  perm : V ≃ V
  step_iff : ∀ {a b x y},
    D.step (perm a, x) (perm b, y) ↔ D.step (a, x) (b, y)

namespace Symmetry
variable {D} (t : D.Symmetry)
def pair (p : V × A) : V × A := (t.perm p.1, p.2)

theorem map_path {p q : V × A} (h : D.Connected p q) :
    D.Connected (t.pair p) (t.pair q) := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (t.step_iff.mpr e)

def symm : D.Symmetry where
  perm := t.perm.symm
  step_iff := by
    intro a b x y
    have h := t.step_iff (a := t.perm.symm a) (b := t.perm.symm b) (x := x) (y := y)
    simpa using h.symm

def map : D.Realization → D.Realization := Quotient.map t.pair (fun _ _ h => t.map_path h)
@[simp] theorem map_copy (a : V) (x : A) : t.map (D.copy a x) = D.copy (t.perm a) x := rfl

@[simp] theorem symm_map_map (q : D.Realization) : t.symm.map (t.map q) = q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    change D.copy (t.perm.symm (t.perm p.1)) p.2 = D.copy p.1 p.2
    rw [t.perm.symm_apply_apply]

@[simp] theorem map_symm_map (q : D.Realization) : t.map (t.symm.map q) = q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    change D.copy (t.perm (t.perm.symm p.1)) p.2 = D.copy p.1 p.2
    rw [t.perm.apply_symm_apply]

def quotientEquiv : D.Realization ≃ D.Realization where
  toFun := t.map
  invFun := t.symm.map
  left_inv := t.symm_map_map
  right_inv := t.map_symm_map

variable {L : Nat → Type w} (S : RelStructure L A)

theorem map_rel {n : Nat} (r : L n) (q : Fin n → D.Realization)
    (h : (D.quotientStructure S).rel r q) :
    (D.quotientStructure S).rel r (fun i => t.map (q i)) := by
  obtain ⟨a, x, hx, heq⟩ := h
  exact ⟨t.perm a, x, hx, fun i => congrArg t.map (heq i)⟩

theorem rel_iff {n : Nat} (r : L n) (q : Fin n → D.Realization) :
    (D.quotientStructure S).rel r (fun i => t.map (q i)) ↔
      (D.quotientStructure S).rel r q := by
  constructor
  · intro h
    have k := t.symm.map_rel S r (fun i => t.map (q i)) h
    simpa using k
  · exact t.map_rel S r q

/-- The incoming edge, not the outgoing inverse-labelled edge, extends f. -/
theorem extends_of_step (a : V) (x y : A) (h : D.step (t.perm a, x) (a, y)) :
    t.map (D.copy a x) = D.copy a y := D.copy_eq_of_step h
end Symmetry
end System
end GluingEPPA
