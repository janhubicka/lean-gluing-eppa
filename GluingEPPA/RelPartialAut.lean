import GluingEPPA.PartialFamily

/-!
The label type for the unconditional finite relational EPPA theorem is the
finite set of all relation-preserving partial equivalences A ≃. A.
It contains empty maps, partial involutions, and all ordered repeated tuples.
No assumption that a chosen family of extensions already exists is made here.
-/
namespace GluingEPPA
universe u v

/-- A partial automorphism is a partial bijection preserving and reflecting
all relations on tuples entirely in its domain. -/
def RelPartialAut {L : Nat → Type u} {A : Type v}
    (S : RelStructure L A) :=
  {f : A ≃. A // ∀ {n : Nat} (r : L n) (x y : Fin n → A),
    (∀ j, f (x j) = some (y j)) → (S.rel r x ↔ S.rel r y)}

namespace RelPartialAut
variable {L : Nat → Type u} {A : Type v} (S : RelStructure L A)

instance [Finite A] : Finite (RelPartialAut S) := by
  have hf : Finite (A ≃. A) := by
    apply Finite.of_injective (fun f : A ≃. A => fun x : A => f x)
    intro p q h
    exact PEquiv.ext (fun x => congrFun h x)
  exact Subtype.finite

def inverse (f : RelPartialAut S) : RelPartialAut S := by
  refine ⟨f.val.symm, ?_⟩
  intro n r x y h
  have hb : ∀ j, f.val (y j) = some (x j) := by
    intro j
    exact (f.val.eq_some_iff).mp (h j)
  exact (f.property r y x hb).symm

@[simp] theorem inverse_inverse (f : RelPartialAut S) :
    inverse S (inverse S f) = f := by
  apply Subtype.ext
  exact f.val.symm_symm

def family : PartialFamily S (RelPartialAut S) where
  labels :=
    { inv := inverse S
      inv_inv := inverse_inverse S }
  transport f x y := f.val x = some y
  transport_inverse := by
    intro f x y
    exact (f.val.eq_some_iff).symm
  unique_target := by
    intro f x y z hy hz
    exact Option.some.inj (hy.symm.trans hz)
  unique_source := by
    intro f x y z hx hy
    have hx' := (f.val.eq_some_iff).mpr hx
    have hy' := (f.val.eq_some_iff).mpr hy
    exact Option.some.inj (hx'.symm.trans hy')
  transport_rel := by
    intro n r f x y h
    exact f.property r x y h

/-- A finite index type carries a chosen order used only to orient inverse
pairs. The witness is independent of any canonical ordering choice. -/
noncomputable def chosenOrder [Finite A] : LinearOrder (RelPartialAut S) := by
  classical
  letI : Fintype (RelPartialAut S) := Fintype.ofFinite _
  let e := Fintype.equivFin (RelPartialAut S)
  exact LinearOrder.lift' e e.injective

end RelPartialAut
end GluingEPPA
