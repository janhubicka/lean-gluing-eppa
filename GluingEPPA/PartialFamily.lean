import GluingEPPA.PaddedFamily

/-!
Finite partial transport relations with an involution on their labels.
The structure does not contain a total permutation extension.  The
latter is proved below using finite injective-pair extension and
involutive completion, with an arbitrary linear order to orient each
two-element orbit of the inverse operation.
-/
namespace GluingEPPA
universe u v w
structure PartialFamily {L : Nat → Type u} {A : Type v}
    (S : RelStructure L A) (I : Type w) where
  labels : InverseLabels I
  transport : I → A → A → Prop
  transport_inverse : ∀ i x y,
    transport i x y ↔ transport (labels.inv i) y x
  unique_target : ∀ i x y z,
    transport i x y → transport i x z → y = z
  unique_source : ∀ i x y z,
    transport i x z → transport i y z → x = y
  transport_rel : ∀ {n} (r : L n) (i : I) (x y : Fin n → A),
    (∀ j, transport i (x j) (y j)) → (S.rel r x ↔ S.rel r y)

namespace PartialFamily
variable {L : Nat → Type u} {A : Type v} {I : Type w}
variable {S : RelStructure L A} (F : PartialFamily S I)

def Extends (i : I) (σ : A ≃ A) : Prop :=
  ∀ x y, F.transport i x y → σ x = y

theorem exists_extension [Finite A] (i : I) :
    ∃ σ : A ≃ A, F.Extends i σ := by
  classical
  let dom : A → Prop := fun x => ∃ y, F.transport i x y
  let target : {x // dom x} → A := fun x => Classical.choose x.property
  have ht (x : {x // dom x}) : F.transport i x (target x) :=
    Classical.choose_spec x.property
  have hinj : Function.Injective target := by
    intro x y h
    apply Subtype.ext
    exact F.unique_source i x y (target x) (ht x) (h ▸ ht y)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun x : {x // dom x} => (x : A)) target Subtype.val_injective hinj
  refine ⟨σ, ?_⟩
  intro x y h
  have hx : dom x := ⟨y, h⟩
  exact (hσ ⟨x, hx⟩).trans (F.unique_target i x (target ⟨x, hx⟩) y (ht ⟨x, hx⟩) h)

theorem inverse_extends (i : I) (σ : A ≃ A)
    (h : F.Extends i σ) :
    F.Extends (F.labels.inv i) σ.symm := by
  intro x y hxy
  have hback : F.transport i y x := by
    have h1 := (F.transport_inverse (F.labels.inv i) x y).mp hxy
    simpa only [F.labels.inv_inv] using h1
  have hσ := h y x hback
  calc
    σ.symm x = σ.symm (σ y) := congrArg σ.symm hσ.symm
    _ = y := σ.symm_apply_apply y

theorem exists_involution_extension [Finite A] (i : I)
    (hs : F.labels.inv i = i) :
    ∃ σ : A ≃ A, σ.symm = σ ∧ F.Extends i σ := by
  classical
  let dom : A → Prop := fun x => ∃ y, F.transport i x y
  let g : A → A := fun x => if hx : dom x then Classical.choose hx else x
  have hg (x : A) (hx : dom x) : F.transport i x (g x) := by
    simpa [g, hx] using (Classical.choose_spec hx : F.transport i x (Classical.choose hx))
  have hinv : ∀ x y, F.transport i x y → F.transport i y x := by
    intro x y h
    have := (F.transport_inverse i x y).mp h
    simpa only [hs] using this
  have hgg : Function.Involutive g := by
    intro x
    by_cases hx : dom x
    · have hxy := hg x hx
      have hy : dom (g x) := ⟨x, hinv x (g x) hxy⟩
      exact F.unique_target i (g x) (g (g x)) x (hg (g x) hy)
        (hinv x (g x) hxy)
    · simp [g, hx]
  let σ : A ≃ A := {toFun := g, invFun := g, left_inv := hgg, right_inv := hgg}
  refine ⟨σ, ?_, ?_⟩
  · apply Equiv.ext
    intro x
    rfl
  · intro x y h
    have hx : dom x := ⟨y, h⟩
    exact F.unique_target i x (g x) y (hg x hx) h

noncomputable def arbitrary [Finite A] (i : I) : A ≃ A :=
  Classical.choose (F.exists_extension i)

theorem arbitrary_extends [Finite A] (i : I) :
    F.Extends i (F.arbitrary i) :=
  Classical.choose_spec (F.exists_extension i)

noncomputable def selfChoice [Finite A] (i : I)
    (h : F.labels.inv i = i) : A ≃ A :=
  Classical.choose (F.exists_involution_extension i h)

theorem selfChoice_symm [Finite A] (i : I)
    (h : F.labels.inv i = i) :
    (F.selfChoice i h).symm = F.selfChoice i h :=
  (Classical.choose_spec (F.exists_involution_extension i h)).1

theorem selfChoice_extends [Finite A] (i : I)
    (h : F.labels.inv i = i) :
    F.Extends i (F.selfChoice i h) :=
  (Classical.choose_spec (F.exists_involution_extension i h)).2

variable [Finite A] [LinearOrder I]

/-- Choose one orientation in each two-element inverse orbit.
At an inverse fixed point, choose the involutive extension. -/
noncomputable def coherentBase (i : I) : A ≃ A :=
  if hi : F.labels.inv i = i then F.selfChoice i hi
  else if i < F.labels.inv i then F.arbitrary i
  else (F.arbitrary (F.labels.inv i)).symm

theorem coherentBase_extends (i : I) : F.Extends i (F.coherentBase i) := by
  unfold coherentBase
  split_ifs with hfixed hlt
  · exact F.selfChoice_extends i hfixed
  · exact F.arbitrary_extends i
  · have h : F.labels.inv (F.labels.inv i) = i := F.labels.inv_inv i
    have he : F.Extends (F.labels.inv (F.labels.inv i))
        (F.arbitrary (F.labels.inv i)).symm :=
      F.inverse_extends (F.labels.inv i)
        (F.arbitrary (F.labels.inv i))
        (F.arbitrary_extends (F.labels.inv i))
    simpa only [h] using he

theorem coherentBase_inverse (i : I) :
    F.coherentBase (F.labels.inv i) = (F.coherentBase i).symm := by
  classical
  by_cases hs : F.labels.inv i = i
  · calc
      F.coherentBase (F.labels.inv i) = F.coherentBase i :=
        congrArg F.coherentBase hs
      _ = (F.coherentBase i).symm := by
        simp only [coherentBase, dif_pos hs]
        exact (F.selfChoice_symm i hs).symm
  · have hsi : i ≠ F.labels.inv i := Ne.symm hs
    by_cases hlt : i < F.labels.inv i
    · have hnlt : ¬ F.labels.inv i < i := not_lt.mpr (le_of_lt hlt)
      simp [coherentBase, hs, hsi, F.labels.inv_inv, hlt, hnlt]
    · have hgt : F.labels.inv i < i :=
        (lt_or_gt_of_ne hsi).resolve_left hlt
      simp [coherentBase, hs, hsi, F.labels.inv_inv, hlt, hgt]


noncomputable def baseFamily : BaseFamily S I where
  labels := F.labels
  base := F.coherentBase
  base_inverse := F.coherentBase_inverse
  transport := F.transport
  transport_inverse := F.transport_inverse
  transport_base := F.coherentBase_extends
  transport_rel := F.transport_rel

end PartialFamily
end GluingEPPA
