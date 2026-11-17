import GluingEPPA.Reducts.MultipartiteReplication
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

/-!
Finite carrier bridge for the multipartite local-action construction.
Equal cardinalities give an equivalence that agrees with two specified
embeddings, not merely an arbitrary equivalence. Applied separately in
occupied parts this identifies the replicated model with the SAME padded
carrier, pointwise on the original local domain. No EPPA theorem is used.
-/
namespace GluingEPPA.Reducts.MultipartiteFiniteAtlas
open GluingEPPA.Reducts.MultipartiteReplication
open scoped BigOperators
universe u v w

/-- Extend the identification of two embedded copies while keeping every
specified source point. No action on the complements is assumed. -/
theorem equiv_extending_embeddings
    {D : Type u} {X : Type v} {Y : Type w}
    [Fintype D] [Fintype X] [Fintype Y]
    (a : D ↪ X) (b : D ↪ Y) (hcard : Fintype.card X = Fintype.card Y) :
    ∃ e : X ≃ Y, ∀ d, e (a d) = b d := by
  classical
  let e0 : X ≃ Y := Fintype.equivOfCardEq hcard
  let a0 : D ↪ Y := a.trans e0.toEmbedding
  let er : Set.range a0 ≃ Set.range b :=
    a0.toEquivRange.symm.trans b.toEquivRange
  refine ⟨e0.trans er.extendSubtype, ?_⟩
  intro d
  change er.extendSubtype (a0 d) = b d
  rw [Equiv.extendSubtype_apply_of_mem er (a0 d) (by exact ⟨d, rfl⟩)]
  change (b.toEquivRange (a0.toEquivRange.symm (a0.toEquivRange d))).val = b d
  rw [Equiv.symm_apply_apply]
  rfl

/-- One part, with the entire zero layer fixed as the distinguished domain. -/
theorem replica_atlas
    {D : Type u} {W : Type v} [Fintype D] [Fintype W]
    (j : D ↪ W) (t : Nat) (ht : 0 < t)
    (hcard : Fintype.card D * t = Fintype.card W) :
    ∃ e : (D × Fin t) ≃ W, ∀ d, e (d, ⟨0, ht⟩) = j d := by
  let z : D ↪ D × Fin t :=
    ⟨fun d => (d, ⟨0, ht⟩), fun _ _ h => congrArg Prod.fst h⟩
  exact equiv_extending_embeddings z j (by simpa using hcard)

/-- The actual divisibility hypothesis yields a positive replication count
and the pointwise-fixed finite atlas; that atlas is not an assumption. -/
theorem replica_atlas_of_dvd
    {D : Type u} {W : Type v} [Fintype D] [Fintype W]
    (j : D ↪ W) (hpositive : 0 < Fintype.card W)
    (hdiv : Fintype.card D ∣ Fintype.card W) :
    ∃ t : Nat, ∃ ht : 0 < t, ∃ e : (D × Fin t) ≃ W,
      ∀ d, e (d, ⟨0, ht⟩) = j d := by
  obtain ⟨t, ht⟩ := hdiv
  have htpos : 0 < t := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have bad : Fintype.card W = 0 := by simpa [hzero] using ht
    exact (Nat.ne_of_gt hpositive) bad
  obtain ⟨e, he⟩ := replica_atlas j t htpos ht.symm
  exact ⟨t, htpos, e, he⟩

/-- The bounded layer representation used in the core module is exactly a
finite dependent sum, including when multiplicities vary between parts. -/
def copiesEquivSigma {D : Type u} (m : D → Nat) :
    Copies m ≃ (Σ d : D, Fin (m d)) where
  toFun z := ⟨z.val.1, ⟨z.val.2, z.property⟩⟩
  invFun z := ⟨(z.1, z.2.val), z.2.isLt⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

noncomputable abbrev copiesFintype {D : Type u} [Fintype D] (m : D → Nat) :
    Fintype (Copies m) :=
  Fintype.ofEquiv (Σ d : D, Fin (m d)) (copiesEquivSigma m).symm

theorem copies_card {D : Type u} [Fintype D] (m : D → Nat) :
    @Fintype.card (Copies m) (copiesFintype m) = ∑ d, m d := by
  letI := copiesFintype m
  calc
    Fintype.card (Copies m) = Fintype.card (Σ d : D, Fin (m d)) :=
      Fintype.card_congr (copiesEquivSigma m)
    _ = ∑ d, m d := by simp

theorem finite_replication {D U : Type u} [Finite D] [Finite U] (m : D → Nat) :
    Finite (Space m U) := by
  classical
  letI := Fintype.ofFinite D
  letI := Fintype.ofFinite U
  letI := copiesFintype m
  infer_instance

end GluingEPPA.Reducts.MultipartiteFiniteAtlas
