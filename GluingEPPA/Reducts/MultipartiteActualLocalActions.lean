import GluingEPPA.Reducts.MultipartiteConcreteCarrier

/-!
Instantiate replication and transport for the full automorphism group of each
actual induced domain of a finite multipartite input. The common carrier and
all coordinate identifications are constructed by MultipartiteConcreteCarrier.
The auxiliary orientation is constructed from the input, not supplied.
This is the concrete local-action stage, not the final coherent-EPPA endpoint.
-/
namespace GluingEPPA.Reducts.MultipartiteActualLocalActions
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.FixedCarrierTransport
open GluingEPPA.Reducts.MultipartiteConcreteCarrier

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {A I : Type u} [Fintype A] [Fintype I]

structure Input (A I : Type u) where
  owner : A → I
  color : A → A → Bool
  within : ∀ x y, owner x = owner y → color x y = false
  reverse : ∀ x y, owner x ≠ owner y → color y x = Bool.not (color x y)

structure LocalAut (S : Input A I) (D : Set A) where
  perm : BasePerm D
  part_iff : ∀ x y, S.owner (perm.forward x).val = S.owner (perm.forward y).val ↔
    S.owner x.val = S.owner y.val
  color_eq : ∀ x y, S.color (perm.forward x).val (perm.forward y).val =
    S.color x.val y.val

namespace LocalAut

def identity (S : Input A I) (D : Set A) : LocalAut S D where
  perm := BasePerm.identity D
  part_iff := fun _ _ => Iff.rfl
  color_eq := fun _ _ => rfl

def comp {S : Input A I} {D : Set A} (g f : LocalAut S D) : LocalAut S D where
  perm := g.perm.comp f.perm
  part_iff := fun x y => (g.part_iff (f.perm.forward x) (f.perm.forward y)).trans
    (f.part_iff x y)
  color_eq := fun x y => (g.color_eq (f.perm.forward x) (f.perm.forward y)).trans
    (f.color_eq x y)

end LocalAut

def modelAtlas (S : Input A I) (D : Set A) : Atlas (Model S.owner D) (Base A I) where
  forward := commonAtlas S.owner D
  backward := (commonAtlas S.owner D).symm
  left_inv := (commonAtlas S.owner D).symm_apply_apply
  right_inv := (commonAtlas S.owner D).apply_symm_apply

def modelAction {S : Input A I} {D : Set A} (f : LocalAut S D) : BasePerm (Model S.owner D) :=
  MultipartiteReplication.paddedPerm f.perm
    (multiplicity_invariant S.owner D f.perm f.part_iff)

def baseAction {S : Input A I} {D : Set A} (f : LocalAut S D) : BasePerm (Base A I) :=
  transport (modelAtlas S D) (modelAction f)

theorem modelAction_identity (S : Input A I) (D : Set A) :
    modelAction (LocalAut.identity S D) = BasePerm.identity (Model S.owner D) := by
  apply basePerm_ext
  intro z
  exact MultipartiteReplication.padded_identity_forward z

theorem modelAction_comp {S : Input A I} {D : Set A} (g f : LocalAut S D) :
    modelAction (g.comp f) = (modelAction g).comp (modelAction f) := by
  apply basePerm_ext
  intro z
  exact MultipartiteReplication.padded_comp_forward g.perm f.perm
    (multiplicity_invariant S.owner D g.perm g.part_iff)
    (multiplicity_invariant S.owner D f.perm f.part_iff) z

theorem baseAction_identity (S : Input A I) (D : Set A) :
    baseAction (LocalAut.identity S D) = BasePerm.identity (Base A I) := by
  unfold baseAction
  rw [modelAction_identity, transport_identity]

theorem baseAction_comp {S : Input A I} {D : Set A} (g f : LocalAut S D) :
    baseAction (g.comp f) = (baseAction g).comp (baseAction f) := by
  unfold baseAction
  rw [modelAction_comp, transport_comp]

theorem baseAction_extends {S : Input A I} {D : Set A} (f : LocalAut S D) (d : D) :
    (baseAction f).forward (inputEmbedding S.owner d.val) =
      inputEmbedding S.owner (f.perm.forward d).val := by
  exact transport_extends (modelAtlas S D)
    (MultipartiteReplication.embed (multiplicity_pos S.owner D))
    (fun d : D => inputEmbedding S.owner d.val) f.perm.forward (modelAction f)
    (commonAtlas_fixes S.owner D)
    (MultipartiteReplication.padded_embed (multiplicity_pos S.owner D) f.perm
      (multiplicity_invariant S.owner D f.perm f.part_iff)) d

def modelOwner (S : Input A I) (D : Set A) : Model S.owner D → I :=
  MultipartiteReplication.owner (fun d : D => S.owner d.val)
    (fun w : Unused S.owner D => w.val.1)

theorem backward_owner (S : Input A I) (D : Set A) (w : Base A I) :
    modelOwner S D ((modelAtlas S D).backward w) = w.1 := by
  have h := commonAtlas_owner S.owner D ((commonAtlas S.owner D).symm w)
  rw [(commonAtlas S.owner D).apply_symm_apply] at h
  exact h.symm

theorem baseAction_part {S : Input A I} {D : Set A} (f : LocalAut S D) (x y : Base A I) :
    ((baseAction f).forward x).1 = ((baseAction f).forward y).1 ↔ x.1 = y.1 := by
  change (commonAtlas S.owner D ((modelAction f).forward ((modelAtlas S D).backward x))).1 =
    (commonAtlas S.owner D ((modelAction f).forward ((modelAtlas S D).backward y))).1 ↔ _
  rw [commonAtlas_owner, commonAtlas_owner]
  change modelOwner S D ((modelAction f).forward ((modelAtlas S D).backward x)) =
    modelOwner S D ((modelAction f).forward ((modelAtlas S D).backward y)) ↔ _
  rw [MultipartiteReplication.padded_part_iff
    (fun d : D => S.owner d.val) (fun w : Unused S.owner D => w.val.1)
    (unused_separate S.owner D) f.perm
    (multiplicity_invariant S.owner D f.perm f.part_iff) f.part_iff]
  rw [backward_owner, backward_owner]

def baseline (x y : Base A I) : Bool :=
  decide ((Fintype.equivFin I x.1).val < (Fintype.equivFin I y.1).val)

theorem baseline_within (x y : Base A I) (h : x.1 = y.1) : baseline x y = false := by
  simp [baseline, h]

theorem baseline_reverse (x y : Base A I) (h : x.1 ≠ y.1) :
    baseline y x = Bool.not (baseline x y) := by
  have hn : (Fintype.equivFin I x.1).val ≠ (Fintype.equivFin I y.1).val := by
    intro he
    exact h ((Fintype.equivFin I).injective (Fin.ext he))
  unfold baseline
  by_cases hlt : (Fintype.equivFin I x.1).val < (Fintype.equivFin I y.1).val
  · have hnot : ¬ (Fintype.equivFin I y.1).val < (Fintype.equivFin I x.1).val := by omega
    simp [hlt, hnot]
  · have hgt : (Fintype.equivFin I y.1).val < (Fintype.equivFin I x.1).val := by omega
    simp [hlt, hgt]

def modelTable (S : Input A I) (D : Set A) : Model S.owner D → Model S.owner D → Bool :=
  MultipartiteReplication.auxiliary
    (fun d e : D => S.color d.val e.val)
    (fun x y : Unused S.owner D => baseline x.val y.val)

def localTable (S : Input A I) (D : Set A) : Base A I → Base A I → Bool :=
  transportedTable (modelAtlas S D) (modelTable S D)

theorem localTable_restrict (S : Input A I) (D : Set A) (d e : D) :
    localTable S D (inputEmbedding S.owner d.val) (inputEmbedding S.owner e.val) =
      S.color d.val e.val := by
  exact table_restrict (modelAtlas S D)
    (MultipartiteReplication.embed (multiplicity_pos S.owner D))
    (fun d : D => inputEmbedding S.owner d.val) (modelTable S D)
    (commonAtlas_fixes S.owner D) d e

theorem localTable_invariant {S : Input A I} {D : Set A} (f : LocalAut S D) (x y : Base A I) :
    localTable S D ((baseAction f).forward x) ((baseAction f).forward y) = localTable S D x y := by
  exact replicated_table_invariant (modelAtlas S D)
    (fun d e : D => S.color d.val e.val)
    (fun x y : Unused S.owner D => baseline x.val y.val) f.perm
    (multiplicity_invariant S.owner D f.perm f.part_iff) f.color_eq x y

theorem localTable_reverse (S : Input A I) (D : Set A) (x y : Base A I) (h : x.1 ≠ y.1) :
    localTable S D y x = Bool.not (localTable S D x y) := by
  apply MultipartiteReplication.auxiliary_reverse
    (fun d : D => S.owner d.val) (fun w : Unused S.owner D => w.val.1)
    (fun d e : D => S.color d.val e.val)
    (fun v w : Unused S.owner D => baseline v.val w.val)
    (fun d e hde => S.reverse d.val e.val hde)
    (fun v w hvw => baseline_reverse v.val w.val hvw)
  change modelOwner S D ((modelAtlas S D).backward x) ≠
    modelOwner S D ((modelAtlas S D).backward y)
  simpa only [backward_owner] using h

theorem localTable_within (S : Input A I) (D : Set A) (x y : Base A I) (h : x.1 = y.1) :
    localTable S D x y = false := by
  apply MultipartiteReplication.auxiliary_within
    (fun d : D => S.owner d.val) (fun w : Unused S.owner D => w.val.1)
    (fun d e : D => S.color d.val e.val)
    (fun v w : Unused S.owner D => baseline v.val w.val)
    (unused_separate S.owner D)
    (fun d e hde => S.within d.val e.val hde)
    (fun v w hvw => baseline_within v.val w.val hvw)
  change modelOwner S D ((modelAtlas S D).backward x) =
    modelOwner S D ((modelAtlas S D).backward y)
  simpa only [backward_owner] using h

/-- Every actual local group has an explicit action and invariant orientation
on the same constructed finite carrier, extending the actual input on D. -/
theorem actual_local_actions (S : Input A I) (D : Set A) :
    ∃ q : Base A I → Base A I → Bool, ∃ F : LocalAut S D → BasePerm (Base A I),
      (∀ d e : D, q (inputEmbedding S.owner d.val) (inputEmbedding S.owner e.val) = S.color d.val e.val) ∧
      (∀ x y, x.1 = y.1 → q x y = false) ∧
      (∀ x y, x.1 ≠ y.1 → q y x = Bool.not (q x y)) ∧
      F (LocalAut.identity S D) = BasePerm.identity (Base A I) ∧
      (∀ g f, F (g.comp f) = (F g).comp (F f)) ∧
      (∀ f d, (F f).forward (inputEmbedding S.owner d.val) = inputEmbedding S.owner (f.perm.forward d).val) ∧
      (∀ f x y, q ((F f).forward x) ((F f).forward y) = q x y) := by
  exact ⟨localTable S D, baseAction,
    localTable_restrict S D, localTable_within S D, localTable_reverse S D,
    baseAction_identity S D, baseAction_comp, baseAction_extends, localTable_invariant⟩

end
end GluingEPPA.Reducts.MultipartiteActualLocalActions
