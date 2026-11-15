import GluingEPPA.Reducts.MultipartiteFiniteAtlas
import GluingEPPA.Reducts.FixedCarrierTransport
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Pi

/-!
A single finite balanced carrier for an actual finite partitioned input.
For every actual induced domain D, construct and combine the partwise replica
coordinates, preserving the partition and every original domain point.
No atlas, divisibility hypothesis, or finite extension is supplied by the caller.
Factorial padding is larger than the paper's sharp lcm padding. This module
does not assert the final coherent-EPPA theorem.
-/
namespace GluingEPPA.Reducts.MultipartiteConcreteCarrier
open GluingEPPA.Reducts.MultipartiteFiniteAtlas
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.FixedCarrierTransport

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {A I : Type u} [Fintype A] [Fintype I]

abbrev padding (A : Type u) [Fintype A] : Nat := (Fintype.card A).factorial
abbrev Base (A I : Type u) [Fintype A] := I × Fin (padding A)

def inputIndex : A ↪ Fin (padding A) where
  toFun a := ⟨(Fintype.equivFin A a).val,
    Nat.lt_of_lt_of_le (Fintype.equivFin A a).isLt (Nat.self_le_factorial _)⟩
  inj' := by
    intro a b h
    apply (Fintype.equivFin A).injective
    apply Fin.ext
    exact congrArg Fin.val h

def inputEmbedding (o : A → I) : A ↪ Base A I where
  toFun a := (o a, inputIndex a)
  inj' := by
    intro a b h
    exact inputIndex.injective (congrArg Prod.snd h)

abbrev Trace (o : A → I) (D : Set A) (i : I) := {d : D // o d.val = i}
abbrev occupied (o : A → I) (D : Set A) (i : I) := Nonempty (Trace o D i)

def layers (o : A → I) (D : Set A) (i : I) : Nat :=
  padding A / Fintype.card (Trace o D i)

theorem trace_card_le (o : A → I) (D : Set A) (i : I) :
    Fintype.card (Trace o D i) ≤ Fintype.card A := by
  exact Fintype.card_le_of_injective (fun d : Trace o D i => d.val.val)
    (fun _ _ h => Subtype.ext (Subtype.ext h))

theorem trace_card_dvd (o : A → I) (D : Set A) (i : I) (hi : occupied o D i) :
    Fintype.card (Trace o D i) ∣ padding A := by
  exact Nat.dvd_factorial (Fintype.card_pos_iff.mpr hi) (trace_card_le o D i)

theorem layers_pos (o : A → I) (D : Set A) (i : I) (hi : occupied o D i) :
    0 < layers o D i := by
  exact Nat.div_pos ((trace_card_le o D i).trans (Nat.self_le_factorial _))
    (Fintype.card_pos_iff.mpr hi)

def traceIndex (o : A → I) (D : Set A) (i : I) : Trace o D i ↪ Fin (padding A) where
  toFun d := inputIndex d.val.val
  inj' := by
    intro a b h
    exact Subtype.ext (Subtype.ext (inputIndex.injective h))

theorem exists_part_atlas (o : A → I) (D : Set A) (i : I) (hi : occupied o D i) :
    ∃ e : (Trace o D i × Fin (layers o D i)) ≃ Fin (padding A),
      ∀ d, e (d, ⟨0, layers_pos o D i hi⟩) = inputIndex d.val.val := by
  apply replica_atlas (traceIndex o D i) (layers o D i) (layers_pos o D i hi)
  simpa only [Fintype.card_fin] using Nat.mul_div_cancel' (trace_card_dvd o D i hi)

def partAtlas (o : A → I) (D : Set A) (i : I) (hi : occupied o D i) :
    (Trace o D i × Fin (layers o D i)) ≃ Fin (padding A) :=
  Classical.choose (exists_part_atlas o D i hi)

theorem partAtlas_zero (o : A → I) (D : Set A) (i : I) (hi : occupied o D i)
    (d : Trace o D i) :
    partAtlas o D i hi (d, ⟨0, layers_pos o D i hi⟩) = inputIndex d.val.val :=
  Classical.choose_spec (exists_part_atlas o D i hi) d

abbrev Unused (o : A → I) (D : Set A) := {w : Base A I // ¬ occupied o D w.1}
abbrev Indexed (o : A → I) (D : Set A) :=
  Sum (Σ i : I, Trace o D i × Fin (layers o D i)) (Unused o D)

def indexedForward (o : A → I) (D : Set A) : Indexed o D → Base A I
  | .inl ⟨i, d, t⟩ => (i, partAtlas o D i ⟨d⟩ (d, t))
  | .inr w => w.val

def indexedOwner (o : A → I) (D : Set A) : Indexed o D → I
  | .inl z => z.1
  | .inr w => w.val.1

theorem indexedForward_injective (o : A → I) (D : Set A) :
    Function.Injective (indexedForward o D) := by
  intro x y h
  cases x with
  | inl x =>
    rcases x with ⟨i, d, t⟩
    cases y with
    | inl y =>
      rcases y with ⟨j, e, s⟩
      have hij : i = j := congrArg Prod.fst h
      subst j
      have hz : (d, t) = (e, s) := (partAtlas o D i ⟨d⟩).injective (congrArg Prod.snd h)
      cases hz
      rfl
    | inr w =>
      have hi : i = w.val.1 := congrArg Prod.fst h
      exact False.elim (w.property (hi ▸ (show occupied o D i from ⟨d⟩)))
  | inr w =>
    cases y with
    | inl y =>
      rcases y with ⟨i, d, t⟩
      have hi : w.val.1 = i := congrArg Prod.fst h
      exact False.elim (w.property (hi.symm ▸ (show occupied o D i from ⟨d⟩)))
    | inr z => exact congrArg Sum.inr (Subtype.ext h)

theorem indexedForward_surjective (o : A → I) (D : Set A) :
    Function.Surjective (indexedForward o D) := by
  intro w
  by_cases hi : occupied o D w.1
  · let z := (partAtlas o D w.1 hi).symm w.2
    refine ⟨.inl ⟨w.1, z⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact (partAtlas o D w.1 hi).apply_symm_apply w.2
  · exact ⟨.inr ⟨w, hi⟩, rfl⟩

def indexedAtlas (o : A → I) (D : Set A) : Indexed o D ≃ Base A I :=
  Equiv.ofBijective (indexedForward o D)
    ⟨indexedForward_injective o D, indexedForward_surjective o D⟩

def multiplicity (o : A → I) (D : Set A) (d : D) := layers o D (o d.val)

theorem multiplicity_pos (o : A → I) (D : Set A) (d : D) :
    0 < multiplicity o D d := layers_pos o D (o d.val) ⟨⟨d, rfl⟩⟩

def copiesIndexed (o : A → I) (D : Set A) :
    MultipartiteReplication.Copies (multiplicity o D) ≃
      (Σ i : I, Trace o D i × Fin (layers o D i)) where
  toFun z := ⟨o z.val.1.val, ⟨z.val.1, rfl⟩, ⟨z.val.2, z.property⟩⟩
  invFun z := ⟨(z.2.1.val, z.2.2.val), by
    change z.2.2.val < layers o D (o z.2.1.val.val)
    rw [z.2.1.property]
    exact z.2.2.isLt⟩
  left_inv := by intro z; rfl
  right_inv := by
    rintro ⟨i, ⟨d, hd⟩, t⟩
    cases hd
    rfl

abbrev Model (o : A → I) (D : Set A) :=
  MultipartiteReplication.Space (multiplicity o D) (Unused o D)

def commonAtlas (o : A → I) (D : Set A) : Model o D ≃ Base A I :=
  (Equiv.sumCongr (copiesIndexed o D) (Equiv.refl _)).trans (indexedAtlas o D)

theorem commonAtlas_owner (o : A → I) (D : Set A) (z : Model o D) :
    (commonAtlas o D z).1 = MultipartiteReplication.owner (fun d : D => o d.val)
      (fun w : Unused o D => w.val.1) z := by
  cases z <;> rfl

theorem commonAtlas_fixes (o : A → I) (D : Set A) (d : D) :
    commonAtlas o D (MultipartiteReplication.embed (multiplicity_pos o D) d) =
      inputEmbedding o d.val := by
  apply Prod.ext
  · rfl
  · exact partAtlas_zero o D (o d.val) ⟨⟨d, rfl⟩⟩ ⟨d, rfl⟩

theorem unused_separate (o : A → I) (D : Set A) (d : D) (w : Unused o D) :
    o d.val ≠ w.val.1 := by
  intro h
  exact w.property ⟨⟨d, h⟩⟩

/-- The actual fibre equivalence induced by a partition-preserving local map. -/
def traceEquiv (o : A → I) (D : Set A) (p : BasePerm D)
    (hp : ∀ x y, o (p.forward x).val = o (p.forward y).val ↔ o x.val = o y.val)
    (d : D) : Trace o D (o d.val) ≃ Trace o D (o (p.forward d).val) where
  toFun x := ⟨p.forward x.val, (hp x.val d).2 x.property⟩
  invFun y := ⟨p.backward y.val, (hp (p.backward y.val) d).1 (by
    rw [p.right_inv]
    exact y.property)⟩
  left_inv := by intro x; apply Subtype.ext; exact p.left_inv x.val
  right_inv := by intro x; apply Subtype.ext; exact p.right_inv x.val

theorem multiplicity_invariant (o : A → I) (D : Set A) (p : BasePerm D)
    (hp : ∀ x y, o (p.forward x).val = o (p.forward y).val ↔ o x.val = o y.val)
    (d : D) : multiplicity o D (p.forward d) = multiplicity o D d := by
  unfold multiplicity layers
  rw [Fintype.card_congr (traceEquiv o D p hp d)]

/-- One fixed finite carrier and input embedding, with a constructed atlas
for every actual induced domain, including the empty one. -/
theorem concrete_common_carrier (o : A → I) :
    ∃ j : A ↪ Base A I, ∀ D : Set A,
      ∃ e : Model o D ≃ Base A I,
        (∀ d : D, e (MultipartiteReplication.embed (multiplicity_pos o D) d) = j d.val) ∧
        (∀ z, (e z).1 = MultipartiteReplication.owner (fun d : D => o d.val)
          (fun w : Unused o D => w.val.1) z) := by
  exact ⟨inputEmbedding o, fun D =>
    ⟨commonAtlas o D, commonAtlas_fixes o D, commonAtlas_owner o D⟩⟩

theorem model_finite (o : A → I) (D : Set A) : Finite (Model o D) :=
  Finite.of_equiv (Base A I) (commonAtlas o D).symm

end
end GluingEPPA.Reducts.MultipartiteConcreteCarrier
