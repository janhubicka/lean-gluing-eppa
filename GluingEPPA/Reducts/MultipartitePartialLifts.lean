import GluingEPPA.Reducts.MultipartitePartialBase

/-! Construct individual extensions of ALL actual partial isomorphisms in the
same finite witness as the local homomorphic lifts. These individual choices
are not claimed coherent; they supply the transports for domain assembly.
-/
namespace GluingEPPA.Reducts.MultipartitePartialLifts
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.PairRowCompletion
open GluingEPPA.Reducts.FixedCarrierTransport
open GluingEPPA.Reducts.MultipartiteConcreteCarrier
open GluingEPPA.Reducts.MultipartiteActualLocalActions
open GluingEPPA.Reducts.MultipartiteLocalWitness
open GluingEPPA.Reducts.MultipartitePartialBase

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {A I : Type u} [Fintype A] [Fintype I]
variable {S : Input A I} {D E : Set A}

def basePerm (p : PartialIso S D E) : BasePerm (Base A I) where
  forward := baseEquiv p
  backward := (baseEquiv p).symm
  left_inv := (baseEquiv p).symm_apply_apply
  right_inv := (baseEquiv p).apply_symm_apply

def movedBaseline (p : PartialIso S D E) (x y : Base A I) : Bool :=
  baseline (baseEquiv p x) (baseEquiv p y)

def forced (p : PartialIso S D E) (x y : Base A I) : Bool :=
  Bool.xor (rows S (baseEquiv p x) (baseEquiv p y)) (rows S x y)

theorem defect_of_sums (a b c d col bas moved : Bool)
    (h1 : Bool.xor a b = Bool.xor col bas)
    (h2 : Bool.xor c d = Bool.xor col moved) :
    Bool.xor (Bool.xor c a) (Bool.xor d b) = Bool.xor moved bas := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases col <;>
    cases bas <;> cases moved <;> simp_all

theorem prescribed_defect (p : PartialIso S D E) (x y : Base A I)
    (hxy : x.1 ≠ y.1) (hx : inside S D x = true) (hy : inside S D y = true) :
    Bool.xor (forced p x y) (forced p y x) = Bool.xor (movedBaseline p x y) (baseline x y) := by
  obtain ⟨d, rfl⟩ := of_decide_eq_true hx
  obtain ⟨e, rfl⟩ := of_decide_eq_true hy
  have ht : S.owner (p.map d).val ≠ S.owner (p.map e).val :=
    fun h => hxy ((p.part_iff d e).1 h)
  have h1 := rows_sum S (inputEmbedding S.owner d.val) (inputEmbedding S.owner e.val) hxy
  have h2 := rows_sum S (inputEmbedding S.owner (p.map d).val)
    (inputEmbedding S.owner (p.map e).val) ht
  rw [initialTable_restrict] at h1
  rw [initialTable_restrict, p.color_eq] at h2
  unfold forced movedBaseline
  rw [baseEquiv_extends, baseEquiv_extends]
  exact defect_of_sums _ _ _ _ _ _ _ h1 h2

def shifts (p : PartialIso S D E) : Base A I → Base A I → Bool :=
  completeRows (inside S D) baseline (movedBaseline p) (forced p)

theorem shifts_pair (p : PartialIso S D E) (x y : Base A I) (h : x.1 ≠ y.1) :
    Bool.xor (shifts p x y) (shifts p y x) = Bool.xor (movedBaseline p x y) (baseline x y) := by
  exact completeRows_pair (inside S D) baseline (movedBaseline p) (forced p) x y
    (baseline_reverse x y h)
    (baseline_reverse (baseEquiv p x) (baseEquiv p y)
      (fun he => h ((baseEquiv_part p x y).1 he)))
    (prescribed_defect p x y h)

def extension (p : PartialIso S D E) : BasePerm (Carrier A I) where
  forward v := rename (basePerm p) (translate (shifts p) v)
  backward v := translate (shifts p) (rename (basePerm p).inverse v)
  left_inv := by intro v; rw [rename_inverse, translate_twice]
  right_inv := by
    intro v
    rw [translate_twice]
    have hi : (basePerm p).inverse.inverse = basePerm p := basePerm_ext _ _ (fun _ => rfl)
    simpa only [hi] using rename_inverse (basePerm p).inverse v

theorem extension_part (p : PartialIso S D E) (x y : Carrier A I) :
    ((extension p).forward x).1.1 = ((extension p).forward y).1.1 ↔ x.1.1 = y.1.1 :=
  baseEquiv_part p x.1 y.1

theorem xor_reading (bas moved l r t s : Bool) (h : Bool.xor t s = Bool.xor moved bas) :
    Bool.xor (Bool.xor moved (Bool.xor l t)) (Bool.xor r s) =
      Bool.xor (Bool.xor bas l) r := by
  cases bas <;> cases moved <;> cases l <;> cases r <;> cases t <;> cases s <;> simp_all

theorem extension_reading (p : PartialIso S D E) (x y : Carrier A I)
    (h : x.1.1 ≠ y.1.1) :
    reading baseline ((extension p).forward x) ((extension p).forward y) = reading baseline x y := by
  change Bool.xor (Bool.xor (baseline (baseEquiv p x.1) (baseEquiv p y.1))
    (Bool.xor (x.2 ((baseEquiv p).symm (baseEquiv p y.1)))
      (shifts p x.1 ((baseEquiv p).symm (baseEquiv p y.1)))))
    (Bool.xor (y.2 ((baseEquiv p).symm (baseEquiv p x.1)))
      (shifts p y.1 ((baseEquiv p).symm (baseEquiv p x.1)))) = reading baseline x y
  rw [(baseEquiv p).symm_apply_apply, (baseEquiv p).symm_apply_apply]
  exact xor_reading _ _ _ _ _ _ (shifts_pair p x.1 y.1 h)

theorem extension_color (p : PartialIso S D E) (x y : Carrier A I) :
    label ((extension p).forward x) ((extension p).forward y) = label x y := by
  by_cases h : x.1.1 = y.1.1
  · rw [label_within _ _ ((extension_part p x y).2 h), label_within _ _ h]
  · have hn : ((extension p).forward x).1.1 ≠ ((extension p).forward y).1.1 :=
      fun he => h ((extension_part p x y).1 he)
    simp only [label, if_neg h, if_neg hn]
    exact extension_reading p x y h

theorem extension_agrees (p : PartialIso S D E) (d : D) :
    (extension p).forward (inputCopy S d.val) = inputCopy S (p.map d).val := by
  apply Prod.ext
  · exact baseEquiv_extends p d
  · funext y
    change Bool.xor (rows S (inputEmbedding S.owner d.val) ((baseEquiv p).symm y))
      (shifts p (inputEmbedding S.owner d.val) ((baseEquiv p).symm y)) =
      rows S (inputEmbedding S.owner (p.map d).val) y
    have hs : shifts p (inputEmbedding S.owner d.val) ((baseEquiv p).symm y) =
        forced p (inputEmbedding S.owner d.val) ((baseEquiv p).symm y) :=
      completeRows_on_domain (inside S D) baseline (movedBaseline p) (forced p)
        (inputEmbedding S.owner d.val) (inside_input S D d) ((baseEquiv p).symm y)
    rw [hs]
    unfold forced
    rw [baseEquiv_extends, (baseEquiv p).apply_symm_apply]
    cases rows S (inputEmbedding S.owner d.val) ((baseEquiv p).symm y) <;>
      cases rows S (inputEmbedding S.owner (p.map d).val) y <;> rfl

/-- An unconditional ordinary EPPA witness for the actual Boolean input.
The finite carrier and its class axioms are constructed in LocalWitness.
Coherence across different domains is a further construction, not a premise.
-/
theorem finite_ordinary_witness (S : Input A I) :
    ∃ j : A ↪ Carrier A I,
      (∀ a b, label (j a) (j b) = S.color a b) ∧
      (∀ a b, (j a).1.1 = (j b).1.1 ↔ S.owner a = S.owner b) ∧
      ∀ (D E : Set A) (p : PartialIso S D E), ∃ F : BasePerm (Carrier A I),
        (∀ d : D, F.forward (j d.val) = j (p.map d).val) ∧
        (∀ x y, label (F.forward x) (F.forward y) = label x y) ∧
        (∀ x y, (F.forward x).1.1 = (F.forward y).1.1 ↔ x.1.1 = y.1.1) := by
  exact ⟨inputCopy S, inputCopy_color S, inputCopy_part S, fun D E p =>
    ⟨extension p, extension_agrees p, extension_color p, extension_part p⟩⟩

end
end GluingEPPA.Reducts.MultipartitePartialLifts
