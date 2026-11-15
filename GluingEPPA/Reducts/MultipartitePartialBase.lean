import GluingEPPA.Reducts.MultipartiteWitnessScope

/-! Actual partial isomorphisms extend to part-preserving permutations of the
same balanced base. This is the finite-set part of the remaining transports;
it is not yet an automorphism of the valuation reading relation.
-/
namespace GluingEPPA.Reducts.MultipartitePartialBase
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.MultipartiteConcreteCarrier
open GluingEPPA.Reducts.MultipartiteActualLocalActions

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {A I : Type u} [Fintype A] [Fintype I]

structure PartialIso (S : Input A I) (D E : Set A) where
  map : D ≃ E
  part_iff : ∀ x y, S.owner (map x).val = S.owner (map y).val ↔ S.owner x.val = S.owner y.val
  color_eq : ∀ x y, S.color (map x).val (map y).val = S.color x.val y.val

variable {S : Input A I} {D E : Set A}
abbrev Occupied (S : Input A I) (D : Set A) := {i : I // occupied S.owner D i}

def partMap (p : PartialIso S D E) (i : Occupied S D) : Occupied S E :=
  ⟨S.owner (p.map (Classical.choice i.property).val).val,
    ⟨⟨p.map (Classical.choice i.property).val, rfl⟩⟩⟩

theorem partMap_value (p : PartialIso S D E) (i : Occupied S D) (d : D)
    (hd : S.owner d.val = i.val) : (partMap p i).val = S.owner (p.map d).val := by
  exact (p.part_iff (Classical.choice i.property).val d).2
    ((Classical.choice i.property).property.trans hd.symm)

theorem partMap_injective (p : PartialIso S D E) : Function.Injective (partMap p) := by
  intro i j h
  apply Subtype.ext
  have hx := (p.part_iff (Classical.choice i.property).val
    (Classical.choice j.property).val).1 (congrArg Subtype.val h)
  exact (Classical.choice i.property).property.symm.trans
    (hx.trans (Classical.choice j.property).property)

theorem partMap_surjective (p : PartialIso S D E) : Function.Surjective (partMap p) := by
  intro j
  let e := (Classical.choice j.property).val
  let d := p.map.symm e
  let i : Occupied S D := ⟨S.owner d.val, ⟨⟨d, rfl⟩⟩⟩
  refine ⟨i, Subtype.ext ?_⟩
  calc
    (partMap p i).val = S.owner (p.map d).val := partMap_value p i d rfl
    _ = S.owner e.val := congrArg (fun x : E => S.owner x.val) (p.map.apply_symm_apply e)
    _ = j.val := (Classical.choice j.property).property

def partsEquiv (p : PartialIso S D E) : Occupied S D ≃ Occupied S E :=
  Equiv.ofBijective (partMap p) ⟨partMap_injective p, partMap_surjective p⟩

def partPermutation (p : PartialIso S D E) : I ≃ I := (partsEquiv p).extendSubtype

theorem partPermutation_on_point (p : PartialIso S D E) (d : D) :
    partPermutation p (S.owner d.val) = S.owner (p.map d).val := by
  rw [partPermutation, Equiv.extendSubtype_apply_of_mem (partsEquiv p)
    (S.owner d.val) (show occupied S.owner D (S.owner d.val) from ⟨⟨d, rfl⟩⟩)]
  exact partMap_value p _ d rfl

theorem partPermutation_occupied (p : PartialIso S D E) (i : I) :
    occupied S.owner E (partPermutation p i) ↔ occupied S.owner D i := by
  constructor
  · rintro ⟨e⟩
    let d := p.map.symm e.val
    have hid : S.owner d.val = i := by
      apply (partPermutation p).injective
      rw [partPermutation_on_point]
      change S.owner (p.map (p.map.symm e.val)).val = partPermutation p i
      rw [p.map.apply_symm_apply]
      exact e.property
    exact ⟨⟨d, hid⟩⟩
  · rintro ⟨d⟩
    have h := partPermutation_on_point p d.val
    rw [d.property] at h
    exact ⟨⟨p.map d.val, h.symm⟩⟩

def betweenTraces (p : PartialIso S D E) (d : D) :
    Trace S.owner D (S.owner d.val) ≃ Trace S.owner E (S.owner (p.map d).val) where
  toFun x := ⟨p.map x.val, (p.part_iff x.val d).2 x.property⟩
  invFun y := ⟨p.map.symm y.val, (p.part_iff (p.map.symm y.val) d).1 (by
    rw [p.map.apply_symm_apply]
    exact y.property)⟩
  left_inv := by intro x; apply Subtype.ext; exact p.map.symm_apply_apply x.val
  right_inv := by intro y; apply Subtype.ext; exact p.map.apply_symm_apply y.val

theorem multiplicity_match (p : PartialIso S D E) (d : D) :
    multiplicity S.owner E (p.map d) = multiplicity S.owner D d := by
  unfold multiplicity layers
  rw [Fintype.card_congr (betweenTraces p d)]

def copiesMap (p : PartialIso S D E) :
    MultipartiteReplication.Copies (multiplicity S.owner D) ≃
      MultipartiteReplication.Copies (multiplicity S.owner E) where
  toFun z := ⟨(p.map z.val.1, z.val.2), by rw [multiplicity_match]; exact z.property⟩
  invFun z := ⟨(p.map.symm z.val.1, z.val.2), by
    have h := multiplicity_match p (p.map.symm z.val.1)
    rw [p.map.apply_symm_apply] at h
    rw [← h]
    exact z.property⟩
  left_inv := by intro z; apply Subtype.ext; exact Prod.ext (p.map.symm_apply_apply z.val.1) rfl
  right_inv := by intro z; apply Subtype.ext; exact Prod.ext (p.map.apply_symm_apply z.val.1) rfl

def unusedMap (p : PartialIso S D E) : Unused S.owner D ≃ Unused S.owner E where
  toFun w := ⟨(partPermutation p w.val.1, w.val.2), by
    intro h
    exact w.property ((partPermutation_occupied p w.val.1).1 h)⟩
  invFun w := ⟨((partPermutation p).symm w.val.1, w.val.2), by
    intro h
    have he := (partPermutation_occupied p ((partPermutation p).symm w.val.1)).2 h
    rw [(partPermutation p).apply_symm_apply] at he
    exact w.property he⟩
  left_inv := by intro w; apply Subtype.ext; exact Prod.ext ((partPermutation p).symm_apply_apply w.val.1) rfl
  right_inv := by intro w; apply Subtype.ext; exact Prod.ext ((partPermutation p).apply_symm_apply w.val.1) rfl

def modelMap (p : PartialIso S D E) : Model S.owner D ≃ Model S.owner E :=
  Equiv.sumCongr (copiesMap p) (unusedMap p)

theorem modelMap_owner (p : PartialIso S D E) (z : Model S.owner D) :
    modelOwner S E (modelMap p z) = partPermutation p (modelOwner S D z) := by
  cases z with
  | inl z => exact (partPermutation_on_point p z.val.1).symm
  | inr z => rfl

def baseEquiv (p : PartialIso S D E) : Base A I ≃ Base A I :=
  ((commonAtlas S.owner D).symm.trans (modelMap p)).trans (commonAtlas S.owner E)

theorem baseEquiv_extends (p : PartialIso S D E) (d : D) :
    baseEquiv p (inputEmbedding S.owner d.val) = inputEmbedding S.owner (p.map d).val := by
  rw [← commonAtlas_fixes S.owner D d]
  change commonAtlas S.owner E (modelMap p ((commonAtlas S.owner D).symm
    (commonAtlas S.owner D (MultipartiteReplication.embed (multiplicity_pos S.owner D) d)))) = _
  rw [(commonAtlas S.owner D).symm_apply_apply]
  exact commonAtlas_fixes S.owner E (p.map d)

theorem baseEquiv_owner (p : PartialIso S D E) (w : Base A I) :
    (baseEquiv p w).1 = partPermutation p w.1 := by
  change (commonAtlas S.owner E (modelMap p ((commonAtlas S.owner D).symm w))).1 = _
  rw [commonAtlas_owner]
  change modelOwner S E (modelMap p ((modelAtlas S D).backward w)) = _
  rw [modelMap_owner, backward_owner]

theorem baseEquiv_part (p : PartialIso S D E) (x y : Base A I) :
    (baseEquiv p x).1 = (baseEquiv p y).1 ↔ x.1 = y.1 := by
  rw [baseEquiv_owner, baseEquiv_owner]
  exact (partPermutation p).injective.eq_iff

/-- All hypotheses now concern the actual input and an actual partial
isomorphism. The balanced-base permutation is a conclusion, not a premise. -/
theorem partial_base_extension (p : PartialIso S D E) :
    ∃ s : Base A I ≃ Base A I,
      (∀ d : D, s (inputEmbedding S.owner d.val) = inputEmbedding S.owner (p.map d).val) ∧
      (∀ x y, (s x).1 = (s y).1 ↔ x.1 = y.1) :=
  ⟨baseEquiv p, baseEquiv_extends p, baseEquiv_part p⟩

end
end GluingEPPA.Reducts.MultipartitePartialBase
