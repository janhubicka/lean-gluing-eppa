import GluingEPPA.Reducts.AnchorGeneralTheorem
import GluingEPPA.Reducts.AnchorStructureTransfer

/-! Coherence for every compatible decorated arrow, with an actual section
of the descended ambient-group map. The incoming coherent augmented
realization is explicit; no existence of that realization is asserted.
No coherent choice of unlabelled ambient extensions is assumed. -/
namespace GluingEPPA.Reducts.AnchorLabelledCoherence
open GluingEPPA.Reducts.AnchorExtraction
open GluingEPPA.Reducts.AnchorFamily
open GluingEPPA.Reducts.AnchorActions
open GluingEPPA.Reducts.AnchorGroupDescent
open GluingEPPA.Reducts.AnchorGeneralTheorem
noncomputable section
universe u
variable {A V Z J : Type u}

def partialId {X : Type u} (D : X → Prop) : Rel X := fun x y => D x ∧ x = y
def Matching {X : Type u} (f g : Rel X) : Prop :=
  ∀ y, (∃ x, f x y) ↔ ∃ z, g y z

theorem decorated_matching (f g : Rel A) (h k : Equiv.Perm V)
    (hm : Matching f g) : Matching (decorated f h) (decorated g k) := by
  intro y
  cases y with
  | inl a =>
    constructor
    · rintro ⟨x,hx⟩
      cases x with
      | inl b =>
        obtain ⟨c,hc⟩ := (hm a).1 ⟨b,hx⟩
        exact ⟨.inl c,hc⟩
      | inr v => exact False.elim hx
    · rintro ⟨z,hz⟩
      cases z with
      | inl b =>
        obtain ⟨c,hc⟩ := (hm a).2 ⟨b,hz⟩
        exact ⟨.inl c,hc⟩
      | inr v => exact False.elim hz
  | inr v =>
    exact ⟨fun _ => ⟨.inr (k v),rfl⟩,
      fun _ => ⟨.inr (h.symm v),h.apply_symm_apply v⟩⟩

theorem decorated_identity (D : A → Prop) :
    decorated (partialId D) (1 : Equiv.Perm V) =
      partialId (fun x : Sum A V => match x with | .inl a => D a | .inr _ => True) := by
  funext x y
  apply propext
  cases x <;> cases y <;> simp [decorated,partialId]

theorem partialId_false : partialId (fun _ : A => False) = emptyRel A := by
  funext x y
  apply propext
  simp [partialId,emptyRel]

theorem empty_comp : relComp (emptyRel A) (emptyRel A) = emptyRel A := by
  funext x y
  apply propext
  simp [relComp,emptyRel]

variable {e : A ↪ V} {L : Rel A → Prop} {H : Subgroup (Equiv.Perm V)}
variable (S : System e L (fun h => h ∈ H) Z J) [Nonempty V]

/-- Precisely the coherent extension data on the augmented set. All laws
concern incoming permutations of Z, not the desired extracted projection. -/
structure CoherentRaw where
  realizes : Realizes S
  transitive : ∀ j k, ∃ p : Equiv.Perm Z,
    CopySymmetry S p ∧ ∀ x, p (S.copy j x) = S.copy k x
  extend : (r : Rel (Sum A V)) → Allowed e L (fun h => h ∈ H) r → Equiv.Perm Z
  copies : ∀ r hr, CopySymmetry S (extend r hr)
  agrees : ∀ r hr x y, r x y → extend r hr (S.copy S.root x) = S.copy S.root y
  identity : ∀ D (hr : Allowed e L (fun h => h ∈ H) (partialId D)),
    extend (partialId D) hr = 1
  composition : ∀ r s hr hs (hc : Allowed e L (fun h => h ∈ H) (relComp r s)),
    Matching r s → extend (relComp r s) hc = extend s hs * extend r hr

/-- Changing the graph transports only a proof-valued admissibility witness. -/
theorem CoherentRaw.extend_congr (R : CoherentRaw S)
    {r s : Rel (Sum A V)} (hr : Allowed e L (fun h => h ∈ H) r)
    (hs : Allowed e L (fun h => h ∈ H) s) (heq : r = s) :
    R.extend r hr = R.extend s hs := by
  cases heq
  rfl

def CoherentRaw.ordinary (R : CoherentRaw S) : RawData S where
  realizes := R.realizes
  extensions := fun r hr => ⟨R.extend r hr,R.copies r hr,R.agrees r hr⟩
  transitive := R.transitive

def labelledAllowed (f : Rel A) (hf : L f) (h : H) (hc : Compatible e f h.val) :
    Allowed e L (fun h => h ∈ H) (decorated f h.val) :=
  Or.inr ⟨f,hf,h.val,h.property,hc,rfl⟩

def liftedSymmetry (R : CoherentRaw S) (f : Rel A) (hf : L f) (h : H)
    (hc : Compatible e f h.val) : Symmetry S :=
  symmetryOfExtension S (R.extend (decorated f h.val) (labelledAllowed f hf h hc))
    (R.copies _ _).1 (R.copies _ _).2 h.val
    (fun v => R.agrees _ _ (.inr v) (.inr (h.val v)) rfl)

abbrev RealGroup := (realHom S).range

def labelledLift (R : CoherentRaw S) (f : Rel A) (hf : L f) (h : H)
    (hc : Compatible e f h.val) : RealGroup S :=
  ⟨realHom S (stabilizerOfSymmetry S (liftedSymmetry S R f hf h hc)),
    ⟨stabilizerOfSymmetry S (liftedSymmetry S R f hf h hc),rfl⟩⟩

theorem labelledLift_label_congr (R : CoherentRaw S) (f : Rel A) (hf : L f)
    (h k : H) (hc : Compatible e f h.val) (kc : Compatible e f k.val) (heq : h = k) :
    labelledLift S R f hf h hc = labelledLift S R f hf k kc := by
  cases heq
  rfl

theorem labelledLift_perm (R : CoherentRaw S) (f : Rel A) (hf : L f) (h : H)
    (hc : Compatible e f h.val) :
    (labelledLift S R f hf h hc).val = (liftedSymmetry S R f hf h hc).restrict := by
  change (chosen S (stabilizerOfSymmetry S (liftedSymmetry S R f hf h hc))).restrict = _
  rw [chosen_of_symmetry S]

theorem labelledLift_value (R : CoherentRaw S) (f : Rel A) (hf : L f) (h : H)
    (hc : Compatible e f h.val) (y : Real S) :
    ((labelledLift S R f hf h hc).val y).val =
      R.extend (decorated f h.val) (labelledAllowed f hf h hc) y.val := by
  rw [labelledLift_perm S R f hf h hc]
  rfl

theorem labelledLift_extends (R : CoherentRaw S) (f : Rel A) (hf : L f) (h : H)
    (hc : Compatible e f h.val) (a b : A) (hab : f a b) :
    (labelledLift S R f hf h hc).val (chart S S.root (root_retained S) a) =
      chart S S.root (root_retained S) b := by
  apply Subtype.ext
  rw [labelledLift_value S R f hf h hc]
  exact R.agrees _ _ (.inl a) (.inl b) hab

def identityCompatible (D : A → Prop) : Compatible e (partialId D) (1 : H).val :=
  fun a b hab => congrArg e hab.2

theorem labelledLift_identity (R : CoherentRaw S) (D : A → Prop) (hf : L (partialId D)) :
    labelledLift S R (partialId D) hf (1 : H) (identityCompatible D) = 1 := by
  have hi : R.extend (decorated (partialId D) (1 : H).val)
      (labelledAllowed _ hf 1 (identityCompatible D)) = 1 := by
    have ha : Allowed e L (fun h => h ∈ H)
        (partialId (fun x : Sum A V => match x with | .inl a => D a | .inr _ => True)) := by
      rw [← decorated_identity D]
      exact labelledAllowed _ hf 1 (identityCompatible D)
    exact (R.extend_congr _ ha (decorated_identity D)).trans (R.identity _ ha)
  apply Subtype.ext
  apply Equiv.ext
  intro y
  apply Subtype.ext
  rw [labelledLift_value S R (partialId D) hf 1 (identityCompatible D),hi]
  rfl

theorem labelledLift_comp (R : CoherentRaw S) (f g : Rel A)
    (hf : L f) (hg : L g) (hfg : L (relComp f g)) (h k : H)
    (hc : Compatible e f h.val) (kc : Compatible e g k.val) (hm : Matching f g) :
    labelledLift S R (relComp f g) hfg (k*h) (compatible_comp e f g h.val k.val hc kc) =
      labelledLift S R g hg k kc * labelledLift S R f hf h hc := by
  have ha : Allowed e L (fun h => h ∈ H) (relComp (decorated f h.val) (decorated g k.val)) := by
    rw [decorated_comp]
    exact labelledAllowed _ hfg (k*h) (compatible_comp e f g h.val k.val hc kc)
  have hp0 := R.composition (decorated f h.val) (decorated g k.val)
    (labelledAllowed f hf h hc) (labelledAllowed g hg k kc) ha (decorated_matching f g h.val k.val hm)
  have hp := (R.extend_congr ha
    (labelledAllowed (relComp f g) hfg (k*h) (compatible_comp e f g h.val k.val hc kc))
    (decorated_comp f g h.val k.val)).symm.trans hp0
  apply Subtype.ext
  apply Equiv.ext
  intro y
  apply Subtype.ext
  change ((labelledLift S R (relComp f g) hfg (k*h) _).val y).val =
    ((labelledLift S R g hg k kc).val ((labelledLift S R f hf h hc).val y)).val
  rw [labelledLift_value, labelledLift_value, labelledLift_value]
  exact congrArg (fun p : Equiv.Perm Z => p y.val) hp

def ambientDescent (hs : Function.Surjective (projection S)) : RealGroup S →* H where
  toFun g := ⟨(descent S hs g).val,anchor_range_allowed S (descent S hs g)⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun q : (anchorHom S).range => q.val) (descent S hs).map_one
  map_mul' := by
    intro g f
    apply Subtype.ext
    exact congrArg (fun q : (anchorHom S).range => q.val) ((descent S hs).map_mul g f)

theorem ambientDescent_equivariant (hs : Function.Surjective (projection S))
    (g : RealGroup S) (y : Real S) :
    projection S (g.val y) = (ambientDescent S hs g).val (projection S y) :=
  descended_equivariant S g y

theorem labelledLift_over (R : CoherentRaw S) (hs : Function.Surjective (projection S))
    (f : Rel A) (hf : L f) (h : H) (hc : Compatible e f h.val) :
    ambientDescent S hs (labelledLift S R f hf h hc) = h := by
  apply Subtype.ext
  ext v
  obtain ⟨y,rfl⟩ := hs v
  rw [← ambientDescent_equivariant S hs, labelledLift_perm]
  have ha : (liftedSymmetry S R f hf h hc).anchorAction = h.val :=
    supplied_anchor_action S _ _ _ h.val
      (fun v => R.agrees _ _ (.inr v) (.inr (h.val v)) rfl)
  rw [(liftedSymmetry S R f hf h hc).projection_equivariant,ha]

def emptyCompatible (h : H) : Compatible e (emptyRel A) h.val :=
  fun _ _ hab => False.elim hab

def ambientSection (R : CoherentRaw S) (hzero : L (emptyRel A)) : H →* RealGroup S where
  toFun h := labelledLift S R (emptyRel A) hzero h (emptyCompatible h)
  map_one' := by
    have hid : L (partialId (fun _ : A => False)) := by
      simpa only [partialId_false] using hzero
    simpa only [partialId_false] using labelledLift_identity S R (fun _ : A => False) hid
  map_mul' := by
    intro k h
    have hf : L (relComp (emptyRel A) (emptyRel A)) := by
      simpa only [empty_comp] using hzero
    have hm : Matching (emptyRel A) (emptyRel A) := by intro a; simp [emptyRel]
    simpa only [empty_comp] using labelledLift_comp S R (emptyRel A) (emptyRel A)
      hzero hzero hf h k (emptyCompatible h) (emptyCompatible k) hm

theorem ambientSection_rightInverse (R : CoherentRaw S) (hzero : L (emptyRel A))
    (hs : Function.Surjective (projection S)) (h : H) :
    ambientDescent S hs (ambientSection S R hzero h) = h :=
  labelledLift_over S R hs (emptyRel A) hzero h (emptyCompatible h)

theorem split_ambient_epimorphism (R : CoherentRaw S) (hzero : L (emptyRel A))
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, h ∈ H ∧ ∃ a : A, h (e a) = v) :
    ∃ theta : RealGroup S →* H, ∃ sec : H →* RealGroup S,
      (∀ h, theta (sec h) = h) ∧ Function.Surjective theta ∧
      ∀ g y, projection S (g.val y) = (theta g).val (projection S y) := by
  have hs := projection_surjective S R.realizes hzero (fun h hh => H.inv_mem hh) horbit
  refine ⟨ambientDescent S hs,ambientSection S R hzero,
    ambientSection_rightInverse S R hzero hs,?_,ambientDescent_equivariant S hs⟩
  intro h
  exact ⟨ambientSection S R hzero h,ambientSection_rightInverse S R hzero hs h⟩

end
end GluingEPPA.Reducts.AnchorLabelledCoherence
