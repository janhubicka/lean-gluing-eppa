import GluingEPPA.Reducts.MultipartitePartialLifts
import GluingEPPA.Reducts.CoherentDomainAssembly

/-!
Assemble constructed local lifts and constructed individual transports for all
actual induced domains. Representatives use the actual isomorphism setoid;
normalized arrows are proved admissible. No EPPA, coherent selection, ambient
action, or completion is assumed. The carrier uses full rows and factorial
padding, not the sharp cross-coordinate bound in the paper.
-/
namespace GluingEPPA.Reducts.MultipartitePartialBase.PartialIso
open GluingEPPA.Reducts.MultipartiteActualLocalActions
open GluingEPPA.Reducts.FixedCarrierTransport
universe u
variable {A I : Type u} {S : Input A I} {D E F : Set A}

def identity (S : Input A I) (D : Set A) : PartialIso S D D where
  map := Equiv.refl D
  part_iff := fun _ _ => Iff.rfl
  color_eq := fun _ _ => rfl

def inverse (p : PartialIso S D E) : PartialIso S E D where
  map := p.map.symm
  part_iff := by
    intro x y
    have h := p.part_iff (p.map.symm x) (p.map.symm y)
    rw [p.map.apply_symm_apply, p.map.apply_symm_apply] at h
    exact h.symm
  color_eq := by
    intro x y
    have h := p.color_eq (p.map.symm x) (p.map.symm y)
    rw [p.map.apply_symm_apply, p.map.apply_symm_apply] at h
    exact h.symm

def comp (q : PartialIso S E F) (p : PartialIso S D E) : PartialIso S D F where
  map := p.map.trans q.map
  part_iff := fun x y => (q.part_iff (p.map x) (p.map y)).trans (p.part_iff x y)
  color_eq := fun x y => (q.color_eq (p.map x) (p.map y)).trans (p.color_eq x y)

def toAtlas (p : PartialIso S D E) : Atlas D E where
  forward := p.map
  backward := p.map.symm
  left_inv := p.map.symm_apply_apply
  right_inv := p.map.apply_symm_apply

end GluingEPPA.Reducts.MultipartitePartialBase.PartialIso

namespace GluingEPPA.Reducts.MultipartiteCoherentEPPA
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.FixedCarrierTransport
open GluingEPPA.Reducts.CoherentDomainAssembly
open GluingEPPA.Reducts.MultipartiteConcreteCarrier
open GluingEPPA.Reducts.MultipartiteActualLocalActions
open GluingEPPA.Reducts.MultipartiteLocalWitness
open GluingEPPA.Reducts.MultipartiteWitnessScope
open GluingEPPA.Reducts.MultipartitePartialBase
open GluingEPPA.Reducts.MultipartitePartialLifts

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {A I : Type u} [Fintype A] [Fintype I]

/-- Part-preservation follows from the digraph relation; no named sorts. -/
def partialIsoOfColor (S : Input A I) {D E : Set A} (p : D ≃ E)
    (hc : ∀ x y, S.color (p x).val (p y).val = S.color x.val y.val) : PartialIso S D E where
  map := p
  part_iff := by intro x y; rw [same_part_iff, same_part_iff, hc, hc]
  color_eq := hc

def domainSetoid (S : Input A I) : Setoid (Set A) where
  r D E := Nonempty (PartialIso S D E)
  iseqv := ⟨fun D => ⟨PartialIso.identity S D⟩,
    fun ⟨p⟩ => ⟨p.inverse⟩, fun ⟨p⟩ ⟨q⟩ => ⟨q.comp p⟩⟩

abbrev Component (S : Input A I) := Quotient (domainSetoid S)
def classOf (S : Input A I) (D : Set A) : Component S := Quotient.mk (domainSetoid S) D

theorem class_eq {S : Input A I} {D E : Set A} (p : PartialIso S D E) :
    classOf S D = classOf S E := Quotient.sound ⟨p⟩

theorem representative_exists (S : Input A I) (q : Component S) :
    ∃ D : Set A, classOf S D = q := by
  refine Quotient.inductionOn q ?_
  intro D
  exact ⟨D, rfl⟩

def representative (S : Input A I) (q : Component S) : Set A :=
  Classical.choose (representative_exists S q)

theorem representative_class (S : Input A I) (q : Component S) :
    classOf S (representative S q) = q := Classical.choose_spec (representative_exists S q)

abbrev Object (S : Input A I) (q : Component S) := {D : Set A // classOf S D = q}

def transportIso (S : Input A I) (q : Component S) (D : Object S q) :
    PartialIso S (representative S q) D.val :=
  Classical.choice (Quotient.exact ((representative_class S q).trans D.property.symm))

def coordinates (S : Input A I) (q : Component S) (D : Object S q) :
    Atlas (representative S q) D.val := (transportIso S q D).toAtlas

def U (S : Input A I) (q : Component S) (D : Object S q) : BasePerm (Carrier A I) :=
  extension (transportIso S q D)

def Allowed (S : Input A I) (D : Set A) (p : BasePerm D) : Prop :=
  (∀ x y, S.owner (p.forward x).val = S.owner (p.forward y).val ↔ S.owner x.val = S.owner y.val) ∧
  (∀ x y, S.color (p.forward x).val (p.forward y).val = S.color x.val y.val)

def L (S : Input A I) (D : Set A) (p : BasePerm D) : BasePerm (Carrier A I) :=
  if hp : Allowed S D p then localLift ⟨p, hp.1, hp.2⟩ else BasePerm.identity _

theorem L_identity (S : Input A I) (D : Set A) :
    L S D (BasePerm.identity D) = BasePerm.identity (Carrier A I) := by
  have hid : Allowed S D (BasePerm.identity D) := ⟨fun _ _ => Iff.rfl, fun _ _ => rfl⟩
  rw [L, dif_pos hid]
  exact localLift_identity S D

theorem L_comp (S : Input A I) (D : Set A) (g f : BasePerm D)
    (hg : Allowed S D g) (hf : Allowed S D f) :
    L S D (g.comp f) = (L S D g).comp (L S D f) := by
  have hgf : Allowed S D (g.comp f) :=
    ⟨fun x y => (hg.1 (f.forward x) (f.forward y)).trans (hf.1 x y),
     fun x y => (hg.2 (f.forward x) (f.forward y)).trans (hf.2 x y)⟩
  rw [L, dif_pos hgf, L, dif_pos hg, L, dif_pos hf]
  exact localLift_comp (⟨g, hg.1, hg.2⟩ : LocalAut S D) ⟨f, hf.1, hf.2⟩

theorem L_extends (S : Input A I) (D : Set A) (p : BasePerm D)
    (hp : Allowed S D p) (d : D) :
    (L S D p).forward (inputCopy S d.val) = inputCopy S (p.forward d).val := by
  rw [L, dif_pos hp]
  exact localLift_extends ⟨p, hp.1, hp.2⟩ d

theorem L_color (S : Input A I) (D : Set A) (p : BasePerm D)
    (hp : Allowed S D p) (x y : Carrier A I) :
    label ((L S D p).forward x) ((L S D p).forward y) = label x y := by
  rw [L, dif_pos hp]
  exact localLift_color ⟨p, hp.1, hp.2⟩ x y

/-- Discharge admissibility for every normalized actual arrow. -/
theorem normalized_allowed (S : Input A I) (q : Component S) {D E : Object S q}
    (p : PartialIso S D.val E.val) :
    Allowed S (representative S q) (normalize (coordinates S q) p.toAtlas) := by
  let f := (transportIso S q E).inverse.comp (p.comp (transportIso S q D))
  exact ⟨f.part_iff, f.color_eq⟩

def componentLift (S : Input A I) (q : Component S) {D E : Object S q}
    (p : PartialIso S D.val E.val) : BasePerm (Carrier A I) :=
  assemble (coordinates S q) (U S q) (L S (representative S q)) p.toAtlas

theorem component_identity (S : Input A I) (q : Component S) (D : Object S q) :
    componentLift S q (PartialIso.identity S D.val) = BasePerm.identity (Carrier A I) := by
  exact assemble_identity (coordinates S q) (U S q) (L S (representative S q))
    (L_identity S (representative S q)) D

theorem component_comp (S : Input A I) (q : Component S) {D E F : Object S q}
    (r : PartialIso S E.val F.val) (p : PartialIso S D.val E.val) :
    componentLift S q (r.comp p) = (componentLift S q r).comp (componentLift S q p) := by
  exact assemble_comp (coordinates S q) (U S q) (L S (representative S q))
    (Allowed S (representative S q))
    (fun f g hf hg => L_comp S (representative S q) g f hg hf)
    r.toAtlas p.toAtlas (normalized_allowed S q p) (normalized_allowed S q r)

theorem component_extends (S : Input A I) (q : Component S) {D E : Object S q}
    (p : PartialIso S D.val E.val) (d : D.val) :
    (componentLift S q p).forward (inputCopy S d.val) = inputCopy S (p.map d).val := by
  exact assemble_extends (coordinates S q) (U S q) (L S (representative S q))
    (Allowed S (representative S q))
    (fun d : representative S q => inputCopy S d.val)
    (fun o (d : o.val) => inputCopy S d.val)
    (fun o d => extension_agrees (transportIso S q o) d)
    (L_extends S (representative S q)) p.toAtlas (normalized_allowed S q p) d

theorem component_color (S : Input A I) (q : Component S) {D E : Object S q}
    (p : PartialIso S D.val E.val) (x y : Carrier A I) :
    label ((componentLift S q p).forward x) ((componentLift S q p).forward y) = label x y := by
  have h := assemble_preserves_relation (coordinates S q) (U S q)
    (L S (representative S q)) (Allowed S (representative S q))
    (fun x y : Carrier A I => label x y = true)
    (fun o x y => by rw [show label ((U S q o).forward x) ((U S q o).forward y) = label x y from
      extension_color (transportIso S q o) x y])
    (fun f hf x y => by rw [L_color S (representative S q) f hf])
    p.toAtlas (normalized_allowed S q p) x y
  change (label ((componentLift S q p).forward x) ((componentLift S q p).forward y) = true) ↔
    label x y = true at h
  cases h1 : label ((componentLift S q p).forward x) ((componentLift S q p).forward y) <;>
    cases h2 : label x y <;> simp_all

def atComponent (S : Input A I) (q : Component S) (D E : Set A)
    (hD : classOf S D = q) (hE : classOf S E = q) (p : PartialIso S D E) :
    BasePerm (Carrier A I) := componentLift S q (D := ⟨D,hD⟩) (E := ⟨E,hE⟩) p

theorem atComponent_congr (S : Input A I) {q r : Component S} (h : q = r)
    (D E : Set A) (hD : classOf S D = q) (hE : classOf S E = q)
    (kD : classOf S D = r) (kE : classOf S E = r) (p : PartialIso S D E) :
    atComponent S q D E hD hE p = atComponent S r D E kD kE p := by
  cases h
  rfl

theorem atComponent_comp (S : Input A I) (q : Component S) (D E F : Set A)
    (hD : classOf S D = q) (hE : classOf S E = q) (hF : classOf S F = q)
    (r : PartialIso S E F) (p : PartialIso S D E) :
    atComponent S q D F hD hF (r.comp p) =
      (atComponent S q E F hE hF r).comp (atComponent S q D E hD hE p) :=
  component_comp S q (D := ⟨D,hD⟩) (E := ⟨E,hE⟩) (F := ⟨F,hF⟩) r p

def coherentLift (S : Input A I) {D E : Set A} (p : PartialIso S D E) :
    BasePerm (Carrier A I) :=
  atComponent S (classOf S D) D E rfl (class_eq p).symm p

theorem coherent_identity (S : Input A I) (D : Set A) :
    coherentLift S (PartialIso.identity S D) = BasePerm.identity (Carrier A I) :=
  component_identity S (classOf S D) ⟨D,rfl⟩

theorem coherent_comp (S : Input A I) {D E F : Set A}
    (r : PartialIso S E F) (p : PartialIso S D E) :
    coherentLift S (r.comp p) = (coherentLift S r).comp (coherentLift S p) := by
  let q := classOf S D
  have hE : classOf S E = q := (class_eq p).symm
  have hF : classOf S F = q := (class_eq r).symm.trans hE
  have hr : coherentLift S r = atComponent S q E F hE hF r :=
    atComponent_congr S (class_eq p).symm E F rfl (class_eq r).symm hE hF r
  calc
    coherentLift S (r.comp p) = atComponent S q D F rfl hF (r.comp p) := rfl
    _ = (atComponent S q E F hE hF r).comp (atComponent S q D E rfl hE p) :=
      atComponent_comp S q D E F rfl hE hF r p
    _ = (coherentLift S r).comp (coherentLift S p) := by rw [← hr]; rfl

theorem coherent_extends (S : Input A I) {D E : Set A} (p : PartialIso S D E) (d : D) :
    (coherentLift S p).forward (inputCopy S d.val) = inputCopy S (p.map d).val :=
  component_extends S (classOf S D) (D := ⟨D,rfl⟩) (E := ⟨E,(class_eq p).symm⟩) p d

theorem coherent_color (S : Input A I) {D E : Set A} (p : PartialIso S D E) (x y : Carrier A I) :
    label ((coherentLift S p).forward x) ((coherentLift S p).forward y) = label x y :=
  component_color S (classOf S D) (D := ⟨D,rfl⟩) (E := ⟨E,(class_eq p).symm⟩) p x y

theorem coherent_part (S : Input A I) {D E : Set A} (p : PartialIso S D E) (x y : Carrier A I) :
    ((coherentLift S p).forward x).1.1 = ((coherentLift S p).forward y).1.1 ↔ x.1.1 = y.1.1 := by
  have h := same_part_iff (witness (A := A) (I := I)) ((coherentLift S p).forward x)
    ((coherentLift S p).forward y)
  have k := same_part_iff (witness (A := A) (I := I)) x y
  change (((coherentLift S p).forward x).1.1 = ((coherentLift S p).forward y).1.1) ↔
    label ((coherentLift S p).forward x) ((coherentLift S p).forward y) = false ∧
    label ((coherentLift S p).forward y) ((coherentLift S p).forward x) = false at h
  rw [coherent_color, coherent_color] at h
  exact h.trans k.symm

/-- Full finite coherent EPPA for the concrete Boolean multipartite presentation.
Only the actual finite input is assumed. Empty domains are included; coherence
is the usual matching-range/domain composition law.
-/
theorem finite_coherent_eppa (S : Input A I) :
    Finite (Carrier A I) ∧
    ∃ T : Input (Carrier A I) I, ∃ j : A ↪ Carrier A I,
    ∃ F : (D E : Set A) → PartialIso S D E → BasePerm (Carrier A I),
      (∀ a b, T.color (j a) (j b) = S.color a b) ∧
      (∀ a b, T.owner (j a) = T.owner (j b) ↔ S.owner a = S.owner b) ∧
      Function.Surjective T.owner ∧
      (∀ D, F D D (PartialIso.identity S D) = BasePerm.identity (Carrier A I)) ∧
      (∀ D E H (p : PartialIso S D E) (q : PartialIso S E H),
        F D H (q.comp p) = (F E H q).comp (F D E p)) ∧
      (∀ D E (p : PartialIso S D E) (d : D), (F D E p).forward (j d.val) = j (p.map d).val) ∧
      (∀ D E (p : PartialIso S D E) x y,
        T.color ((F D E p).forward x) ((F D E p).forward y) = T.color x y) ∧
      (∀ D E (p : PartialIso S D E) x y,
        T.owner ((F D E p).forward x) = T.owner ((F D E p).forward y) ↔ T.owner x = T.owner y) := by
  refine ⟨carrier_finite, witness, inputCopy S, (fun _ _ p => coherentLift S p), ?_⟩
  exact ⟨inputCopy_color S, inputCopy_part S, witness_owner_surjective,
    coherent_identity S, fun _ _ _ p q => coherent_comp S q p,
    fun _ _ p d => coherent_extends S p d,
    fun _ _ p x y => coherent_color S p x y,
    fun _ _ p x y => coherent_part S p x y⟩

end
end GluingEPPA.Reducts.MultipartiteCoherentEPPA
