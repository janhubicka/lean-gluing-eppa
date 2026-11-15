import GluingEPPA.Reducts.AnchorActions
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Basic

/-! Actual image groups and a surjective homomorphism after faithful descent.
The subgroup is formed from permutations of the augmented realization;
its real and anchor representations come from AnchorActions, not hypotheses.
-/
namespace GluingEPPA.Reducts.AnchorGroupDescent
open GluingEPPA.Reducts.AnchorExtraction
open GluingEPPA.Reducts.AnchorActions

noncomputable section
universe u
variable {A V Z J : Type u} {e : A ↪ V}
variable {L : Rel A → Prop} {H : Equiv.Perm V → Prop}
variable (S : System e L H Z J)

theorem symmetry_ext (g f : Symmetry S) (h : g.perm = f.perm) : g = f := by
  cases g
  cases f
  cases h
  rfl

def stabilizer : Subgroup (Equiv.Perm Z) where
  carrier := {p | ∃ g : Symmetry S, g.perm = p}
  one_mem' := ⟨Symmetry.identity,rfl⟩
  mul_mem' := by
    rintro p q ⟨g,rfl⟩ ⟨f,rfl⟩
    exact ⟨g.comp f,rfl⟩
  inv_mem' := by
    rintro p ⟨g,rfl⟩
    exact ⟨g.inverse,rfl⟩

def chosen (g : S.stabilizer) : Symmetry S := Classical.choose g.property

theorem chosen_perm (g : S.stabilizer) : (S.chosen g).perm = g.val :=
  Classical.choose_spec g.property

theorem chosen_one : S.chosen 1 = Symmetry.identity := by
  apply S.symmetry_ext
  exact S.chosen_perm 1

theorem chosen_mul (g f : S.stabilizer) : S.chosen (g*f) = (S.chosen g).comp (S.chosen f) := by
  apply S.symmetry_ext
  rw [S.chosen_perm]
  change g.val * f.val = (S.chosen g).perm * (S.chosen f).perm
  rw [S.chosen_perm,S.chosen_perm]

def realHom : S.stabilizer →* Equiv.Perm S.Real where
  toFun g := (S.chosen g).restrict
  map_one' := by rw [S.chosen_one,Symmetry.restrict_identity]; rfl
  map_mul' := by
    intro g f
    rw [S.chosen_mul,Symmetry.restrict_comp]
    rfl

variable [Nonempty V]

def anchorHom : S.stabilizer →* Equiv.Perm V where
  toFun g := (S.chosen g).anchorAction
  map_one' := by rw [S.chosen_one,Symmetry.anchorAction_identity]; rfl
  map_mul' := by
    intro g f
    rw [S.chosen_mul,Symmetry.anchorAction_comp]
    rfl

theorem hom_equivariant (g : S.stabilizer) (y : S.Real) :
    S.projection (S.realHom g y) = S.anchorHom g (S.projection y) :=
  (S.chosen g).projection_equivariant y

def imageLift (p : S.realHom.range) : S.stabilizer := Classical.choose p.property

theorem imageLift_spec (p : S.realHom.range) : S.realHom (S.imageLift p) = p.val :=
  Classical.choose_spec p.property

def descendedMap (p : S.realHom.range) : S.anchorHom.range :=
  ⟨S.anchorHom (S.imageLift p),⟨S.imageLift p,rfl⟩⟩

theorem descended_equivariant (p : S.realHom.range) (y : S.Real) :
    S.projection (p.val y) = (S.descendedMap p).val (S.projection y) := by
  rw [← S.imageLift_spec p]
  exact S.hom_equivariant (S.imageLift p) y

/-- Surjectivity makes the anchor action independent of the chosen preimage. -/
def descent (hsurj : Function.Surjective S.projection) : S.realHom.range →* S.anchorHom.range where
  toFun := S.descendedMap
  map_one' := by
    apply Subtype.ext
    ext v
    obtain ⟨y,rfl⟩ := hsurj v
    exact (S.descended_equivariant 1 y).symm
  map_mul' := by
    intro p q
    apply Subtype.ext
    ext v
    obtain ⟨y,rfl⟩ := hsurj v
    calc
      (S.descendedMap (p*q)).val (S.projection y) = S.projection ((p*q).val y) :=
        (S.descended_equivariant (p*q) y).symm
      _ = S.projection (p.val (q.val y)) := rfl
      _ = (S.descendedMap p).val (S.projection (q.val y)) := S.descended_equivariant p (q.val y)
      _ = (S.descendedMap p).val ((S.descendedMap q).val (S.projection y)) :=
        congrArg (S.descendedMap p).val (S.descended_equivariant q y)

theorem descent_surjective (hsurj : Function.Surjective S.projection) :
    Function.Surjective (S.descent hsurj) := by
  intro h
  obtain ⟨g,hg⟩ := h.property
  let p : S.realHom.range := ⟨S.realHom g,⟨g,rfl⟩⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  ext v
  obtain ⟨y,rfl⟩ := hsurj v
  calc
    (S.descent hsurj p).val (S.projection y) = S.projection (p.val y) :=
      (S.descended_equivariant p y).symm
    _ = S.anchorHom g (S.projection y) := S.hom_equivariant g y
    _ = h.val (S.projection y) := congrArg (fun t : Equiv.Perm V => t (S.projection y)) hg

theorem anchor_range_allowed (h : S.anchorHom.range) : H h.val := by
  obtain ⟨g,hg⟩ := h.property
  rw [← hg]
  exact (S.chosen g).anchorAction_mem

def stabilizerOfSymmetry (g : Symmetry S) : S.stabilizer := ⟨g.perm,⟨g,rfl⟩⟩

theorem chosen_of_symmetry (g : Symmetry S) : S.chosen (S.stabilizerOfSymmetry g) = g := by
  apply S.symmetry_ext
  exact S.chosen_perm _

theorem supplied_anchor_action (p : Equiv.Perm Z)
    (hf : ∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x)
    (hb : ∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)
    (h : Equiv.Perm V)
    (ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v))) :
    (S.symmetryOfExtension p hf hb h ha).anchorAction = h := by
  ext v
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  exact ((S.symmetryOfExtension p hf hb h ha).anchorAction_spec v).symm.trans (ha v)

/-- Extension of every anchor-only map makes the image exactly the intended
ambient permutation group, not merely an unspecified subgroup of it. -/
theorem ambient_in_anchor_range
    (h : Equiv.Perm V)
    (p : Equiv.Perm Z)
    (hf : ∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x)
    (hb : ∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)
    (ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v))) :
    h ∈ S.anchorHom.range := by
  let g := S.symmetryOfExtension p hf hb h ha
  refine ⟨S.stabilizerOfSymmetry g, ?_⟩
  change (S.chosen (S.stabilizerOfSymmetry g)).anchorAction = h
  rw [S.chosen_of_symmetry]
  exact S.supplied_anchor_action p hf hb h ha

theorem real_group_extends
    (p : Equiv.Perm Z)
    (hf : ∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x)
    (hb : ∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)
    (h : Equiv.Perm V)
    (ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v)))
    (f : Rel A) (hext : ∀ a b, f a b → p (S.copy S.root (.inl a)) = S.copy S.root (.inl b)) :
    ∃ q : S.realHom.range, ∀ a b, f a b →
      q.val (S.chart S.root S.root_retained a) = S.chart S.root S.root_retained b := by
  let g := S.symmetryOfExtension p hf hb h ha
  let t := S.stabilizerOfSymmetry g
  refine ⟨⟨S.realHom t,⟨t,rfl⟩⟩, ?_⟩
  intro a b hab
  change (S.chosen (S.stabilizerOfSymmetry g)).restrict (S.chart S.root S.root_retained a) = _
  rw [S.chosen_of_symmetry]
  exact S.restricted_extension p hf hb h ha f hext a b hab

/-- Transitivity on retained copies is inherited from raw augmented-copy
transporters; preservation of the anchor is proved, not requested. -/
theorem retained_transporter (j k : J) (hj : S.retained j) (hk : S.retained k)
    (p : Equiv.Perm Z)
    (hf : ∀ l, ∃ m, ∀ x, p (S.copy l x) = S.copy m x)
    (hb : ∀ l, ∃ m, ∀ x, p.symm (S.copy l x) = S.copy m x)
    (hjk : ∀ x, p (S.copy j x) = S.copy k x) :
    ∃ q : S.realHom.range, ∀ a, q.val (S.chart j hj a) = S.chart k hk a := by
  obtain ⟨h,hH,ha,he⟩ := S.chart_has_ambient_label j hj
  obtain ⟨t,tH,ta,te⟩ := S.chart_has_ambient_label k hk
  let u := h.symm.trans t
  have hu : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (u v)) := by
    intro v
    have hpre : S.copy j (.inr (h.symm v)) = S.copy S.root (.inr v) :=
      (ha (h.symm v)).trans (congrArg (fun w => S.copy S.root (.inr w)) (h.apply_symm_apply v))
    exact (congrArg p hpre.symm).trans ((hjk (.inr (h.symm v))).trans (ta (h.symm v)))
  let g := S.symmetryOfExtension p hf hb u hu
  let z := S.stabilizerOfSymmetry g
  refine ⟨⟨S.realHom z,⟨z,rfl⟩⟩, ?_⟩
  intro a
  change (S.chosen (S.stabilizerOfSymmetry g)).restrict (S.chart j hj a) = _
  rw [S.chosen_of_symmetry]
  exact Subtype.ext (hjk (.inl a))

theorem restriction_preserves_composition (g f k : Symmetry S)
    (h : k.perm = f.perm.trans g.perm) : k.restrict = f.restrict.trans g.restrict := by
  have he : k = g.comp f := S.symmetry_ext k (g.comp f) h
  rw [he,Symmetry.restrict_comp]

end
end GluingEPPA.Reducts.AnchorGroupDescent
