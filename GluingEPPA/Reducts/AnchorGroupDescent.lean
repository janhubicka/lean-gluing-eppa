import GluingEPPA.Reducts.AnchorActions
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Basic

/-! Faithful image groups and descended epimorphism, constructed from
symmetries of the incoming augmented realization. -/
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

def chosen (g : stabilizer S) : Symmetry S := Classical.choose g.property
theorem chosen_perm (g : stabilizer S) : (chosen S g).perm = g.val :=
  Classical.choose_spec g.property

theorem chosen_one : chosen S 1 = Symmetry.identity := by
  apply symmetry_ext S
  exact chosen_perm S 1

theorem chosen_mul (g f : stabilizer S) : chosen S (g*f) = (chosen S g).comp (chosen S f) := by
  apply symmetry_ext S
  rw [chosen_perm S]
  change g.val * f.val = (chosen S g).perm * (chosen S f).perm
  rw [chosen_perm S,chosen_perm S]

def realHom : stabilizer S →* Equiv.Perm (Real S) where
  toFun g := (chosen S g).restrict
  map_one' := by rw [chosen_one S,Symmetry.restrict_identity]; rfl
  map_mul' := by
    intro g f
    rw [chosen_mul S,Symmetry.restrict_comp]
    rfl

variable [Nonempty V]
def anchorHom : stabilizer S →* Equiv.Perm V where
  toFun g := (chosen S g).anchorAction
  map_one' := by rw [chosen_one S,Symmetry.anchorAction_identity]; rfl
  map_mul' := by
    intro g f
    rw [chosen_mul S,Symmetry.anchorAction_comp]
    rfl

theorem hom_equivariant (g : stabilizer S) (y : Real S) :
    projection S (realHom S g y) = anchorHom S g (projection S y) :=
  (chosen S g).projection_equivariant y

def imageLift (p : (realHom S).range) : stabilizer S := Classical.choose p.property
theorem imageLift_spec (p : (realHom S).range) : realHom S (imageLift S p) = p.val :=
  Classical.choose_spec p.property

def descendedMap (p : (realHom S).range) : (anchorHom S).range :=
  ⟨anchorHom S (imageLift S p),⟨imageLift S p,rfl⟩⟩

theorem descended_equivariant (p : (realHom S).range) (y : Real S) :
    projection S (p.val y) = (descendedMap S p).val (projection S y) := by
  rw [← imageLift_spec S p]
  exact hom_equivariant S (imageLift S p) y

def descent (hsurj : Function.Surjective (projection S)) :
    (realHom S).range →* (anchorHom S).range where
  toFun := descendedMap S
  map_one' := by
    apply Subtype.ext
    ext v
    obtain ⟨y,rfl⟩ := hsurj v
    exact (descended_equivariant S 1 y).symm
  map_mul' := by
    intro p q
    apply Subtype.ext
    ext v
    obtain ⟨y,rfl⟩ := hsurj v
    calc
      (descendedMap S (p*q)).val (projection S y) = projection S ((p*q).val y) :=
        (descended_equivariant S (p*q) y).symm
      _ = projection S (p.val (q.val y)) := rfl
      _ = (descendedMap S p).val (projection S (q.val y)) := descended_equivariant S p (q.val y)
      _ = (descendedMap S p).val ((descendedMap S q).val (projection S y)) :=
        congrArg (descendedMap S p).val (descended_equivariant S q y)

theorem descent_surjective (hsurj : Function.Surjective (projection S)) :
    Function.Surjective (descent S hsurj) := by
  intro h
  obtain ⟨g,hg⟩ := h.property
  let p : (realHom S).range := ⟨realHom S g,⟨g,rfl⟩⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  ext v
  obtain ⟨y,rfl⟩ := hsurj v
  calc
    (descent S hsurj p).val (projection S y) = projection S (p.val y) :=
      (descended_equivariant S p y).symm
    _ = anchorHom S g (projection S y) := hom_equivariant S g y
    _ = h.val (projection S y) := congrArg (fun t : Equiv.Perm V => t (projection S y)) hg

theorem anchor_range_allowed (h : (anchorHom S).range) : H h.val := by
  obtain ⟨g,hg⟩ := h.property
  rw [← hg]
  exact (chosen S g).anchorAction_mem

def stabilizerOfSymmetry (g : Symmetry S) : stabilizer S := ⟨g.perm,⟨g,rfl⟩⟩
theorem chosen_of_symmetry (g : Symmetry S) : chosen S (stabilizerOfSymmetry S g) = g := by
  apply symmetry_ext S
  exact chosen_perm S _

theorem supplied_anchor_action (p : Equiv.Perm Z)
    (hf : ∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x)
    (hb : ∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)
    (h : Equiv.Perm V)
    (ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v))) :
    (symmetryOfExtension S p hf hb h ha).anchorAction = h := by
  ext v
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  exact ((symmetryOfExtension S p hf hb h ha).anchorAction_spec v).symm.trans (ha v)

theorem ambient_in_anchor_range (h : Equiv.Perm V) (p : Equiv.Perm Z)
    (hf : ∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x)
    (hb : ∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)
    (ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v))) :
    h ∈ (anchorHom S).range := by
  let g := symmetryOfExtension S p hf hb h ha
  refine ⟨stabilizerOfSymmetry S g, ?_⟩
  change (chosen S (stabilizerOfSymmetry S g)).anchorAction = h
  rw [chosen_of_symmetry S]
  exact supplied_anchor_action S p hf hb h ha

theorem real_group_extends (p : Equiv.Perm Z)
    (hf : ∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x)
    (hb : ∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)
    (h : Equiv.Perm V)
    (ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v)))
    (f : Rel A) (hext : ∀ a b, f a b → p (S.copy S.root (.inl a)) = S.copy S.root (.inl b)) :
    ∃ q : (realHom S).range, ∀ a b, f a b →
      q.val (chart S S.root (root_retained S) a) = chart S S.root (root_retained S) b := by
  let g := symmetryOfExtension S p hf hb h ha
  let t := stabilizerOfSymmetry S g
  refine ⟨⟨realHom S t,⟨t,rfl⟩⟩, ?_⟩
  intro a b hab
  change (chosen S (stabilizerOfSymmetry S g)).restrict (chart S S.root (root_retained S) a) = _
  rw [chosen_of_symmetry S]
  exact restricted_extension S p hf hb h ha f hext a b hab

theorem retained_transporter (j k : J) (hj : retained S j) (hk : retained S k)
    (p : Equiv.Perm Z)
    (hf : ∀ l, ∃ m, ∀ x, p (S.copy l x) = S.copy m x)
    (hb : ∀ l, ∃ m, ∀ x, p.symm (S.copy l x) = S.copy m x)
    (hjk : ∀ x, p (S.copy j x) = S.copy k x) :
    ∃ q : (realHom S).range, ∀ a, q.val (chart S j hj a) = chart S k hk a := by
  obtain ⟨h,hH,ha,he⟩ := chart_has_ambient_label S j hj
  obtain ⟨t,tH,ta,te⟩ := chart_has_ambient_label S k hk
  let u := h.symm.trans t
  have hu : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (u v)) := by
    intro v
    have hpre : S.copy j (.inr (h.symm v)) = S.copy S.root (.inr v) :=
      (ha (h.symm v)).trans (congrArg (fun w => S.copy S.root (.inr w)) (h.apply_symm_apply v))
    exact (congrArg p hpre.symm).trans ((hjk (.inr (h.symm v))).trans (ta (h.symm v)))
  let g := symmetryOfExtension S p hf hb u hu
  let z := stabilizerOfSymmetry S g
  refine ⟨⟨realHom S z,⟨z,rfl⟩⟩, ?_⟩
  intro a
  change (chosen S (stabilizerOfSymmetry S g)).restrict (chart S j hj a) = _
  rw [chosen_of_symmetry S]
  exact Subtype.ext (hjk (.inl a))

theorem restriction_preserves_composition (g f k : Symmetry S)
    (h : k.perm = f.perm.trans g.perm) : k.restrict = f.restrict.trans g.restrict := by
  have he : k = g.comp f := symmetry_ext S k (g.comp f) h
  rw [he,Symmetry.restrict_comp]
end
end GluingEPPA.Reducts.AnchorGroupDescent
