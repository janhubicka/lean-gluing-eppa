import GluingEPPA.Reducts.AnchorExtraction

/-! Actual symmetries of the augmented copies induce the real action,
anchor action and equivariance. No equivariant projection is assumed. -/
namespace GluingEPPA.Reducts.AnchorActions
open GluingEPPA.Reducts.AnchorExtraction
noncomputable section
universe u
variable {A V Z J : Type u} {e : A ↪ V}
variable {L : Rel A → Prop} {H : Equiv.Perm V → Prop}
variable (S : System e L H Z J)

structure Symmetry where
  perm : Equiv.Perm Z
  forward_copy : ∀ j, ∃ k, ∀ x, perm (S.copy j x) = S.copy k x
  backward_copy : ∀ j, ∃ k, ∀ x, perm.symm (S.copy j x) = S.copy k x
  anchor_iff : ∀ z, anchor S S.root (perm z) ↔ anchor S S.root z

namespace Symmetry
variable {S}
def identity : Symmetry S where
  perm := Equiv.refl Z
  forward_copy := fun j => ⟨j,fun _ => rfl⟩
  backward_copy := fun j => ⟨j,fun _ => rfl⟩
  anchor_iff := fun _ => Iff.rfl

def inverse (g : Symmetry S) : Symmetry S where
  perm := g.perm.symm
  forward_copy := g.backward_copy
  backward_copy := g.forward_copy
  anchor_iff := by
    intro z
    have h := g.anchor_iff (g.perm.symm z)
    simpa only [g.perm.apply_symm_apply] using h.symm

def comp (g f : Symmetry S) : Symmetry S where
  perm := f.perm.trans g.perm
  forward_copy := by
    intro j
    obtain ⟨k,hk⟩ := f.forward_copy j
    obtain ⟨l,hl⟩ := g.forward_copy k
    exact ⟨l,fun x => (congrArg g.perm (hk x)).trans (hl x)⟩
  backward_copy := by
    intro j
    obtain ⟨k,hk⟩ := g.backward_copy j
    obtain ⟨l,hl⟩ := f.backward_copy k
    exact ⟨l,fun x => (congrArg f.perm.symm (hk x)).trans (hl x)⟩
  anchor_iff := fun z => (g.anchor_iff (f.perm z)).trans (f.anchor_iff z)

theorem image_retained (g : Symmetry S) (j k : J) (hj : retained S j)
    (hk : ∀ x, g.perm (S.copy j x) = S.copy k x) : retained S k := by
  intro z
  constructor
  · rintro ⟨v,hv⟩
    have hs : S.copy j (.inr v) = g.perm.symm z := by
      calc
        S.copy j (.inr v) = g.perm.symm (g.perm (S.copy j (.inr v))) := (g.perm.symm_apply_apply _).symm
        _ = g.perm.symm z := congrArg g.perm.symm ((hk (.inr v)).trans hv)
    have hr := (hj _).1 ⟨v,hs⟩
    have ht := (g.anchor_iff (g.perm.symm z)).2 hr
    simpa only [g.perm.apply_symm_apply] using ht
  · intro hz
    have hr : anchor S S.root (g.perm.symm z) := by
      have ht := g.anchor_iff (g.perm.symm z)
      rw [g.perm.apply_symm_apply] at ht
      exact ht.1 hz
    obtain ⟨v,hv⟩ := (hj _).2 hr
    exact ⟨v,(hk (.inr v)).symm.trans ((congrArg g.perm hv).trans (g.perm.apply_symm_apply z))⟩

theorem maps_carrier (g : Symmetry S) (z : Z) (hz : carrier S z) : carrier S (g.perm z) := by
  obtain ⟨⟨j,a⟩,hj,ha⟩ := hz
  obtain ⟨k,hk⟩ := g.forward_copy j
  exact ⟨(k,a),g.image_retained j k hj hk,(hk (.inl a)).symm.trans (congrArg g.perm ha)⟩

def restrict (g : Symmetry S) : Equiv.Perm (Real S) where
  toFun y := ⟨g.perm y.val,g.maps_carrier y.val y.property⟩
  invFun y := ⟨g.perm.symm y.val,g.inverse.maps_carrier y.val y.property⟩
  left_inv := fun y => Subtype.ext (g.perm.symm_apply_apply y.val)
  right_inv := fun y => Subtype.ext (g.perm.apply_symm_apply y.val)

theorem restrict_chart (g : Symmetry S) (j k : J) (hj : retained S j)
    (hk : ∀ x, g.perm (S.copy j x) = S.copy k x) (a : A) :
    g.restrict (chart S j hj a) = chart S k (g.image_retained j k hj hk) a :=
  Subtype.ext (hk (.inl a))

theorem restrict_identity : (identity (S := S)).restrict = Equiv.refl (Real S) := by
  ext y
  rfl

theorem restrict_comp (g f : Symmetry S) :
    (g.comp f).restrict = f.restrict.trans g.restrict := by
  ext y
  rfl

variable [Nonempty V]
theorem anchor_action_exists (g : Symmetry S) :
    ∃ h : Equiv.Perm V, H h ∧ ∀ v,
      g.perm (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v)) := by
  obtain ⟨k,hk⟩ := g.forward_copy S.root
  have hr := g.image_retained S.root k (root_retained S) hk
  obtain ⟨h,hh,ha,hp⟩ := chart_has_ambient_label S k hr
  exact ⟨h,hh,fun v => (hk (.inr v)).trans (ha v)⟩

def anchorAction (g : Symmetry S) : Equiv.Perm V := Classical.choose g.anchor_action_exists

theorem anchorAction_mem (g : Symmetry S) : H g.anchorAction :=
  (Classical.choose_spec g.anchor_action_exists).1

theorem anchorAction_spec (g : Symmetry S) (v : V) :
    g.perm (S.copy S.root (.inr v)) = S.copy S.root (.inr (g.anchorAction v)) :=
  (Classical.choose_spec g.anchor_action_exists).2 v

theorem anchorAction_identity : (identity (S := S)).anchorAction = Equiv.refl V := by
  ext v
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  exact ((identity (S := S)).anchorAction_spec v).symm

theorem anchorAction_comp (g f : Symmetry S) :
    (g.comp f).anchorAction = f.anchorAction.trans g.anchorAction := by
  ext v
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  calc
    S.copy S.root (.inr ((g.comp f).anchorAction v)) =
      g.perm (f.perm (S.copy S.root (.inr v))) := ((g.comp f).anchorAction_spec v).symm
    _ = g.perm (S.copy S.root (.inr (f.anchorAction v))) := congrArg g.perm (f.anchorAction_spec v)
    _ = S.copy S.root (.inr (g.anchorAction (f.anchorAction v))) := g.anchorAction_spec _

theorem projection_equivariant (g : Symmetry S) (y : Real S) :
    projection S (g.restrict y) = g.anchorAction (projection S y) := by
  obtain ⟨⟨j,a⟩,hj,ha⟩ := y.property
  have hy : chart S j hj a = y := Subtype.ext ha
  rw [← hy]
  obtain ⟨k,hk⟩ := g.forward_copy j
  rw [g.restrict_chart j k hj hk]
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  calc
    S.copy S.root (.inr (projection S (chart S k (g.image_retained j k hj hk) a))) =
      S.copy k (.inr (e a)) := projection_anchor S k _ a
    _ = g.perm (S.copy j (.inr (e a))) := (hk (.inr (e a))).symm
    _ = g.perm (S.copy S.root (.inr (projection S (chart S j hj a)))) :=
      congrArg g.perm (projection_anchor S j hj a).symm
    _ = S.copy S.root (.inr (g.anchorAction (projection S (chart S j hj a)))) :=
      g.anchorAction_spec _

theorem faithful_dependence (hsurj : Function.Surjective (projection S))
    (g f : Symmetry S) (heq : g.restrict = f.restrict) : g.anchorAction = f.anchorAction := by
  ext v
  obtain ⟨y,rfl⟩ := hsurj v
  rw [← g.projection_equivariant y, ← f.projection_equivariant y, heq]
end Symmetry

def symmetryOfExtension (p : Equiv.Perm Z)
    (hf : ∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x)
    (hb : ∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)
    (h : Equiv.Perm V)
    (ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v))) : Symmetry S where
  perm := p
  forward_copy := hf
  backward_copy := hb
  anchor_iff := by
    intro z
    constructor
    · rintro ⟨v,hv⟩
      refine ⟨h.symm v, p.injective ?_⟩
      exact (ha (h.symm v)).trans ((congrArg (fun w => S.copy S.root (.inr w)) (h.apply_symm_apply v)).trans hv)
    · rintro ⟨v,hv⟩
      exact ⟨h v,(ha v).symm.trans (congrArg p hv)⟩

theorem restricted_extension (p : Equiv.Perm Z)
    (hf : ∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x)
    (hb : ∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)
    (h : Equiv.Perm V)
    (ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v)))
    (f : Rel A) (hext : ∀ a b, f a b → p (S.copy S.root (.inl a)) = S.copy S.root (.inl b)) :
    ∀ a b, f a b → (symmetryOfExtension S p hf hb h ha).restrict
      (chart S S.root (root_retained S) a) = chart S S.root (root_retained S) b := by
  intro a b hab
  exact Subtype.ext (hext a b hab)
end
end GluingEPPA.Reducts.AnchorActions
