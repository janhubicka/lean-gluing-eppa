import GluingEPPA.Steiner.ChainValuation.MatchingGluing

/-!
# Matching of component classes from exact attachment pullback

Suppose two labelled pieces are glued along a common parameter space Z.
The precise condition for their *component classes* to meet in a matching
is that the old and new connectivity relations agree upon pullback to Z.
This module constructs that matching rather than postulating it.

It is independent of cosets and group actions, and will later be applied
to the actual restricted Cayley components. It does not assert that the
pullback agreement holds for an arbitrary chain: that is the remaining
geometric induction obligation.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-- An old component and a new component are attached precisely if some
point in the attaching space has those two component classes. -/
def AttachmentComponentPair
    (RX : Setoid X) (RY : Setoid Y) (f : Z → X) (g : Z → Y)
    (x : Quotient RX) (y : Quotient RY) : Prop :=
  ∃ z : Z, Quotient.mk RX (f z) = x ∧ Quotient.mk RY (g z) = y

/-- Equal old component classes at two attachment points force equal new
classes whenever the pullbacks of the two equivalence relations agree. -/
theorem attachmentPair_new_unique
    (RX : Setoid X) (RY : Setoid Y) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z, RX.r (f z) (f z') ↔ RY.r (g z) (g z'))
    {x : Quotient RX} {y y' : Quotient RY}
    (h : AttachmentComponentPair RX RY f g x y)
    (h' : AttachmentComponentPair RX RY f g x y') : y = y' := by
  obtain ⟨z, hzX, hzY⟩ := h
  obtain ⟨z', hzX', hzY'⟩ := h'
  have hx : RX.r (f z) (f z') :=
    Quotient.exact (hzX.trans hzX'.symm)
  have hy : Quotient.mk RY (g z) = Quotient.mk RY (g z') :=
    Quotient.sound ((hpull z z').mp hx)
  exact hzY.symm.trans (hy.trans hzY')

/-- The symmetric no-splitting assertion on the new component side. -/
theorem attachmentPair_old_unique
    (RX : Setoid X) (RY : Setoid Y) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z, RX.r (f z) (f z') ↔ RY.r (g z) (g z'))
    {x x' : Quotient RX} {y : Quotient RY}
    (h : AttachmentComponentPair RX RY f g x y)
    (h' : AttachmentComponentPair RX RY f g x' y) : x = x' := by
  obtain ⟨z, hzX, hzY⟩ := h
  obtain ⟨z', hzX', hzY'⟩ := h'
  have hy : RY.r (g z) (g z') :=
    Quotient.exact (hzY.trans hzY'.symm)
  have hx : Quotient.mk RX (f z) = Quotient.mk RX (f z') :=
    Quotient.sound ((hpull z z').mpr hy)
  exact hzX.symm.trans (hx.trans hzX')

/-- A pair of component quotients forms a bipartite matching once the
attachment components agree on the common attaching space. -/
def canonicalAttachmentMatching
    (RX : Setoid X) (RY : Setoid Y) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z, RX.r (f z) (f z') ↔ RY.r (g z) (g z')) :
    Matching (Sum (Quotient RX) (Quotient RY)) where
  Rel x y :=
    match x, y with
    | .inl a, .inr b => AttachmentComponentPair RX RY f g a b
    | .inr b, .inl a => AttachmentComponentPair RX RY f g a b
    | _, _ => False
  symm := by
    intro x y hxy
    cases x <;> cases y <;> exact hxy
  unique := by
    intro x y z hxy hxz
    cases x with
    | inl a =>
        cases y with
        | inl _ => cases hxy
        | inr b =>
            cases z with
            | inl _ => cases hxz
            | inr c =>
                congr 1
                exact attachmentPair_new_unique RX RY f g hpull hxy hxz
    | inr b =>
        cases y with
        | inr _ => cases hxy
        | inl a =>
            cases z with
            | inr _ => cases hxz
            | inl c =>
                congr 1
                exact attachmentPair_old_unique RX RY f g hpull hxy hxz

/-- With exact pullback compatibility, the generated glued connectivity
is exactly the matching quotient of component classes. -/
theorem gluedReach_iff_canonical_matching
    (RX : Setoid X) (RY : Setoid Y) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z, RX.r (f z) (f z') ↔ RY.r (g z) (g z'))
    (a b : Sum X Y) :
    GluedReach RX RY f g a b ↔
      componentClass RX RY (canonicalAttachmentMatching RX RY f g hpull) a =
        componentClass RX RY (canonicalAttachmentMatching RX RY f g hpull) b := by
  apply gluedReach_iff_matching_class_eq
    RX RY f g (canonicalAttachmentMatching RX RY f g hpull)
  · intro z
    exact ⟨z, rfl, rfl⟩
  · intro x x' h
    exact h
  · intro y y' h
    exact h
  · intro x y h
    exact h

/-- No two old connectivity classes can be merged by the quotient gluing
when old and new connectivity agree at all attachment points. -/
theorem gluedReach_old_reflect
    (RX : Setoid X) (RY : Setoid Y) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z, RX.r (f z) (f z') ↔ RY.r (g z) (g z'))
    {x x' : X}
    (h : GluedReach RX RY f g (.inl x) (.inl x')) :
    RX.r x x' := by
  let T := canonicalAttachmentMatching RX RY f g hpull
  have hclass :=
    (gluedReach_iff_canonical_matching RX RY f g hpull
      (.inl x) (.inl x')).mp h
  have hinj : Function.Injective
      (fun a : Quotient RX =>
        Quotient.mk T.componentSetoid (Sum.inl a)) :=
    T.inl_component_injective (by intro a b hab; exact hab)
  exact Quotient.exact (hinj hclass)

/-- Symmetrically, one glued component cannot contain two distinct new
component classes. -/
theorem gluedReach_new_reflect
    (RX : Setoid X) (RY : Setoid Y) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z, RX.r (f z) (f z') ↔ RY.r (g z) (g z'))
    {y y' : Y}
    (h : GluedReach RX RY f g (.inr y) (.inr y')) :
    RY.r y y' := by
  let T := canonicalAttachmentMatching RX RY f g hpull
  have hclass :=
    (gluedReach_iff_canonical_matching RX RY f g hpull
      (.inr y) (.inr y')).mp h
  have hinj : Function.Injective
      (fun a : Quotient RY =>
        Quotient.mk T.componentSetoid (Sum.inr a)) :=
    T.inr_component_injective (by intro a b hab; exact hab)
  exact Quotient.exact (hinj hclass)

end GluingEPPA.Steiner.ChainValuation
