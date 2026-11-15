import GluingEPPA.Reducts.AnchorExtraction

/-! The decorated family contains every compatible ambient lift, as well as the
true empty graph. Natural-domain composition and inversion are proved closed.
No arbitrary restriction-closure is used. -/
namespace GluingEPPA.Reducts.AnchorFamily
open GluingEPPA.Reducts.AnchorExtraction
universe u
variable {A V : Type u}

def relId (X : Type u) : Rel X := fun x y => x = y
def relInv {X : Type u} (f : Rel X) : Rel X := fun x y => f y x
def relComp {X : Type u} (f g : Rel X) : Rel X := fun x z => ∃ y, f x y ∧ g y z

def PartialBijection {X : Type u} (f : Rel X) : Prop :=
  (∀ x y z, f x y → f x z → y = z) ∧ (∀ x y z, f x z → f y z → x = y)

theorem decorated_partial (f : Rel A) (h : Equiv.Perm V) (hf : PartialBijection f) :
    PartialBijection (decorated f h) := by
  constructor
  · intro x y z hxy hxz
    cases x <;> cases y <;> cases z <;> simp only [decorated] at hxy hxz
    all_goals try contradiction
    · exact congrArg Sum.inl (hf.1 _ _ _ hxy hxz)
    · exact congrArg Sum.inr (hxy.symm.trans hxz)
  · intro x y z hxz hyz
    cases x <;> cases y <;> cases z <;> simp only [decorated] at hxz hyz
    all_goals try contradiction
    · exact congrArg Sum.inl (hf.2 _ _ _ hxz hyz)
    · exact congrArg Sum.inr (h.injective (hxz.trans hyz.symm))

theorem decorated_inverse (f : Rel A) (h : Equiv.Perm V) :
    relInv (decorated f h) = decorated (relInv f) h.symm := by
  funext x y
  apply propext
  cases x with
  | inl a => cases y <;> exact Iff.rfl
  | inr v =>
    cases y with
    | inl a => exact Iff.rfl
    | inr w =>
      change (h w = v) ↔ h.symm v = w
      constructor
      · intro hv
        exact (congrArg h.symm hv).symm.trans (h.symm_apply_apply w)
      · intro hv
        exact (congrArg h hv).symm.trans (h.apply_symm_apply v)

theorem decorated_comp (f g : Rel A) (h k : Equiv.Perm V) :
    relComp (decorated f h) (decorated g k) = decorated (relComp f g) (h.trans k) := by
  funext x z
  apply propext
  cases x with
  | inl a =>
    cases z with
    | inl b =>
      constructor
      · rintro ⟨y,hy,hz⟩
        cases y with
        | inl c => exact ⟨c,hy,hz⟩
        | inr v => exact False.elim hy
      · rintro ⟨c,hc,hd⟩
        exact ⟨.inl c,hc,hd⟩
    | inr v =>
      constructor
      · rintro ⟨y,hy,hz⟩
        cases y with
        | inl c => exact hz
        | inr w => exact hy
      · intro hf
        exact False.elim hf
  | inr v =>
    cases z with
    | inl a =>
      constructor
      · rintro ⟨y,hy,hz⟩
        cases y with
        | inl c => exact hy
        | inr w => exact hz
      · intro hf
        exact False.elim hf
    | inr w =>
      constructor
      · rintro ⟨y,hy,hz⟩
        cases y with
        | inl c => exact False.elim hy
        | inr t => exact (congrArg k hy).trans hz
      · intro hw
        exact ⟨.inr (h v),rfl,hw⟩

theorem compatible_inverse (e : A ↪ V) (f : Rel A) (h : Equiv.Perm V)
    (hc : Compatible e f h) : Compatible e (relInv f) h.symm := by
  intro a b hab
  exact (congrArg h.symm (hc b a hab)).symm.trans (h.symm_apply_apply (e b))

theorem compatible_comp (e : A ↪ V) (f g : Rel A) (h k : Equiv.Perm V)
    (hf : Compatible e f h) (hg : Compatible e g k) :
    Compatible e (relComp f g) (h.trans k) := by
  rintro a c ⟨b,hab,hbc⟩
  exact (congrArg k (hf a b hab)).trans (hg b c hbc)

theorem allowed_empty (e : A ↪ V) (L : Rel A → Prop) (H : Equiv.Perm V → Prop) :
    Allowed e L H (emptyRel (Sum A V)) := Or.inl rfl

theorem allowed_identity (e : A ↪ V) (L : Rel A → Prop) (H : Equiv.Perm V → Prop)
    (hl : L (relId A)) (hh : H (Equiv.refl V)) : Allowed e L H (relId (Sum A V)) := by
  refine Or.inr ⟨relId A,hl,Equiv.refl V,hh,?_,?_⟩
  · intro a b hab
    exact congrArg e hab
  · funext x y
    apply propext
    cases x <;> cases y <;> simp [relId,decorated]

theorem allowed_inverse (e : A ↪ V) (L : Rel A → Prop) (H : Equiv.Perm V → Prop)
    (hl : ∀ f, L f → L (relInv f)) (hh : ∀ h, H h → H h.symm)
    (r : Rel (Sum A V)) (hr : Allowed e L H r) : Allowed e L H (relInv r) := by
  rcases hr with rfl | ⟨f,hf,h,hH,hc,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨relInv f,hl f hf,h.symm,hh h hH,compatible_inverse e f h hc,decorated_inverse f h⟩

theorem allowed_composition (e : A ↪ V) (L : Rel A → Prop) (H : Equiv.Perm V → Prop)
    (hl : ∀ f g, L f → L g → L (relComp f g))
    (hh : ∀ h k, H h → H k → H (h.trans k))
    (r s : Rel (Sum A V)) (hr : Allowed e L H r) (hs : Allowed e L H s) :
    Allowed e L H (relComp r s) := by
  rcases hr with rfl | ⟨f,hf,h,hH,hc,rfl⟩
  · left
    funext x y
    simp [relComp,emptyRel]
  · rcases hs with rfl | ⟨g,hg,k,hK,kc,rfl⟩
    · left
      funext x y
      simp [relComp,emptyRel]
    · exact Or.inr ⟨relComp f g,hl f g hf hg,h.trans k,hh h k hH hK,
        compatible_comp e f g h k hc kc,decorated_comp f g h k⟩

theorem allowed_partial (e : A ↪ V) (L : Rel A → Prop) (H : Equiv.Perm V → Prop)
    (hl : ∀ f, L f → PartialBijection f)
    (r : Rel (Sum A V)) (hr : Allowed e L H r) : PartialBijection r := by
  rcases hr with rfl | ⟨f,hf,h,hH,hc,rfl⟩
  · exact ⟨fun _ _ _ hf => False.elim hf,fun _ _ _ hf => False.elim hf⟩
  · exact decorated_partial f h (hl f hf)

end GluingEPPA.Reducts.AnchorFamily
