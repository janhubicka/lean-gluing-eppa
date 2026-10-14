import GluingEPPA.Sparsening.CompleteChartGraph

/-! The canonical finite atlas: actual closed subsets contained in the orbit
of one distinguished root. No embedding presentations or duplicate copies
are used as chart indices. No EPPA or transitivity conclusion is assumed. -/
namespace GluingEPPA.Sparsening.OrbitAtlas
universe u v w
variable {L : Nat → Type u} {A : Type v} {F : Type w}

structure Aut (R : RelStructure L A) (out : F → A → Set A) where
  perm : A ≃ A
  rel_iff : ∀ {n} (r : L n) (x : Fin n → A),
    R.rel r (fun i => perm (x i)) ↔ R.rel r x
  unary_iff : ∀ f x y, perm y ∈ out f (perm x) ↔ y ∈ out f x

namespace Aut
variable {R : RelStructure L A} {out : F → A → Set A}

def refl : Aut R out where
  perm := Equiv.refl A
  rel_iff _ _ := Iff.rfl
  unary_iff _ _ _ := Iff.rfl

def symm (h : Aut R out) : Aut R out where
  perm := h.perm.symm
  rel_iff r x := by
    simpa using (h.rel_iff r (fun i => h.perm.symm (x i))).symm
  unary_iff f x y := by
    simpa using (h.unary_iff f (h.perm.symm x) (h.perm.symm y)).symm

def trans (h g : Aut R out) : Aut R out where
  perm := h.perm.trans g.perm
  rel_iff r x := (g.rel_iff r (fun i => h.perm (x i))).trans (h.rel_iff r x)
  unary_iff f x y := (g.unary_iff f (h.perm x) (h.perm y)).trans (h.unary_iff f x y)

theorem image_closed (h : Aut R out) (s : Set A)
    (hs : UnaryClosed out (fun x => x ∈ s)) :
    UnaryClosed out (fun x => x ∈ h.perm '' s) := by
  intro f x y hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨h.perm.symm y, hs f a (h.perm.symm y) ha ?_, h.perm.apply_symm_apply y⟩
  apply (h.unary_iff f a (h.perm.symm y)).mp
  simpa only [Equiv.apply_symm_apply] using hy

theorem image_output (h : Aut R out) (f : F) (x : A) :
    h.perm '' out f x = out f (h.perm x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (h.unary_iff f x z).mpr hz
  · intro hy
    refine ⟨h.perm.symm y, ?_, h.perm.apply_symm_apply y⟩
    apply (h.unary_iff f x (h.perm.symm y)).mp
    simpa only [Equiv.apply_symm_apply] using hy
end Aut

variable (R : RelStructure L A) (out : F → A → Set A) (root : Set A)

abbrev Chart := {s : Set A // UnaryClosed out (fun x => x ∈ s) ∧
  ∃ h : Aut R out, s ⊆ h.perm '' root}

def support (x : A) (s : Chart R out root) : Prop := x ∈ s.val

theorem closed (f : F) (x y : A) (s : Chart R out root)
    (hx : support R out root x s) (hy : y ∈ out f x) :
    support R out root y s := s.property.1 f x y hx hy

def imageChart (h : Aut R out) (s : Chart R out root) : Chart R out root :=
  ⟨h.perm '' s.val, h.image_closed s.val s.property.1, by
    obtain ⟨g, hg⟩ := s.property.2
    refine ⟨g.trans h, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨a, ha, heq⟩ := hg hx
    exact ⟨a, ha, congrArg h.perm heq⟩⟩

def chartPerm (h : Aut R out) : Chart R out root ≃ Chart R out root where
  toFun := imageChart R out root h
  invFun := imageChart R out root h.symm
  left_inv s := by
    apply Subtype.ext
    ext x
    change (x ∈ h.perm.symm '' (h.perm '' s.val)) ↔ x ∈ s.val
    simp
  right_inv s := by
    apply Subtype.ext
    ext x
    change (x ∈ h.perm '' (h.perm.symm '' s.val)) ↔ x ∈ s.val
    simp

@[simp] theorem chartPerm_mem (h : Aut R out) (s : Chart R out root) (x : A) :
    support R out root (h.perm x) (chartPerm R out root h s) ↔ support R out root x s := by
  change h.perm x ∈ h.perm '' s.val ↔ x ∈ s.val
  constructor
  · rintro ⟨y, hy, heq⟩
    exact h.perm.injective heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

@[simp] theorem chartPerm_refl :
    chartPerm R out root Aut.refl = Equiv.refl (Chart R out root) := by
  apply Equiv.ext
  intro s
  apply Subtype.ext
  ext x
  change x ∈ (Equiv.refl A) '' s.val ↔ x ∈ s.val
  simp

@[simp] theorem chartPerm_trans (h g : Aut R out) :
    chartPerm R out root (h.trans g) =
      (chartPerm R out root h).trans (chartPerm R out root g) := by
  apply Equiv.ext
  intro s
  apply Subtype.ext
  ext x
  change x ∈ (h.perm.trans g.perm) '' s.val ↔ x ∈ g.perm '' (h.perm '' s.val)
  simp only [Set.mem_image, Equiv.trans_apply]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact ⟨h.perm y, ⟨y, hy, rfl⟩, heq⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, heq⟩
    exact ⟨z, hz, heq⟩

def rootChart (hr : UnaryClosed out (fun x => x ∈ root)) : Chart R out root :=
  ⟨root, hr, Aut.refl, fun x hx => ⟨x, hx, rfl⟩⟩

def fullChart (hr : UnaryClosed out (fun x => x ∈ root)) (h : Aut R out) :
    Chart R out root := chartPerm R out root h (rootChart R out root hr)

def emptyChart : Chart R out root :=
  ⟨∅, by intro f x y hx; exact False.elim hx,
    Aut.refl, fun x hx => False.elim hx⟩

def subchart (s : Set A) (hs : UnaryClosed out (fun x => x ∈ s))
    (incl : s ⊆ root) : Chart R out root :=
  ⟨s, hs, Aut.refl, fun x hx => ⟨x, incl hx, rfl⟩⟩

theorem contained_in_full (hr : UnaryClosed out (fun x => x ∈ root))
    (s : Chart R out root) :
    ∃ h : Aut R out, s.val ⊆ (fullChart R out root hr h).val := s.property.2

instance [Finite A] : Finite (Chart R out root) := inferInstance
end GluingEPPA.Sparsening.OrbitAtlas
