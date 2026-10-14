import Mathlib.Data.Finite.Sum
import GluingEPPA.Sparsening.AuxiliaryJ

/-!
# Concrete carrier for the local-tree amalgamation induction

Adapted, at the structural level, from the verified carrier construction in
shulda/lean_all_those_eppa_classes:
  AllThoseEPPA/TreeLikeAmalgamCarrier.lean.

A direct import is currently blocked by different pinned Lean releases.
The carrier retains every left vertex and adds only right vertices outside
the gluing image. There is no indiscriminate quotient or accidental collapse.
The relational / full unary interpretation will be ported separately.
-/
namespace GluingEPPA.Sparsening.Tree
universe u v w
variable {I : Type u} {X : Type v} {Y : Type w}

/-- The actual strong-amalgam carrier along injections f,g. -/
def PushoutCarrier (f : I → X) (g : I → Y) : Type (max v w) :=
  X ⊕ {y : Y // y ∉ Set.range g}

def inclLeft (f : I → X) (g : I → Y) : X → PushoutCarrier f g := Sum.inl

noncomputable def inclRight (f : I → X) (g : I → Y) :
    Y → PushoutCarrier f g := by
  classical
  intro y
  exact if hy : y ∈ Set.range g then
    Sum.inl (f (Classical.choose hy))
  else
    Sum.inr ⟨y, hy⟩

theorem inclLeft_injective (f : I → X) (g : I → Y) :
    Function.Injective (inclLeft f g) := Sum.inl_injective

theorem inclRight_glued (f : I → X) (g : I → Y)
    (hg : Function.Injective g) (i : I) :
    inclRight f g (g i) = inclLeft f g (f i) := by
  classical
  have hi : g i ∈ Set.range g := ⟨i, rfl⟩
  change (if h : g i ∈ Set.range g then
      (Sum.inl (f (Classical.choose h)) : PushoutCarrier f g)
    else Sum.inr ⟨g i, h⟩) = Sum.inl (f i)
  simp only [dif_pos hi]
  exact congrArg (fun j : I =>
    (Sum.inl (f j) : PushoutCarrier f g))
    (hg (Classical.choose_spec hi))

theorem inclRight_outside (f : I → X) (g : I → Y)
    (y : Y) (hy : y ∉ Set.range g) :
    inclRight f g y = Sum.inr ⟨y, hy⟩ := by
  classical
  change (if h : y ∈ Set.range g then
      (Sum.inl (f (Classical.choose h)) : PushoutCarrier f g)
    else Sum.inr ⟨y, h⟩) = Sum.inr ⟨y, hy⟩
  simp only [dif_neg hy]

theorem inclRight_injective
    (f : I → X) (g : I → Y) (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Injective (inclRight f g) := by
  intro y z h
  classical
  by_cases hy : y ∈ Set.range g
  · obtain ⟨i, rfl⟩ := hy
    by_cases hz : z ∈ Set.range g
    · obtain ⟨j, rfl⟩ := hz
      rw [inclRight_glued f g hg i,
          inclRight_glued f g hg j] at h
      have hfi : f i = f j := Sum.inl.inj h
      exact congrArg g (hf hfi)
    · rw [inclRight_glued f g hg i,
          inclRight_outside f g z hz] at h
      cases h
  · by_cases hz : z ∈ Set.range g
    · obtain ⟨j, rfl⟩ := hz
      rw [inclRight_outside f g y hy,
          inclRight_glued f g hg j] at h
      cases h
    · rw [inclRight_outside f g y hy,
          inclRight_outside f g z hz] at h
      have hSub : (⟨y, hy⟩ : {t : Y // t ∉ Set.range g}) =
          ⟨z, hz⟩ := Sum.inr.inj h
      exact congrArg Subtype.val hSub

/-- The two images meet EXACTLY in the prescribed gluing image. -/
theorem left_eq_right_iff (f : I → X) (g : I → Y)
    (hg : Function.Injective g) (x : X) (y : Y) :
    inclLeft f g x = inclRight f g y ↔
      ∃ i : I, x = f i ∧ y = g i := by
  constructor
  · intro h
    by_cases hy : y ∈ Set.range g
    · obtain ⟨i, rfl⟩ := hy
      rw [inclRight_glued f g hg i] at h
      have hEq : x = f i := Sum.inl.inj h
      exact ⟨i, hEq, rfl⟩
    · rw [inclRight_outside f g y hy] at h
      cases h
  · rintro ⟨i, rfl, rfl⟩
    exact (inclRight_glued f g hg i).symm

theorem pushout_covered (f : I → X) (g : I → Y) :
    Set.range (inclLeft f g) ∪ Set.range (inclRight f g) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro z
  cases z with
  | inl x =>
      exact Or.inl ⟨x, rfl⟩
  | inr y =>
      refine Or.inr ⟨y.1, ?_⟩
      have hSubtype :
          (⟨y.1, y.2⟩ : {z : Y // z ∉ Set.range g}) = y :=
        Subtype.ext rfl
      simpa only [hSubtype] using
        (inclRight_outside f g y.1 y.2)

instance pushout_finite (f : I → X) (g : I → Y)
    [Finite X] [Finite Y] : Finite (PushoutCarrier f g) := by
  change Finite (X ⊕ {y : Y // y ∉ Set.range g})
  infer_instance

end GluingEPPA.Sparsening.Tree
