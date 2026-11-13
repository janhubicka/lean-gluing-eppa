import GluingEPPA.Steiner.ChainValuation.LinkChain

/-!
# Inclusive smaller-mask stages for normalized component chains

A restriction of a chain built at S to an earlier proper alphabet
M ⊊ S uses Cayley groups K_(M∩A) for historical block masks A.
It is false that M∩A is always a *proper* subset of M: when
M ⊆ A, the normalized block is K_M itself.

This file makes the indexing issue explicit. Normalized blocks are
indexed by all T ⊆ M, including T = M, but each T is still a proper
earlier stage of S. The entire normalization can therefore use
existing earlier groups without invoking a hypothetical K_S or
asserting an unjustified coercion to Proper M.

This is an indexing/interface component, not a full chain-restriction
or higher-acyclicity theorem.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

universe u
variable {E : Type u} [Fintype E] [DecidableEq E]
variable (S : Finset E)

/-- All masks bounded above by M; the maximum mask M is allowed. -/
abbrev InclusiveMask (M : Proper S) :=
  {T : Finset E // T ⊆ M.val}

/-- Any mask bounded by M is a genuine proper earlier stage of S,
even when it equals M itself. -/
def inclusiveLift (M : Proper S) (T : InclusiveMask S M) : Proper S :=
  ⟨T.val, lt_of_le_of_lt T.property M.property⟩

/-- The maximum inclusive mask. Its group is the already constructed K_M. -/
def inclusiveTop (M : Proper S) : InclusiveMask S M :=
  ⟨M.val, fun _ h => h⟩

/-- The historical block indexed by A normalizes to M ∩ A. -/
def inclusiveMeet (M A : Proper S) : InclusiveMask S M :=
  ⟨M.val ∩ A.val, Finset.inter_subset_left⟩

theorem inclusiveLift_top (M : Proper S) :
    inclusiveLift S M (inclusiveTop S M) = M := by
  apply Subtype.ext
  rfl

theorem inclusiveLift_meet (M A : Proper S) :
    inclusiveLift S M (inclusiveMeet S M A) = Step.meet S M A := by
  apply Subtype.ext
  rfl

/-- Precisely when M ⊆ A, the normalized block has the full mask M.
This case must not be treated as a Proper M test atom. -/
theorem inclusiveMeet_eq_top_iff (M A : Proper S) :
    inclusiveMeet S M A = inclusiveTop S M ↔ M.val ⊆ A.val := by
  constructor
  · intro heq
    have h : M.val ∩ A.val = M.val :=
      congrArg Subtype.val heq
    intro e he
    have hei : e ∈ M.val ∩ A.val := by
      rw [h]
      exact he
    exact (Finset.mem_inter.mp hei).2
  · intro h
    apply Subtype.ext
    exact Finset.inter_eq_left.mpr h

/-- The dichotomy is exhaustive: a normalized historical block
is either the maximal K_M stage, or its mask is a proper subset of M. -/
theorem inclusiveMeet_strict_or_full (M A : Proper S) :
    (inclusiveMeet S M A).val ⊂ M.val ∨
      inclusiveMeet S M A = inclusiveTop S M := by
  by_cases h : M.val ⊆ A.val
  · exact Or.inr ((inclusiveMeet_eq_top_iff S M A).mpr h)
  · left
    apply lt_of_le_of_ne Finset.inter_subset_left
    intro heq
    apply h
    intro e he
    have hei : e ∈ M.val ∩ A.val := by
      rw [heq]
      exact he
    exact (Finset.mem_inter.mp hei).2

/-- The carrier of a normalized block is always one of the already
constructed earlier Cayley groups. No new recursive group is needed. -/
abbrev InclusiveCarrier
    (old : ∀ i : Proper S, Data E i.val)
    (M : Proper S) (T : InclusiveMask S M) : Type u :=
  (old (inclusiveLift S M T)).Carrier

/-- The normalized chain atom can use a maximal K_M block. -/
abbrev InclusiveAtom
    (old : ∀ i : Proper S, Data E i.val)
    (M : Proper S) :=
  Σ T : InclusiveMask S M, InclusiveCarrier S old M T

instance inclusiveMaskFinite (M : Proper S) :
    Finite (InclusiveMask S M) := by
  infer_instance

instance inclusiveAtomFinite
    (old : ∀ i : Proper S, Data E i.val) (M : Proper S) :
    Finite (InclusiveAtom S old M) := by
  infer_instance

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
