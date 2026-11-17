import GluingEPPA.Steiner.ChainValuation.NormalizedProperSeparatedChain
import Mathlib.Data.List.Chain

/-!
# Assembling a separated test from consecutive normalized interfaces

An ordered nonempty list of interfaces determines one more block than
interfaces.  Each internal block receives the shift already selected
between its incoming and outgoing interface.  The first shift is one
(its chart is based at the first interface point), and the last shift
is immaterial and is also chosen to be one.

This finite construction keeps the supplied shifts and all occurrences
of the source masks.  Pairwise normalized separation is enough to put
the entire resulting list in the genuine earlier `SeparatedChains`.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u v
variable {V E : Type u} {B : Type v}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

def NormalizationAdjacent (M : Proper S)
    (leftMask rightMask : B → Proper S)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier)
    (P Q : B) : Prop :=
  rightMask P = leftMask Q ∧
  Disjoint
    (leftCoset (normalizedCommonRight D S old L M (leftMask P) (rightMask P)).range 1)
    (leftCoset (normalizedCommonLeft D S old L M (rightMask P) (rightMask Q)).range
      (shift P Q))

def normalizedBoundaryTail (M : Proper S)
    (rightMask : B → Proper S)
    (hproper : ∀ P, ¬ M.val ⊆ (rightMask P).val)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier) :
    B → List B → List (NormalizedProperSource S old M)
  | P, [] => [⟨rightMask P, hproper P, 1⟩]
  | P, Q :: rest =>
      ⟨rightMask P, hproper P, shift P Q⟩ ::
        normalizedBoundaryTail M rightMask hproper shift Q rest

theorem normalizedBoundaryTail_masks (M : Proper S)
    (rightMask : B → Proper S)
    (hproper : ∀ P, ¬ M.val ⊆ (rightMask P).val)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier)
    (P : B) (rest : List B) :
    (normalizedBoundaryTail S old M rightMask hproper shift P rest).map
      NormalizedProperSource.mask = (P :: rest).map rightMask := by
  induction rest generalizing P with
  | nil => rfl
  | cons Q rest ih =>
      simpa only [normalizedBoundaryTail, List.map_cons] using
        congrArg (List.cons (rightMask P)) (ih Q)

theorem normalizedBoundaryTail_head (M : Proper S)
    (rightMask : B → Proper S)
    (hproper : ∀ P, ¬ M.val ⊆ (rightMask P).val)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier)
    (P : B) (rest : List B) :
    ∃ x xs, normalizedBoundaryTail S old M rightMask hproper shift P rest = x :: xs ∧
      x.mask = rightMask P := by
  cases rest with
  | nil => exact ⟨_, [], rfl, rfl⟩
  | cons Q rest => exact ⟨_, _, rfl, rfl⟩

/-- An arbitrary preceding block with the correct mask can be attached
to the constructed tail.  Its own outgoing shift does not enter the
separation condition at the tail's first block. -/
theorem normalizedBoundaryTail_separated (M : Proper S)
    (leftMask rightMask : B → Proper S)
    (hproper : ∀ P, ¬ M.val ⊆ (rightMask P).val)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier)
    (P : B) (rest : List B)
    (hchain : (P :: rest).IsChain
      (NormalizationAdjacent D S old L M leftMask rightMask shift))
    (first : NormalizedProperSource S old M)
    (hfirst : first.mask = leftMask P) :
    NormalizedSeparated D S old L M
      (first :: normalizedBoundaryTail S old M rightMask hproper shift P rest) := by
  induction rest generalizing P first with
  | nil => trivial
  | cons Q rest ih =>
      obtain ⟨hpair, htail⟩ := List.isChain_cons_cons.mp hchain
      let next : NormalizedProperSource S old M :=
        ⟨rightMask P, hproper P, shift P Q⟩
      have hnext : next.mask = leftMask Q := hpair.1
      have hrest := ih Q htail next hnext
      obtain ⟨x, xs, hxs, hx⟩ :=
        normalizedBoundaryTail_head S old M rightMask hproper shift Q rest
      change NormalizedSeparated D S old L M
        (first :: next :: normalizedBoundaryTail S old M rightMask hproper shift Q rest)
      rw [hxs]
      constructor
      · change Disjoint
          (leftCoset (normalizedCommonRight D S old L M first.mask (rightMask P)).range 1)
          (leftCoset (normalizedCommonLeft D S old L M (rightMask P) x.mask).range
            (shift P Q))
        rw [hfirst, hx]
        exact hpair.2
      · simpa only [hxs] using hrest

def normalizedBoundarySources (M : Proper S)
    (leftMask rightMask : B → Proper S)
    (hleft : ∀ P, ¬ M.val ⊆ (leftMask P).val)
    (hright : ∀ P, ¬ M.val ⊆ (rightMask P).val)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier)
    (P : B) (rest : List B) : List (NormalizedProperSource S old M) :=
  ⟨leftMask P, hleft P, 1⟩ ::
    normalizedBoundaryTail S old M rightMask hright shift P rest

theorem normalizedBoundarySources_masks (M : Proper S)
    (leftMask rightMask : B → Proper S)
    (hleft : ∀ P, ¬ M.val ⊆ (leftMask P).val)
    (hright : ∀ P, ¬ M.val ⊆ (rightMask P).val)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier)
    (P : B) (rest : List B) :
    (normalizedBoundarySources S old M leftMask rightMask hleft hright shift P rest).map
      NormalizedProperSource.mask = leftMask P :: (P :: rest).map rightMask := by
  change leftMask P :: _ = _
  rw [normalizedBoundaryTail_masks]

theorem normalizedBoundarySources_length (M : Proper S)
    (leftMask rightMask : B → Proper S)
    (hleft : ∀ P, ¬ M.val ⊆ (leftMask P).val)
    (hright : ∀ P, ¬ M.val ⊆ (rightMask P).val)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier)
    (P : B) (rest : List B) :
    (normalizedBoundarySources S old M leftMask rightMask hleft hright shift P rest).length =
      rest.length + 2 := by
  have h := congrArg List.length
    (normalizedBoundarySources_masks S old M leftMask rightMask hleft hright shift P rest)
  simpa only [List.length_map, List.length_cons, Nat.add_assoc] using h

/-- The supplied actual normalized shifts define a member of the earlier
test package, not merely an untyped quotient or raw chain. -/
noncomputable def normalizedBoundarySeparatedChain (M : Proper S) (N : Nat)
    (leftMask rightMask : B → Proper S)
    (hleft : ∀ P, ¬ M.val ⊆ (leftMask P).val)
    (hright : ∀ P, ¬ M.val ⊆ (rightMask P).val)
    (shift : ∀ P Q : B, (old (Step.meet S M (rightMask P))).Carrier)
    (P : B) (rest : List B) (hbound : rest.length + 2 ≤ N)
    (hchain : (P :: rest).IsChain
      (NormalizationAdjacent D S old L M leftMask rightMask shift)) :
    SeparatedChains D N M.val (smallerOld S old M) (smallerLinks D S old L M) :=
  normalizedProperSeparatedChain D S old L M N
    (normalizedBoundarySources S old M leftMask rightMask hleft hright shift P rest)
    (List.cons_ne_nil _ _)
    (by simpa only [normalizedBoundarySources_length] using hbound)
    (normalizedBoundaryTail_separated D S old L M leftMask rightMask hright shift
      P rest hchain ⟨leftMask P, hleft P, 1⟩ rfl)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
