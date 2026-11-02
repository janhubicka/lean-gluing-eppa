import GluingEPPA.Steiner.ChainValuation.ChainIndex
import GluingEPPA.Steiner.ChainValuation.Cosets

/-!
# The finite subtype of separated chain data

The separation condition is evaluated on consecutive triples.  The middle
block carries the outgoing parameter used in the next attachment.  A supplied
subgroup family identifies the common smaller alphabets inside each block.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u
variable {E : Type u} [Fintype E] [DecidableEq E]
variable {S : Finset E} (old : ∀ i : Proper S, Data E i.val)

/-- Subgroups inside each proper block, indexed by an edge set.  The actual
recursive inclusions will instantiate this interface later. -/
abbrev BlockSubgroups :=
  ∀ A : Proper S, Finset E → Subgroup (old A).Carrier

/-- Separation at one internal block. -/
def tripleSeparated (sub : BlockSubgroups old)
    (x y z : ChainAtom S old) : Prop :=
  match x, y, z with
  | ⟨Aprev, _⟩, ⟨A, h⟩, ⟨Anext, _⟩ =>
      Disjoint
        (ChainValuation.leftCoset (sub A (Aprev.val ∩ A.val)) 1)
        (ChainValuation.leftCoset (sub A (A.val ∩ Anext.val)) h)

/-- Every consecutive triple satisfies the internal attachment separation. -/
def separatedList (sub : BlockSubgroups old) : List (ChainAtom S old) → Prop
  | x :: y :: z :: rest =>
      tripleSeparated (old := old) sub x y z ∧ separatedList (old := old) sub (y :: z :: rest)
  | _ => True

def IsSeparated {N : Nat} (sub : BlockSubgroups old)
    (c : RawChain N S old) : Prop :=
  separatedList (old := old) sub (List.ofFn c.2)

/-- The actual finite index type of separated tests of length at most N. -/
abbrev SeparatedChains (N : Nat) (sub : BlockSubgroups old) :=
  FilteredChains N S old (IsSeparated (old := old) sub)

instance separatedChainsFinite (N : Nat) (sub : BlockSubgroups old) :
    Finite (SeparatedChains old N sub) := by
  infer_instance

theorem separatedList_three_iff (sub : BlockSubgroups old)
    (x y z : ChainAtom S old) :
    separatedList (old := old) sub [x, y, z] ↔ tripleSeparated (old := old) sub x y z := by
  simp [separatedList]

/-- Chains of one or two blocks have no internal separation condition. -/
theorem separatedList_short (sub : BlockSubgroups old)
    (l : List (ChainAtom S old)) (h : l.length ≤ 2) :
    separatedList (old := old) sub l := by
  rcases l with _ | ⟨x, l⟩
  · trivial
  · rcases l with _ | ⟨y, l⟩
    · trivial
    · rcases l with _ | ⟨z, l⟩
      · trivial
      · simp at h

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
