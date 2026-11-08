import GluingEPPA.Steiner.ChainValuation.ChainIndex
import GluingEPPA.Steiner.ChainValuation.Cosets

/-!
# The finite subtype of separated chain data
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u
variable {E : Type u} [Fintype E] [DecidableEq E]

abbrev BlockSubgroups {S : Finset E}
    (old : ∀ i : Proper S, Data E i.val) :=
  ∀ A : Proper S, Finset E → Subgroup (old A).Carrier

def tripleSeparated {S : Finset E}
    {old : ∀ i : Proper S, Data E i.val}
    (sub : BlockSubgroups old)
    (x y z : ChainAtom S old) : Prop :=
  match x, y, z with
  | ⟨Aprev, _⟩, ⟨A, h⟩, ⟨Anext, _⟩ =>
      Disjoint
        (ChainValuation.leftCoset (sub A (Aprev.val ∩ A.val)) 1)
        (ChainValuation.leftCoset (sub A (A.val ∩ Anext.val)) h)

def separatedList {S : Finset E}
    {old : ∀ i : Proper S, Data E i.val}
    (sub : BlockSubgroups old) : List (ChainAtom S old) → Prop
  | x :: y :: z :: rest =>
      tripleSeparated sub x y z ∧ separatedList sub (y :: z :: rest)
  | _ => True

def IsSeparated {N : Nat} {S : Finset E}
    {old : ∀ i : Proper S, Data E i.val}
    (sub : BlockSubgroups old) (c : RawChain N S old) : Prop :=
  separatedList sub (List.ofFn c.2)

abbrev SeparatedChains (N : Nat) {S : Finset E}
    (old : ∀ i : Proper S, Data E i.val)
    (sub : BlockSubgroups old) :=
  FilteredChains N S old (IsSeparated sub)

instance separatedChainsFinite (N : Nat) {S : Finset E}
    (old : ∀ i : Proper S, Data E i.val)
    (sub : BlockSubgroups old) :
    Finite (SeparatedChains N old sub) := by
  infer_instance

theorem separatedList_three_iff {S : Finset E}
    {old : ∀ i : Proper S, Data E i.val}
    (sub : BlockSubgroups old) (x y z : ChainAtom S old) :
    separatedList sub [x, y, z] ↔ tripleSeparated sub x y z := by
  change (tripleSeparated sub x y z ∧ True) ↔ tripleSeparated sub x y z
  simp

theorem separatedList_short {S : Finset E}
    {old : ∀ i : Proper S, Data E i.val}
    (sub : BlockSubgroups old)
    (l : List (ChainAtom S old)) (h : l.length ≤ 2) :
    separatedList sub l := by
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
