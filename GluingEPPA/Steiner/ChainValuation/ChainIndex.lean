import GluingEPPA.Steiner.RecursiveRecord

/-!
# Finite indexing of bounded chain data

For finiteness we do not quotient chains by isomorphism. A block atom stores
its proper alphabet together with one element of that block group; the element
on the last block is harmless redundant data. A bounded chain is a positive
length r <= N and an r-tuple of such atoms. Any separated-chain predicate is
therefore a finite subtype.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u
variable {E : Type u} [Fintype E] [DecidableEq E]

/-- One block alphabet together with the parameter used for its outgoing
attachment. The last parameter of a chain is ignored. -/
abbrev ChainAtom (S : Finset E) (old : ∀ i : Proper S, Data E i.val) :=
  Σ A : Proper S, (old A).Carrier

instance chainAtomFinite (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) :
    Finite (ChainAtom S old) := by
  infer_instance

/-- Positive lengths at most N. -/
abbrev ChainLength (N : Nat) := {r : Fin (N + 1) // 0 < r.val}

/-- Raw bounded chain data. -/
abbrev RawChain (N : Nat) (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) :=
  Σ r : ChainLength N, Fin r.val → ChainAtom S old

instance rawChainFinite (N : Nat) (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) :
    Finite (RawChain N S old) := by
  infer_instance

/-- Any property, in particular attachment separation, cuts out a finite
family of chain data. -/
abbrev FilteredChains (N : Nat) (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val)
    (P : RawChain N S old → Prop) :=
  {c : RawChain N S old // P c}

instance filteredChainsFinite (N : Nat) (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val)
    (P : RawChain N S old → Prop) :
    Finite (FilteredChains N S old P) := by
  infer_instance

theorem chainLength_le {N : Nat} (r : ChainLength N) : r.val ≤ N := by
  exact Nat.lt_succ_iff.mp r.val.isLt

theorem chainLength_pos {N : Nat} (r : ChainLength N) : 0 < r.val :=
  r.property

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
