import GluingEPPA.Steiner.ChainValuation.LinkChain
import GluingEPPA.Steiner.ChainValuation.ParameterizedFamily

/-!
# The actual finite test package of all separated bounded chains

For fixed N and one recursive stage S, the index type is the finite subtype of
raw bounded chain data satisfying the Link-based separation predicate.  Each
index is built left-to-right into a ChainState; its global letter matching
supplies the added permutation coordinate of the augmented record.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (N : Nat) (S : Finset E)
variable (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

def IsSeparated (c : ChainValuation.RawChain N S old) : Prop :=
  separatedList D S old L (List.ofFn c.2)

abbrev SeparatedChains :=
  {c : ChainValuation.RawChain N S old // IsSeparated D N S old L c}

instance separatedChainsFinite :
    Finite (SeparatedChains D N S old L) := by
  infer_instance

theorem rawChain_list_nonempty (c : ChainValuation.RawChain N S old) :
    List.ofFn c.2 ≠ [] := by
  intro h
  have hlen : (List.ofFn c.2).length = c.1.val := by simp
  rw [h] at hlen
  have hpos := c.1.property
  simp at hlen
  omega

noncomputable def chainState (c : SeparatedChains D N S old L) :
    SomeState S old :=
  buildNonempty D S old L (List.ofFn c.1.2)
    (rawChain_list_nonempty D N S old c.1) c.2

abbrev chainSpace (c : SeparatedChains D N S old L) :=
  (chainState D N S old L c).state.Space

instance chainSpaceFinite (c : SeparatedChains D N S old L) :
    Finite (chainSpace D N S old L c) :=
  inferInstance

noncomputable def chainPerm (c : SeparatedChains D N S old L)
    (e : E) : Equiv.Perm (chainSpace D N S old L c) :=
  ((chainState D N S old L c).state.matching e).perm

theorem chainPerm_involutive (c : SeparatedChains D N S old L) (e : E) :
    Function.Involutive (chainPerm D N S old L c e) :=
  ((chainState D N S old L c).state.matching e).next_involutive

theorem chainPerm_square (c : SeparatedChains D N S old L) (e : E) :
    chainPerm D N S old L c e * chainPerm D N S old L c e = 1 := by
  ext x
  exact chainPerm_involutive D N S old L c e x

/-- The finite package appended to the old recursive record at stage S. -/
noncomputable def testPackage :
    TestPackage E S old where
  J := SeparatedChains D N S old L
  finiteJ := inferInstance
  X := chainSpace D N S old L
  finiteX := fun _ => inferInstance
  τ := fun c e => chainPerm D N S old L c e
  square := chainPerm_square D N S old L

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
