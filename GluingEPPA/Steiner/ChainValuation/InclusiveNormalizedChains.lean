import GluingEPPA.Steiner.ChainValuation.InclusiveNormalizedMasks
import GluingEPPA.Steiner.ChainValuation.ChainTests

/-!
# Finite normalized chains with inclusive smaller-mask blocks

At stage S, for each earlier mask M ⊊ S the normalized connected
component of a separated chain may contain blocks K_T with
T ⊆ M, including T = M. Since all such T are proper in S,
the actual earlier-stage Link chain builder accepts them.

This file defines inclusive normalized atoms, finite bounded
chains, and separated tests by *mapping into the original literal
LinkChain builder*. No alternate gluing relation is postulated.

Thus the typing obstruction M∩A=M disappears without asserting
that this is already an old stage-M Proper M test. A later theorem
must still construct, for each M-component, the normalized
parameters and an edge-reflecting equivalence to one such test.
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

/-- Map an inclusive normalized atom to its genuine earlier-stage
LinkChain atom without changing its group coordinate. -/
def inclusiveAtomToAtom (M : Proper S) :
    InclusiveAtom S old M → Atom S old
  | ⟨T, x⟩ => ⟨inclusiveLift S M T, x⟩

/-- A maximal normalized atom is allowed: this is the already
constructed group K_M, even though M is not a proper subset of M. -/
noncomputable def inclusiveFullAtom (M : Proper S)
    (x : (old M).Carrier) : InclusiveAtom S old M := by
  have htop := inclusiveLift_top S M
  exact ⟨inclusiveTop S M,
    (show (old (inclusiveLift S M (inclusiveTop S M))).Carrier from
      htop.symm ▸ x)⟩

/-- Bounded positive-length normalized chain indices, before imposing
the original separation condition. -/
abbrev InclusiveRawChain (M : Proper S) :=
  Σ r : ChainValuation.ChainLength N,
    Fin r.val → InclusiveAtom S old M

instance inclusiveRawChainFinite (M : Proper S) :
    Finite (InclusiveRawChain N S old M) := by
  infer_instance

/-- Forget the inclusive bound and obtain a literal stage-S
chain; every block is still a proper earlier stage of S. -/
def inclusiveRawToRaw (M : Proper S)
    (c : InclusiveRawChain N S old M) :
    ChainValuation.RawChain N S old :=
  ⟨c.1, fun i => inclusiveAtomToAtom S old M (c.2 i)⟩

/-- The original LinkChain separation predicate, not a weakening. -/
def InclusiveIsSeparated (M : Proper S)
    (c : InclusiveRawChain N S old M) : Prop :=
  IsSeparated D N S old L (inclusiveRawToRaw N S old M c)

/-- The finite family of actual separated normalized chains whose
block alphabets lie inside M, possibly equal to M. -/
abbrev InclusiveSeparatedChains (M : Proper S) :=
  {c : InclusiveRawChain N S old M //
    InclusiveIsSeparated D N S old L M c}

instance inclusiveSeparatedChainsFinite (M : Proper S) :
    Finite (InclusiveSeparatedChains D N S old L M) := by
  infer_instance

/-- Realize an inclusive normalized chain using exactly the
original stage-S LinkChain.chainState pushout and matching. -/
noncomputable def inclusiveChainState
    (M : Proper S) (c : InclusiveSeparatedChains D N S old L M) :
    SomeState S old :=
  chainState D N S old L
    ⟨inclusiveRawToRaw N S old M c.1, c.2⟩

/-- Completed letter actions on the realized inclusive chain. -/
noncomputable def inclusiveChainPerm
    (M : Proper S) (c : InclusiveSeparatedChains D N S old L M)
    (e : E) :
    Equiv.Perm (inclusiveChainState D N S old L M c).state.Space :=
  ((inclusiveChainState D N S old L M c).state.matching e).perm

theorem inclusiveChainPerm_involutive
    (M : Proper S) (c : InclusiveSeparatedChains D N S old L M)
    (e : E) :
    Function.Involutive (inclusiveChainPerm D N S old L M c e) :=
  ((inclusiveChainState D N S old L M c).state.matching e).next_involutive

theorem inclusiveChainPerm_square
    (M : Proper S) (c : InclusiveSeparatedChains D N S old L M)
    (e : E) :
    inclusiveChainPerm D N S old L M c e *
      inclusiveChainPerm D N S old L M c e = 1 := by
  ext x
  exact inclusiveChainPerm_involutive D N S old L M c e x

/-- A genuine finite TestPackage built only from the previously
constructed K_T, T ⊆ M, including T=M. This makes the normalized
test family available without claiming it is a Proper M test. -/
noncomputable def inclusiveTestPackage (M : Proper S) :
    TestPackage E S old where
  J := InclusiveSeparatedChains D N S old L M
  finiteJ := inferInstance
  X := fun c => (inclusiveChainState D N S old L M c).state.Space
  finiteX := fun _ => inferInstance
  τ := fun c e => inclusiveChainPerm D N S old L M c e
  square := inclusiveChainPerm_square D N S old L M

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
