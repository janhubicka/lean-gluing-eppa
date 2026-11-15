import GluingEPPA.Steiner.ChainValuation.NormalizedProperMaskReindex
import GluingEPPA.Steiner.ChainValuation.ChainTests

/-!
# Actual bounded normalized chain data over the earlier alphabet M

Once a genuine M-component has a proper-mask active interval,
each historical source block K_A must be replaced by its *real*
earlier group K_(M intersection A), with a chosen normalized
outgoing group parameter. The preceding proper-mask reindexing
proves that these are genuine earlier stages below M.

This file packages those already supplied normalized parameters into
the actual RawChain N M data type used by the recursive valuation.
It retains the SAME bounded positive length and the exact named
source indices. In particular this does not manufacture separated
coordinates: separation of the translated actual boundaries
remains the next geometric obligation.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

/-- One original historical source mask, certified to give a
proper submask of M, together with its genuine normalized
outgoing parameter in the existing older group K_(M intersection A). -/
structure NormalizedProperSource (M : Proper S) where
  mask : Proper S
  proper : ¬ M.val ⊆ mask.val
  shift : (old (Step.meet S M mask)).Carrier

/-- Convert exactly those original data into an actual atom
for the smaller-alphabet chain constructor. -/
def normalizedProperAtom
    (M : Proper S) (a : NormalizedProperSource S old M) :
    ChainValuation.ChainAtom M.val (smallerOld S old M) :=
  ⟨normalizedProperMask S M a.mask a.proper, a.shift⟩

@[simp] theorem normalizedProperAtom_mask
    (M : Proper S) (a : NormalizedProperSource S old M) :
    (normalizedProperAtom S old M a).1.val =
      M.val ∩ a.mask.val := rfl

/-- The converted atom carries the actual group element of the
same original earlier-stage group, not a chosen isomorphic value. -/
theorem normalizedProperAtom_value
    (M : Proper S) (a : NormalizedProperSource S old M) :
    (normalizedProperAtom S old M a).2 = a.shift := rfl

/-- A finite original interval, after supplying one normalized
parameter in each earlier source group, becomes a literal bounded
raw chain over the earlier alphabet M, of exactly the same length.

No membership in the separated-chain subtype is claimed here:
that requires the genuine normalized interior separation proof.
-/
def normalizedProperRawChain
    (M : Proper S) (N : Nat)
    (r : ChainValuation.ChainLength N)
    (a : Fin r.val → NormalizedProperSource S old M) :
    ChainValuation.RawChain N M.val (smallerOld S old M) :=
  ⟨r, fun i => normalizedProperAtom S old M (a i)⟩

@[simp] theorem normalizedProperRawChain_length
    (M : Proper S) (N : Nat)
    (r : ChainValuation.ChainLength N)
    (a : Fin r.val → NormalizedProperSource S old M) :
    (normalizedProperRawChain S old M N r a).1.val = r.val := rfl

/-- Every entry of the resulting genuine raw chain has exactly
the M intersection original-source mask; no mask reordering,
cardinality change, or additional alphabet is introduced. -/
theorem normalizedProperRawChain_mask
    (M : Proper S) (N : Nat)
    (r : ChainValuation.ChainLength N)
    (a : Fin r.val → NormalizedProperSource S old M)
    (i : Fin r.val) :
    ((normalizedProperRawChain S old M N r a).2 i).1.val =
      M.val ∩ (a i).mask.val := rfl

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
