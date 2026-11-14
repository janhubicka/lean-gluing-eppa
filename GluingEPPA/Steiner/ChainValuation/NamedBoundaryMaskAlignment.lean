import GluingEPPA.Steiner.ChainValuation.NamedHistoryFinite
import GluingEPPA.Steiner.ChainValuation.FiniteBoundarySourcePairs

/-!
# Matching ordered historical source masks with actual boundary masks

The source-named historical chart list has the same block order as the
literal input atoms. The independently verified witnessed-boundary
history records exactly the consecutive mask pairs. We identify those
two lists without choosing a common ambient group or changing the
original finite chain quotient.

The final equality is only an *index alignment*. Matching the actual
embedded historical block maps and normalized interface charts at
those indices remains a separate geometric theorem.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

/-- Adjacent pairs of genuine source masks, independent of the
coset-translation parameters in their chain atoms. -/
def maskPairTail (c : Proper S) : List (Proper S) → List (Proper S × Proper S)
  | [] => []
  | z :: zs => (c, z) :: maskPairTail z zs

/-- The ordered adjacent boundary masks of a source-mask list. -/
def adjacentMaskPairs : List (Proper S) → List (Proper S × Proper S)
  | [] => []
  | c :: cs => maskPairTail S c cs

/-- Forgetting the group parameters from atoms commutes with taking
all consecutive adjacent pairs, including repeated source masks. -/
theorem maskPairTail_atoms (c : Atom S old)
    (rest : List (Atom S old)) :
    maskPairTail S c.1 (rest.map (fun a => a.1)) =
      tailSourceMaskPairs S old c rest := by
  induction rest generalizing c with
  | nil =>
      rfl
  | cons z zs ih =>
      change
        (c.1, z.1) ::
          maskPairTail S z.1 (zs.map (fun a => a.1)) =
        (c.1, z.1) :: tailSourceMaskPairs S old z zs
      exact congrArg (List.cons (c.1, z.1)) (ih z)

/-- On the literal input atoms the abstract mask-pair operator is
definitionally the old consecutive-source-pair computation. -/
theorem adjacentMaskPairs_atoms (atoms : List (Atom S old)) :
    adjacentMaskPairs S (atoms.map (fun a => a.1)) =
      consecutiveSourceMaskPairs S old atoms := by
  cases atoms with
  | nil =>
      rfl
  | cons c cs =>
      exact maskPairTail_atoms S old c cs

/-- The actual boundary records and the actual source-named chart
history agree on *every consecutive pair of original masks* and on
their order, for an arbitrary nonempty separated chain.

This theorem compares two already certified histories. It does not
assert equality of their different dependent records or of their
individual embeddings: that comparison is the next normalization
step. -/
theorem namedHistory_boundaries_align_masks
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (boundaryHistoryBuildNonempty D S old L M atoms hne hsep).
        boundaries.map (fun T => (T.leftMask, T.rightMask)) =
      adjacentMaskPairs S
        (namedHistoryBuildNonempty D S old L M atoms hne hsep).sourceMasks := by
  calc
    (boundaryHistoryBuildNonempty D S old L M atoms hne hsep).
        boundaries.map (fun T => (T.leftMask, T.rightMask)) =
        consecutiveSourceMaskPairs S old atoms :=
      boundaryHistoryBuildNonempty_sourcePairs D S old L M atoms hne hsep
    _ = adjacentMaskPairs S
          (namedHistoryBuildNonempty D S old L M atoms hne hsep).sourceMasks := by
      rw [namedHistoryBuildNonempty_sources D S old L M atoms hne hsep]
      exact (adjacentMaskPairs_atoms S old atoms).symm

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
