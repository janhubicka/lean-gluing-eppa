import GluingEPPA.Steiner.ChainValuation.NamedHistoryActiveInterval
import GluingEPPA.Steiner.ChainValuation.CombinedHistoricalExactCharts
import GluingEPPA.Steiner.ChainValuation.CoupledHistoryOriginalCorrespondence
import GluingEPPA.Steiner.ChainValuation.NamedHistoryOriginalCorrespondence

/-!
# One original chain for active named intervals and exact boundary charts

The normalized proper-M chain construction needs two results
SIMULTANEOUSLY on the SAME original quotient:

1. The M-component of q meets a nonempty consecutive interval of
   the genuine named historical Cayley blocks.
2. Every original historical boundary is equipped with its
   pointwise Cayley coordinates and identical adjacent middle
   chart, in its original position.

The first theorem in this module compares the *full dependent
BuildResult states* of the named and aligned finite histories.
Both are the corresponding projections of the previously checked
single coupled-history recursion. Thus their point carriers,
completed matching families, current source block and historical
step data are literally equal, not merely isomorphic.

The joint corollary gives all the geometric invariants on these
two canonically identical states. It does not yet prove that an
active sublist of named blocks selects exactly the internal
aligned boundaries at matching positions; that is the remaining
finite interval-index bridge before normalizing all shifts.
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

open GluingEPPA.Steiner.ChainValuation

/-- The source-named historical chart construction and the
pointwise/linked aligned original boundary construction have
IDENTICAL entire dependent BuildResult states.

The proof uses the actual common coupled-history builder and
the independently checked exact forgetful correspondences.
There is no alternate quotient and no guessed chart map. -/
theorem named_and_aligned_buildNonempty_sameChain
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (namedHistoryBuildNonempty D S old L M
      atoms hne hsep).data.chain =
    (alignedNamedBuildNonempty D S old L M
      atoms hne hsep).boundaryHistory.chain := by
  let T := coupledHistoryBuildNonempty D S old L M
    atoms hne hsep
  let N := namedHistoryBuildNonempty D S old L M
    atoms hne hsep
  let H := alignedNamedBuildNonempty D S old L M
    atoms hne hsep
  have hNamed : T.named = N :=
    coupledHistoryBuildNonempty_named_eq
      D S old L M atoms hne hsep
  have hBoundary : T.boundary =
      boundaryHistoryBuildNonempty D S old L M
        atoms hne hsep :=
    coupledHistoryBuildNonempty_boundary_eq
      D S old L M atoms hne hsep
  have hAligned : H.boundaryHistory =
      boundaryHistoryBuildNonempty D S old L M
        atoms hne hsep :=
    alignedNamedBuildNonempty_boundary_eq
      D S old L M atoms hne hsep
  calc
    N.data.chain = T.named.data.chain := by rw [hNamed]
    _ = T.boundary.chain := T.sameChain
    _ = (boundaryHistoryBuildNonempty D S old L M
        atoms hne hsep).chain :=
      congrArg
        (fun B : BoundaryHistoryBuildResult D S old L M => B.chain)
        hBoundary
    _ = H.boundaryHistory.chain :=
      (congrArg
        (fun B : BoundaryHistoryBuildResult D S old L M => B.chain)
        hAligned).symm

/-- Every actual M-component of the original source-named chain
has a nonempty interval of named source-block occurrences, AND
the identical chain state carries all exact original historical
boundary charts, with both pointwise coordinates and equality
of consecutive middle-block charts.

This is one single original finite LinkChain, not two models
related by a freely chosen isomorphism. -/
theorem buildNonempty_joint_active_interval_and_exact_boundaries
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let N := namedHistoryBuildNonempty D S old L M
      atoms hne hsep
    let H := alignedNamedBuildNonempty D S old L M
      atoms hne hsep
    N.data.chain = H.boundaryHistory.chain ∧
    (∀ q : N.data.chain.state.Space,
      ∃ front active back :
          List (NamedHistoricalBlock D S old L M N.data.chain),
        N.named = front ++ active ++ back ∧
        active ≠ [] ∧
        (∀ T ∈ front,
          ¬ ((T.toHistorical D S old L).Meets
            (block S old N.data.chain.current.1)
            N.data.chain.state M.val q)) ∧
        (∀ T ∈ active,
          (T.toHistorical D S old L).Meets
            (block S old N.data.chain.current.1)
            N.data.chain.state M.val q) ∧
        (∀ T ∈ back,
          ¬ ((T.toHistorical D S old L).Meets
            (block S old N.data.chain.current.1)
            N.data.chain.state M.val q))) ∧
    AlignedBoundaryList.Linked D S old L H.aligned ∧
    H.AllPointwise D S old L := by
  intro N H
  have hSame := named_and_aligned_buildNonempty_sameChain
    D S old L M atoms hne hsep
  have hActive := namedHistoryBuildNonempty_active_interval
    D S old L M atoms hne hsep
  have hCharts := alignedNamedBuildNonempty_pointwise_and_linked
    D S old L M atoms hne hsep
  exact ⟨hSame, hActive, hCharts.1, hCharts.2⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
