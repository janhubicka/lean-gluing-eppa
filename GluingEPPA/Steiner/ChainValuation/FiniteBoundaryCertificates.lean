import GluingEPPA.Steiner.ChainValuation.FiniteBoundaryInjectivity
import GluingEPPA.Steiner.ChainValuation.FiniteBoundarySourcePairs

/-!
# Complete finite-chain boundary certificates

Each original pair of consecutive input masks contributes exactly one
real historical interface. Its source groups remain embedded in the final
quotient, its attachment points remain identified, and reachability across
the two historical charts is characterized by an actual parameter of
the earlier intersection group.

This packages the independently verified indexing, persistence, and
injectivity statements in the *same* literal finite-chain construction.
The separate global normalized M-component equivalence is not claimed.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The number of real embedded historical boundaries is exactly
the number of consecutive adjacent-mask pairs in the input. -/
theorem boundaryHistoryBuildNonempty_boundary_count
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (boundaryHistoryBuildNonempty D S old L M atoms hne hsep).boundaries.length =
      (consecutiveSourceMaskPairs S old atoms).length := by
  have h := boundaryHistoryBuildNonempty_sourcePairs
    D S old L M atoms hne hsep
  have hlen := congrArg List.length h
  simpa only [List.length_map] using hlen

/-- Each original consecutive boundary, transported to the final
state, embeds both source Cayley blocks and retains its actual
two-sided parameter interface with exact M-path reflection. -/
theorem boundaryHistoryBuildNonempty_complete_boundary_certificates
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := boundaryHistoryBuildNonempty D S old L M atoms hne hsep
    H.boundaries.map (fun T => (T.leftMask, T.rightMask)) =
      consecutiveSourceMaskPairs S old atoms ∧
    (∀ T : HistoricalLinkBoundary D S old L M H.chain,
      T ∈ H.boundaries →
        T.Embeds D S old L ∧
        (∀ k : (old (common S T.leftMask T.rightMask)).Carrier,
          T.leftChart (T.leftParam k) =
            T.rightChart (T.rightParam k)) ∧
        (∀ x y,
          LabelReach (fun e => (H.chain.state.matching e).Rel)
            M.val (T.leftChart x) (T.rightChart y) ↔
          ∃ k : (old (common S T.leftMask T.rightMask)).Carrier,
            LabelReach
              (fun e => ((block S old T.leftMask).matching e).Rel)
              M.val x (T.leftParam k) ∧
            LabelReach
              (fun e => ((block S old T.rightMask).matching e).Rel)
              M.val (T.rightParam k) y)) := by
  constructor
  · exact boundaryHistoryBuildNonempty_sourcePairs
      D S old L M atoms hne hsep
  · intro T hT
    refine ⟨?_, ?_, ?_⟩
    · exact boundaryHistoryBuildNonempty_allEmbedded
        D S old L M atoms hne hsep T hT
    · exact T.attached
    · exact T.reach_iff

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
