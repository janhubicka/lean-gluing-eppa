import GluingEPPA.Steiner.ChainValuation.LinkedAlignedBoundaryPairs
import GluingEPPA.Steiner.ChainValuation.AlignedInteriorShift

/-!
# Unique normalized interior shift in every actual finite LinkChain

This combines two independently Lean-checked geometric developments:
the globally linked original historical boundary charts and the
unique displacement for two true interface points lying in the
same actual M-component and historical middle source block.

For any TWO CONSECUTIVE boundary occurrences of the original
finite separated LinkChain, and for arbitrary actual common-group
parameters reached by one M-component at those boundaries, the
correct pair of historical middle coordinates exists and
determines a unique element of K_(M intersect A).

All carriers, embeddings and labelled reachability refer to the
literal original LinkChain.buildNonempty; no isomorphic replacement
or full-stage ambient K_S is postulated. The original repeated
masks are retained by positional list decomposition.

What remains is extracting an active interval and assembling
these shifts into a separated normalized smaller-M chain quotient.
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

/-- At EVERY interior position of the original finite separated
chain, two genuine adjacent boundary parameters belonging to the
same M-component have a unique normalized K_(M∩A) displacement
in their exact shared historical Cayley block. -/
theorem buildNonempty_consecutive_unique_interior_shift
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := linkedAlignedBuildNonempty D S old L M atoms hne hsep
    ∀ (P Q : AlignedNamedBoundary D S old L M
        H.data.boundaryHistory.chain)
      (pref suffix : List (AlignedNamedBoundary D S old L M
        H.data.boundaryHistory.chain))
      (hpair : H.data.aligned = pref ++ P :: Q :: suffix)
      (q : H.data.boundaryHistory.chain.state.Space)
      (k : (old (common S P.boundary.leftMask
        P.boundary.rightMask)).Carrier)
      (l : (old (common S Q.boundary.leftMask
        Q.boundary.rightMask)).Carrier)
      (hk : LabelReach
        (fun e => (H.data.boundaryHistory.chain.state.matching e).Rel)
        M.val q (P.boundary.interfaceMap D S old L k))
      (hl : LabelReach
        (fun e => (H.data.boundaryHistory.chain.state.matching e).Rel)
        M.val q (Q.boundary.interfaceMap D S old L l)),
      ∃ x y : (old P.rightNamed.source).Carrier,
        P.rightNamed.chart.embed x =
          P.boundary.interfaceMap D S old L k ∧
        P.rightNamed.chart.embed y =
          Q.boundary.interfaceMap D S old L l ∧
        ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
          x * (L (Step.meet S M P.rightNamed.source)
            P.rightNamed.source Finset.inter_subset_right).incl shift = y := by
  intro H P Q pref suffix hpair q k l hk hl
  have hMiddle : P.rightNamed = Q.leftNamed :=
    buildNonempty_adjacent_middle_eq
      D S old L M atoms hne hsep P Q pref suffix hpair
  exact P.adjacent_unique_interior_shift
    D S old L Q hMiddle q k l hk hl

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
