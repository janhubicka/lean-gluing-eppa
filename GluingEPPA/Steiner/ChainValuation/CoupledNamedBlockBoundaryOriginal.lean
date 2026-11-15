import GluingEPPA.Steiner.ChainValuation.CoupledNamedBlockBoundaryHistory
import GluingEPPA.Steiner.ChainValuation.BoundaryHistoryOriginalCorrespondence

/-!
# The coupled block/boundary history is the literal original chain

The block/boundary coupled recursion of the previous module carries
an exact equality between the entire named Cayley-block list and
the list reconstructed from genuine historical boundaries. Here
we verify it is not a replacement chain construction.

Forgetting the named blocks and the extra endpoint-chart
certificates yields exactly the earlier verified
BoundaryHistoryBuildResult at every genuine LinkChain.step,
and hence throughout the entire original finite separated list.
The final dependent SomeState is therefore the manuscript's
literal LinkChain.buildNonempty quotient and genuine letter
matching family.

This makes the block/boundary occurrence equality available on
the actual original finite tests, rather than on an auxiliary
pushout equipped with unspecified group-coordinate identifications.
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

/-- Forget the source-named Cayley-block list and all extra
boundary endpoint charts, keeping only the actual original
BuildResult, the last-mask coset invariant, and the COMPLETE
genuine historical Link boundary list. -/
def CoupledNamedBlockBoundaryHistory.toBoundaryHistory
    {M : Proper S}
    (H : CoupledNamedBlockBoundaryHistory D S old L M) :
    BoundaryHistoryBuildResult D S old L M where
  chain := H.chain
  lastInv := H.lastInv
  boundaries := H.boundaries.map (fun B => B.boundary)

/-- The true one-block source/boundary history forgets to
the genuine earlier singleton boundary-history builder. -/
theorem coupledNamedBlockBoundaryInitial_toBoundaryHistory
    (M : Proper S) (x : Atom S old) :
    (coupledNamedBlockBoundaryInitial
      D S old L M x).toBoundaryHistory D S old L =
      boundaryHistoryInitial D S old L M x := rfl

/-- Forgetting a true coupled named-block/boundary step gives
exactly the already verified ORIGINAL boundaryHistoryStep.

The only nontrivial list calculation is the functoriality of
List.map under transporting earlier boundary records. -/
theorem coupledNamedBlockBoundaryStep_toBoundaryHistory
    (M : Proper S)
    (H : CoupledNamedBlockBoundaryHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.chain.current y) :
    (coupledNamedBlockBoundaryStep
      D S old L M H y hsep).toBoundaryHistory D S old L =
    boundaryHistoryStep D S old L M
      (H.toBoundaryHistory D S old L) y hsep := by
  simp only [CoupledNamedBlockBoundaryHistory.toBoundaryHistory,
    coupledNamedBlockBoundaryStep, boundaryHistoryStep,
    historicalBoundaries_step, List.map_append, List.map_map,
    List.map_singleton, Function.comp_def]
  rfl

/-- The original finite separated tail has exactly the same
boundary-history data after forgetting the coupled source-block
certificates. This is literal dependent record equality. -/
theorem coupledNamedBlockBoundaryBuildTail_toBoundaryHistory
    (M : Proper S) (p c : Atom S old)
    (H : CoupledNamedBlockBoundaryHistory D S old L M)
    (hp : H.chain.previous = some p)
    (hc : H.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (coupledNamedBlockBoundaryBuildTail D S old L M
      p c H hp hc rest hsep).toBoundaryHistory D S old L =
    boundaryHistoryBuildTail D S old L M
      p c (H.toBoundaryHistory D S old L) hp hc
      rest hsep := by
  induction rest generalizing p c H with
  | nil => rfl
  | cons z zs ih =>
      have hstep :
          (match H.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous H.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coupledNamedBlockBoundaryStep
        D S old L M H z hstep
      have hnp : HN.chain.previous = some c := by
        change some H.chain.current = some c
        rw [hc]
      have hnc : HN.chain.current = z := rfl
      change
        (coupledNamedBlockBoundaryBuildTail
          D S old L M c z HN hnp hnc zs hsep.2).toBoundaryHistory
          D S old L =
        boundaryHistoryBuildTail D S old L M c z
          (boundaryHistoryStep D S old L M
            (H.toBoundaryHistory D S old L) z hstep)
          hnp hnc zs hsep.2
      rw [← coupledNamedBlockBoundaryStep_toBoundaryHistory
        D S old L M H z hstep]
      exact ih c z HN hnp hnc hsep.2

/-- The complete coupled finite history forgets exactly to the
previously verified boundaryHistoryBuildNonempty builder,
without changing source indices or the original quotient. -/
theorem coupledNamedBlockBoundaryBuildNonempty_toBoundaryHistory
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coupledNamedBlockBoundaryBuildNonempty D S old L M
      atoms hne hsep).toBoundaryHistory D S old L =
      boundaryHistoryBuildNonempty D S old L M
        atoms hne hsep := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          let H0 := coupledNamedBlockBoundaryInitial D S old L M x
          let H1 := coupledNamedBlockBoundaryStep D S old L M H0 y trivial
          have hp : H1.chain.previous = some x := rfl
          have hc : H1.chain.current = y := rfl
          have hfirst : H1.toBoundaryHistory D S old L =
              boundaryHistoryStep D S old L M
                (boundaryHistoryInitial D S old L M x)
                y trivial := by
            exact coupledNamedBlockBoundaryStep_toBoundaryHistory
              D S old L M H0 y trivial
          change
            (coupledNamedBlockBoundaryBuildTail
              D S old L M x y H1 hp hc ys hsep).toBoundaryHistory
                D S old L =
            boundaryHistoryBuildTail D S old L M x y
              (boundaryHistoryStep D S old L M
                (boundaryHistoryInitial D S old L M x)
                y trivial) hp hc ys hsep
          rw [← hfirst]
          exact coupledNamedBlockBoundaryBuildTail_toBoundaryHistory
            D S old L M x y H1 hp hc ys hsep

/-- The SOURCE-BLOCK/BOUNDARY-COHERENT finite history realizes
the actual manuscript LinkChain.buildNonempty, point carrier,
current atom and genuine completed matching included. -/
theorem coupledNamedBlockBoundaryBuildNonempty_original
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coupledNamedBlockBoundaryBuildNonempty
      D S old L M atoms hne hsep
    (⟨H.chain.current, H.chain.state⟩ : SomeState S old) =
      buildNonempty D S old L atoms hne hsep := by
  let H := coupledNamedBlockBoundaryBuildNonempty
    D S old L M atoms hne hsep
  have hEq : H.toBoundaryHistory D S old L =
      boundaryHistoryBuildNonempty D S old L M atoms hne hsep :=
    coupledNamedBlockBoundaryBuildNonempty_toBoundaryHistory
      D S old L M atoms hne hsep
  have hpoints :
      (⟨H.chain.current, H.chain.state⟩ : SomeState S old) =
      (⟨(boundaryHistoryBuildNonempty D S old L M
          atoms hne hsep).chain.current,
         (boundaryHistoryBuildNonempty D S old L M
          atoms hne hsep).chain.state⟩ : SomeState S old) :=
    congrArg
      (fun B : BoundaryHistoryBuildResult D S old L M =>
        (⟨B.chain.current, B.chain.state⟩ : SomeState S old))
      hEq
  exact hpoints.trans
    (boundaryHistoryBuildNonempty_original
      D S old L M atoms hne hsep)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
