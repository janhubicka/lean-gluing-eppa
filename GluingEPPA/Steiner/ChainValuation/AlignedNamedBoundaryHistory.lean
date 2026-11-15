import GluingEPPA.Steiner.ChainValuation.HistoricalBoundaryNamedBridge
import GluingEPPA.Steiner.ChainValuation.FiniteWitnessedHistoricalBoundaries

/-!
# A single genuine historical boundary with both named Cayley charts

The original recursive chain supplies one actual boundary record
for each attachment. Its source-named Cayley charts are not arbitrary:
each old/new endpoint map of the boundary is exactly the chart of
its corresponding original historical K_A or K_B block.

Store the two named charts and the whole boundary in one record,
with the point-image agreement certified in the literal quotient.
These records transport together through a genuine LinkChain step.

A finite history retaining ALL such records is assembled below,
without discarding or reindexing any original boundary.
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

/-- A *single actual recorded* historical Link interface, paired with
both named earlier Cayley blocks to which its endpoints belong.
The agreement holds in the same original quotient state. -/
structure AlignedNamedBoundary
    (M : Proper S) (R : BuildResult D S old L) where
  boundary : HistoricalLinkBoundary D S old L M R
  leftNamed : NamedHistoricalBlock D S old L M R
  rightNamed : NamedHistoricalBlock D S old L M R
  agree : boundary.AgreesWithNamed D S old L leftNamed rightNamed

/-- Transport all three actual embeddings through a later
LinkChain.step. The source masks and matching of complete image
ranges are unchanged by the common old-chain injection. -/
noncomputable def AlignedNamedBoundary.transport
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    AlignedNamedBoundary D S old L M (step D S old L R y hsep) where
  boundary := P.boundary.transport D S old L y hsep hcoset
  leftNamed := namedHistoricalTransport D S old L M R y hsep
    hcoset P.leftNamed
  rightNamed := namedHistoricalTransport D S old L M R y hsep
    hcoset P.rightNamed
  agree := P.boundary.transport_agreesWithNamed D S old L
    P.leftNamed P.rightNamed P.agree y hsep hcoset

/-- The literal new LinkChain.step supplies the next boundary and
both its true named source blocks, all in the same pushout. -/
noncomputable def alignedNamedBoundaryFresh
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    AlignedNamedBoundary D S old L M
      (step D S old L R y hsep) where
  boundary := historicalLinkBoundary_step D S old L M R y hsep hcoset
  leftNamed := namedHistoricalTransport D S old L M R y hsep hcoset
    (namedHistoricalLast D S old L M R hcoset)
  rightNamed := namedHistoricalLast D S old L M
    (step D S old L R y hsep)
    (step_lastMaskCoset D S old L M R y hsep hcoset)
  agree := historicalStep_boundary_named_agree
    D S old L M R y hsep hcoset

/-- One original boundary-history builder with ALL its genuine
named left/right charts attached. Forgetting those extra chart
certificates gives exactly the earlier checked boundary list. -/
structure AlignedNamedHistory (M : Proper S) where
  boundaryHistory : BoundaryHistoryBuildResult D S old L M
  aligned : List (AlignedNamedBoundary
    D S old L M boundaryHistory.chain)
  forget :
    aligned.map (fun B => B.boundary) = boundaryHistory.boundaries

/-- A one-block original chain has no historical boundary. -/
noncomputable def alignedNamedInitial
    (M : Proper S) (x : Atom S old) :
    AlignedNamedHistory D S old L M where
  boundaryHistory := boundaryHistoryInitial D S old L M x
  aligned := []
  forget := rfl

/-- One genuine separated attachment transports EVERY old aligned
boundary, and adds exactly the newly certified boundary. The
forgetful law is maintained through the same original pushout. -/
noncomputable def alignedNamedStep
    (M : Proper S) (H : AlignedNamedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.boundaryHistory.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.boundaryHistory.chain.current y) :
    AlignedNamedHistory D S old L M := by
  let R := H.boundaryHistory.chain
  let hcoset := H.boundaryHistory.lastInv
  let nextHistory := boundaryHistoryStep D S old L M H.boundaryHistory y hsep
  let P' := H.aligned.map (fun P =>
    P.transport D S old L y hsep hcoset) ++
    [alignedNamedBoundaryFresh D S old L M R y hsep hcoset]
  refine
    { boundaryHistory := nextHistory
      aligned := P'
      forget := ?_ }
  change
    (H.aligned.map (fun P =>
      P.transport D S old L y hsep hcoset) ++
      [alignedNamedBoundaryFresh D S old L M R y hsep hcoset]).map
        (fun P => P.boundary) =
      (boundaryHistoryStep D S old L M H.boundaryHistory y hsep).boundaries
  simp only [List.map_append, List.map_map, List.map_singleton]
  change
    (H.aligned.map (fun P =>
      (P.boundary.transport D S old L y hsep hcoset))) ++
      [historicalLinkBoundary_step D S old L M R y hsep hcoset] =
    H.boundaryHistory.boundaries.map (fun B =>
      B.transport D S old L y hsep hcoset) ++
      [historicalLinkBoundary_step D S old L M R y hsep hcoset]
  rw [← H.forget]
  simp only [List.map_map]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
