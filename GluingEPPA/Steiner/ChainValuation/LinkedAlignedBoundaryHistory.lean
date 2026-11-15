import GluingEPPA.Steiner.ChainValuation.AlignedNamedBoundaryFinite

/-!
# Consecutive aligned Link boundaries share one literal middle Cayley chart

The finite aligned historical records retain the same original
boundary list but previously certified only point ranges, not
that each consecutive pair uses the SAME named middle block chart.

We record this stronger invariant separately, preserving the
original historical data. One new LinkChain.step transports the
old consecutive links and appends a fresh interface whose left
named chart is exactly the transport of the previous rightmost
historical Cayley chart.

The invariant does not choose any normalized M-coset
representatives and assumes no universal ambient group.
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

/-- The corresponding two historical source-block records at
consecutive original boundaries are LITERALLY equal. -/
def AlignedBoundaryList.Linked
    {M : Proper S} {R : BuildResult D S old L} :
    List (AlignedNamedBoundary D S old L M R) → Prop
  | [] => True
  | [_] => True
  | P :: Q :: rest =>
      P.rightNamed = Q.leftNamed ∧
      AlignedBoundaryList.Linked (Q :: rest)

/-- The last historical boundary's right chart is the named
last source-block chart of the entire current original chain. -/
def AlignedBoundaryList.EndsAt
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R) :
    List (AlignedNamedBoundary D S old L M R) → Prop
  | [] => True
  | [P] => P.rightNamed = T
  | _ :: Q :: rest => AlignedBoundaryList.EndsAt T (Q :: rest)

/-- Every later genuine attachment preserves literal equality
of the named middle block at consecutive historical boundaries. -/
theorem alignedBoundaryList_transport_linked
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R))
    (hlink : AlignedBoundaryList.Linked D S old L hist)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    AlignedBoundaryList.Linked D S old L
      (hist.map (fun P =>
        P.transport D S old L y hsep hcoset)) := by
  induction hist with
  | nil => trivial
  | cons P rest ih =>
      cases rest with
      | nil => trivial
      | cons Q tail =>
          change P.rightNamed = Q.leftNamed ∧
            AlignedBoundaryList.Linked D S old L (Q :: tail) at hlink
          change
            (namedHistoricalTransport D S old L M R y hsep hcoset P.rightNamed) =
              (namedHistoricalTransport D S old L M R y hsep hcoset Q.leftNamed) ∧
            AlignedBoundaryList.Linked D S old L
              ((Q :: tail).map (fun B =>
                B.transport D S old L y hsep hcoset))
          exact ⟨congrArg (namedHistoricalTransport
            D S old L M R y hsep hcoset) hlink.1, ih hlink.2⟩

/-- The rightmost chart in an aligned historical list is
transported by the identical original LinkChain old embedding. -/
theorem alignedBoundaryList_transport_end
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R))
    (last : NamedHistoricalBlock D S old L M R)
    (hend : AlignedBoundaryList.EndsAt D S old L last hist)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    AlignedBoundaryList.EndsAt D S old L
      (namedHistoricalTransport D S old L M R y hsep hcoset last)
      (hist.map (fun P =>
        P.transport D S old L y hsep hcoset)) := by
  induction hist with
  | nil => trivial
  | cons P rest ih =>
      cases rest with
      | nil =>
          change P.rightNamed = last at hend
          change (namedHistoricalTransport D S old L M R
            y hsep hcoset P.rightNamed) =
            namedHistoricalTransport D S old L M R y hsep hcoset last
          exact congrArg (namedHistoricalTransport
            D S old L M R y hsep hcoset) hend
      | cons Q tail =>
          exact ih hend

/-- Append a new original historical interface after a list
whose last right named chart is its new left named chart. -/
theorem alignedBoundaryList_append
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R)) :
    ∀ (T : NamedHistoricalBlock D S old L M R)
      (new : AlignedNamedBoundary D S old L M R),
      AlignedBoundaryList.Linked D S old L hist →
      AlignedBoundaryList.EndsAt D S old L T hist →
      T = new.leftNamed →
      AlignedBoundaryList.Linked D S old L (hist ++ [new]) := by
  induction hist with
  | nil =>
      intro _ _ _ _ _
      trivial
  | cons P rest ih =>
      cases rest with
      | nil =>
          intro T new _ hend hnew
          change P.rightNamed = new.leftNamed ∧ True
          exact ⟨hend.trans hnew, trivial⟩
      | cons Q tail =>
          intro T new hlink hend hnew
          change P.rightNamed = Q.leftNamed ∧
            AlignedBoundaryList.Linked D S old L
              (Q :: tail ++ [new])
          exact ⟨hlink.1, ih T new hlink.2 hend hnew⟩

/-- The new rightmost chart is the right-hand named chart of the
freshly appended boundary, regardless of the preceding history. -/
theorem alignedBoundaryList_append_end
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R))
    (new : AlignedNamedBoundary D S old L M R) :
    AlignedBoundaryList.EndsAt D S old L new.rightNamed
      (hist ++ [new]) := by
  induction hist with
  | nil => trivial
  | cons P rest ih =>
      cases rest with
      | nil => rfl
      | cons Q tail => exact ih

/-- A genuine finite boundary history together with the stronger
literal adjacency and final-block chart invariants. -/
structure LinkedAlignedHistory (M : Proper S) where
  data : AlignedNamedHistory D S old L M
  linked : AlignedBoundaryList.Linked D S old L data.aligned
  last :
    AlignedBoundaryList.EndsAt D S old L
      (namedHistoricalLast D S old L M
        data.boundaryHistory.chain data.boundaryHistory.lastInv)
      data.aligned

/-- The one-block original chain has no boundaries and
therefore satisfies both linked-history invariants. -/
noncomputable def linkedAlignedInitial
    (M : Proper S) (x : Atom S old) :
    LinkedAlignedHistory D S old L M where
  data := alignedNamedInitial D S old L M x
  linked := trivial
  last := trivial

/-- The exact genuine LinkChain step simultaneously preserves
literal middle-chart consistency at every historical boundary,
and matches the new last chart to the appended interface. -/
noncomputable def linkedAlignedStep
    (M : Proper S) (H : LinkedAlignedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.data.boundaryHistory.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
          H.data.boundaryHistory.chain.current y) :
    LinkedAlignedHistory D S old L M := by
  let R := H.data.boundaryHistory.chain
  let hcoset := H.data.boundaryHistory.lastInv
  let last := namedHistoricalLast D S old L M R hcoset
  let fresh := alignedNamedBoundaryFresh D S old L M R y hsep hcoset
  let transported := H.data.aligned.map (fun P =>
    P.transport D S old L y hsep hcoset)
  have hlinked : AlignedBoundaryList.Linked D S old L transported :=
    alignedBoundaryList_transport_linked D S old L
      H.data.aligned H.linked y hsep hcoset
  have hend : AlignedBoundaryList.EndsAt D S old L
      (namedHistoricalTransport D S old L M R y hsep hcoset last)
      transported :=
    alignedBoundaryList_transport_end D S old L
      H.data.aligned last H.last y hsep hcoset
  have hmiddle :
      namedHistoricalTransport D S old L M R y hsep hcoset last =
        fresh.leftNamed := rfl
  refine
    { data := alignedNamedStep D S old L M H.data y hsep
      linked := ?_
      last := ?_ }
  · change AlignedBoundaryList.Linked D S old L
      (transported ++ [fresh])
    exact alignedBoundaryList_append D S old L transported
      _ fresh hlinked hend hmiddle
  · change AlignedBoundaryList.EndsAt D S old L
      fresh.rightNamed (transported ++ [fresh])
    exact alignedBoundaryList_append_end D S old L transported fresh

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
