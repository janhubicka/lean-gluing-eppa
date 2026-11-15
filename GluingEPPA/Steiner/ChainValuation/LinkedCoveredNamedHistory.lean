import GluingEPPA.Steiner.ChainValuation.CoveredNamedAlignedHistory
import GluingEPPA.Steiner.ChainValuation.LinkedAlignedBoundaryHistory

/-!
# Link consecutive boundaries inside the covered source-named history

The original covered source-named history now contains the exact
ordered list of actual named Cayley blocks AND its corresponding
historical boundaries. We must also certify that any two consecutive
genuine boundaries use the IDENTICAL middle named chart.

This module adds that linkedness as an invariant of the SAME
covered named history, not a second independently built quotient.
The last boundary's right named chart remains the actual last
Cayley block, which is precisely the condition needed when
appending the next original Link attachment.

Consequently the positional internal-boundary theorem can be used
on the original active-component interval without adding an
unproved linkedness assumption or identifying duplicate masks.
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

/-- The SAME covered original named source history, now including
literal equality of historical middle Cayley charts at consecutive
boundary occurrences and its true last-block endpoint. -/
structure LinkedCoveredNamedHistory (M : Proper S) where
  data : CoveredNamedAlignedHistory D S old L M
  linked : AlignedBoundaryList.Linked D S old L data.aligned
  last : AlignedBoundaryList.EndsAt D S old L
    (namedHistoricalLast D S old L M
      data.named.data.chain data.named.data.lastInv)
    data.aligned

/-- One original Cayley block has no historical interfaces. -/
noncomputable def linkedCoveredNamedInitial
    (M : Proper S) (x : Atom S old) :
    LinkedCoveredNamedHistory D S old L M where
  data := coveredNamedAlignedInitial D S old L M x
  linked := trivial
  last := trivial

/-- The literal original LinkChain.step preserves all old
middle-chart equalities and makes the previous last named
Cayley chart the left endpoint of the new genuine boundary. -/
noncomputable def linkedCoveredNamedStep
    (M : Proper S) (H : LinkedCoveredNamedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.data.named.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
        H.data.named.data.chain.current y) :
    LinkedCoveredNamedHistory D S old L M := by
  let R := H.data.named.data.chain
  let hcoset := H.data.named.data.lastInv
  let oldLast := namedHistoricalLast D S old L M R hcoset
  let transported := H.data.aligned.map (fun P =>
    P.transport D S old L y hsep hcoset)
  let fresh := alignedNamedBoundaryFresh
    D S old L M R y hsep hcoset
  have hLinked : AlignedBoundaryList.Linked D S old L transported :=
    alignedBoundaryList_transport_linked D S old L
      H.data.aligned H.linked y hsep hcoset
  have hEnd : AlignedBoundaryList.EndsAt D S old L
      (namedHistoricalTransport D S old L M R y hsep hcoset oldLast)
      transported :=
    alignedBoundaryList_transport_end D S old L
      H.data.aligned oldLast H.last y hsep hcoset
  have hMiddle :
      namedHistoricalTransport D S old L M R y hsep hcoset oldLast =
        fresh.leftNamed := rfl
  refine
    { data := coveredNamedAlignedStep D S old L M H.data y hsep
      linked := ?_
      last := ?_ }
  · change AlignedBoundaryList.Linked D S old L
      (transported ++ [fresh])
    exact alignedBoundaryList_append D S old L
      transported _ fresh hLinked hEnd hMiddle
  · change AlignedBoundaryList.EndsAt D S old L
      fresh.rightNamed (transported ++ [fresh])
    exact alignedBoundaryList_append_end D S old L
      transported fresh

/-- Entire literal finite tail with the linkedness and last-block
certificates preserved alongside the already covered history. -/
noncomputable def linkedCoveredNamedBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : LinkedCoveredNamedHistory D S old L M)
    (hp : H.data.named.data.chain.previous = some p)
    (hc : H.data.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    LinkedCoveredNamedHistory D S old L M := by
  induction rest generalizing p c H with
  | nil => exact H
  | cons z zs ih =>
      have hstep :
          (match H.data.named.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := linkedCoveredNamedStep D S old L M H z hstep
      have hnp : HN.data.named.data.chain.previous = some c := by
        change some H.data.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.named.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- All genuine original finite separated LinkChain block and
boundary occurrences remain linked and source-named in one
covered history. -/
noncomputable def linkedCoveredNamedBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    LinkedCoveredNamedHistory D S old L M := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => exact linkedCoveredNamedInitial D S old L M x
      | cons y ys =>
          let H0 := linkedCoveredNamedInitial D S old L M x
          let H1 := linkedCoveredNamedStep D S old L M H0 y trivial
          have hp : H1.data.named.data.chain.previous = some x := rfl
          have hc : H1.data.named.data.chain.current = y := rfl
          exact linkedCoveredNamedBuildTail D S old L M
            x y H1 hp hc ys hsep

/-- The linked extra data does not change the previously covered
named+aligned history, including its actual finite quotient. -/
theorem linkedCoveredNamedBuildTail_data_eq
    (M : Proper S) (p c : Atom S old)
    (H : LinkedCoveredNamedHistory D S old L M)
    (hp : H.data.named.data.chain.previous = some p)
    (hc : H.data.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (linkedCoveredNamedBuildTail D S old L M
      p c H hp hc rest hsep).data =
    coveredNamedAlignedBuildTail D S old L M
      p c H.data hp hc rest hsep := by
  induction rest generalizing p c H with
  | nil => rfl
  | cons z zs ih =>
      have hstep :
          (match H.data.named.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := linkedCoveredNamedStep D S old L M H z hstep
      have hnp : HN.data.named.data.chain.previous = some c := by
        change some H.data.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.named.data.chain.current = z := rfl
      change
        (linkedCoveredNamedBuildTail D S old L M c z
          HN hnp hnc zs hsep.2).data =
        coveredNamedAlignedBuildTail D S old L M c z
          HN.data hnp hnc zs hsep.2
      exact ih c z HN hnp hnc hsep.2

/-- The FULL finite linked history forgets to precisely the
previously constructed covered named+aligned history. -/
theorem linkedCoveredNamedBuildNonempty_data_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (linkedCoveredNamedBuildNonempty D S old L M
      atoms hne hsep).data =
      coveredNamedAlignedBuildNonempty D S old L M
        atoms hne hsep := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          let H0 := linkedCoveredNamedInitial D S old L M x
          let H1 := linkedCoveredNamedStep D S old L M H0 y trivial
          have hp : H1.data.named.data.chain.previous = some x := rfl
          have hc : H1.data.named.data.chain.current = y := rfl
          change
            (linkedCoveredNamedBuildTail D S old L M x y
              H1 hp hc ys hsep).data =
            coveredNamedAlignedBuildTail D S old L M x y
              H1.data hp hc ys hsep
          exact linkedCoveredNamedBuildTail_data_eq
            D S old L M x y H1 hp hc ys hsep

/-- The covered original finite history carries linkedness of
all its true historical boundary occurrences, with no extra
hypothesis. In particular any positional active interval may
now select its own genuine internal boundaries unambiguously. -/
theorem coveredNamedAlignedBuildNonempty_linked
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty
      D S old L M atoms hne hsep
    AlignedBoundaryList.Linked D S old L H.aligned := by
  let H := linkedCoveredNamedBuildNonempty
    D S old L M atoms hne hsep
  have hEq : H.data =
      coveredNamedAlignedBuildNonempty D S old L M
        atoms hne hsep :=
    linkedCoveredNamedBuildNonempty_data_eq
      D S old L M atoms hne hsep
  rw [← hEq]
  exact H.linked

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
