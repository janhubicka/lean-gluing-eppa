import GluingEPPA.Steiner.ChainValuation.LinkedCoveredNamedHistory
import GluingEPPA.Steiner.ChainValuation.PointwiseNamedBoundaryCharts

/-!
# Pointwise original Cayley coordinates on the COVERED named history

The already checked covered source-named LinkChain history records
each genuine historical Cayley block, every original boundary,
complete M-component coverage and exact positional correspondence.
Linkedness of its consecutive boundaries is also checked.

The normalized proper-M chain needs the stronger condition that
EVERY historical boundary map agrees POINTWISE with the
corresponding original named Cayley chart, not merely that their
ranges are equal. This was proved for a separately enriched
boundary history; here it is carried directly on the SAME covered
named history, avoiding a late identification of two dependent
quotients.

The resulting finite theorem provides the exact original
entry/exit group coordinates needed by the noncommutative
normalized triple-separation calculation, while retaining
repeated source-mask occurrences and the original completed
matching family.
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

/-- Pointwise correctness of both genuine historical boundary
source coordinates, on the exact covered named LinkChain state. -/
def CoveredNamedAlignedHistory.AllPointwise
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M) : Prop :=
  ∀ P : AlignedNamedBoundary D S old L M H.named.data.chain,
    P ∈ H.aligned →
      P.boundary.PointwiseNamed D S old L
        P.leftNamed P.rightNamed P.agree

/-- Each literal original LinkChain.step transports all old
pointwise source-chart equalities and appends the true new
boundary with its original source-coordinate equations. -/
theorem coveredNamedAlignedStep_allPointwise
    (M : Proper S)
    (H : CoveredNamedAlignedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.named.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
        H.named.data.chain.current y)
    (hOld : H.AllPointwise D S old L) :
    (coveredNamedAlignedStep D S old L M H y hsep).AllPointwise
      D S old L := by
  intro P hP
  have hmem : P ∈
      H.aligned.map (fun U =>
        U.transport D S old L y hsep H.named.data.lastInv) ++
      [alignedNamedBoundaryFresh D S old L M H.named.data.chain
        y hsep H.named.data.lastInv] := hP
  rcases List.mem_append.mp hmem with hPrev | hNew
  · obtain ⟨U, hU, hEq⟩ := List.mem_map.mp hPrev
    subst P
    exact U.boundary.transport_pointwiseNamed D S old L
      U.leftNamed U.rightNamed U.agree (hOld U hU)
      y hsep H.named.data.lastInv
  · have hEq : P = alignedNamedBoundaryFresh
        D S old L M H.named.data.chain
        y hsep H.named.data.lastInv :=
      List.mem_singleton.mp hNew
    subst P
    exact historicalStep_boundary_named_pointwise
      D S old L M H.named.data.chain
      y hsep H.named.data.lastInv

/-- The actual covered named source-block and boundary record,
enhanced solely by the valid pointwise old-coordinate proof. -/
structure PointwiseCoveredNamedHistory (M : Proper S) where
  data : CoveredNamedAlignedHistory D S old L M
  pointwise : data.AllPointwise D S old L

noncomputable def pointwiseCoveredNamedInitial
    (M : Proper S) (x : Atom S old) :
    PointwiseCoveredNamedHistory D S old L M where
  data := coveredNamedAlignedInitial D S old L M x
  pointwise := by
    intro P hP
    cases hP

noncomputable def pointwiseCoveredNamedStep
    (M : Proper S) (H : PointwiseCoveredNamedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.data.named.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
        H.data.named.data.chain.current y) :
    PointwiseCoveredNamedHistory D S old L M where
  data := coveredNamedAlignedStep D S old L M H.data y hsep
  pointwise := coveredNamedAlignedStep_allPointwise
    D S old L M H.data y hsep H.pointwise

/-- Iterate the genuine pointwise original-coordinate invariant
through each remaining separated original LinkChain attachment. -/
noncomputable def pointwiseCoveredNamedBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : PointwiseCoveredNamedHistory D S old L M)
    (hp : H.data.named.data.chain.previous = some p)
    (hc : H.data.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    PointwiseCoveredNamedHistory D S old L M := by
  induction rest generalizing p c H with
  | nil =>
      exact H
  | cons z zs ih =>
      have hstep :
          (match H.data.named.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := pointwiseCoveredNamedStep D S old L M H z hstep
      have hnp : HN.data.named.data.chain.previous = some c := by
        change some H.data.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.named.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- All genuine original historical boundaries of one finite
separated LinkChain retain the exact original Cayley coordinates. -/
noncomputable def pointwiseCoveredNamedBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    PointwiseCoveredNamedHistory D S old L M := by
  cases atoms with
  | nil =>
      exact False.elim (hatoms rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact pointwiseCoveredNamedInitial D S old L M x
      | cons y ys =>
          let H0 := pointwiseCoveredNamedInitial D S old L M x
          let H1 := pointwiseCoveredNamedStep D S old L M H0 y trivial
          have hp : H1.data.named.data.chain.previous = some x := rfl
          have hc : H1.data.named.data.chain.current = y := rfl
          exact pointwiseCoveredNamedBuildTail
            D S old L M x y H1 hp hc ys hsep

/-- Forgetting pointwise certificates recovers exactly the
existing covered named historical tail recursion and quotient. -/
theorem pointwiseCoveredNamedBuildTail_data_eq
    (M : Proper S) (p c : Atom S old)
    (H : PointwiseCoveredNamedHistory D S old L M)
    (hp : H.data.named.data.chain.previous = some p)
    (hc : H.data.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (pointwiseCoveredNamedBuildTail D S old L M
      p c H hp hc rest hsep).data =
    coveredNamedAlignedBuildTail D S old L M
      p c H.data hp hc rest hsep := by
  induction rest generalizing p c H with
  | nil =>
      rfl
  | cons z zs ih =>
      have hstep :
          (match H.data.named.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := pointwiseCoveredNamedStep D S old L M H z hstep
      have hnp : HN.data.named.data.chain.previous = some c := by
        change some H.data.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.named.data.chain.current = z := rfl
      change
        (pointwiseCoveredNamedBuildTail D S old L M
          c z HN hnp hnc zs hsep.2).data =
        coveredNamedAlignedBuildTail D S old L M
          c z HN.data hnp hnc zs hsep.2
      exact ih c z HN hnp hnc hsep.2

/-- The completed pointwise history forgets to the EXACT same
covered source-named finite history whose component coverage,
active interval and linked boundary list were already verified. -/
theorem pointwiseCoveredNamedBuildNonempty_data_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (pointwiseCoveredNamedBuildNonempty D S old L M
      atoms hatoms hsep).data =
    coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep := by
  cases atoms with
  | nil =>
      exact False.elim (hatoms rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          rfl
      | cons y ys =>
          let H0 := pointwiseCoveredNamedInitial D S old L M x
          let H1 := pointwiseCoveredNamedStep D S old L M H0 y trivial
          have hp : H1.data.named.data.chain.previous = some x := rfl
          have hc : H1.data.named.data.chain.current = y := rfl
          change
            (pointwiseCoveredNamedBuildTail D S old L M
              x y H1 hp hc ys hsep).data =
            coveredNamedAlignedBuildTail D S old L M
              x y H1.data hp hc ys hsep
          exact pointwiseCoveredNamedBuildTail_data_eq
            D S old L M x y H1 hp hc ys hsep

/-- In the canonical genuine finite LinkChain, the covered named
historical block list and ALL actual aligned interfaces have
pointwise correct original Cayley coordinates, WITHOUT a new
independent chain state or a free additional hypothesis. -/
theorem coveredNamedAlignedBuildNonempty_allPointwise
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep
    H.AllPointwise D S old L := by
  let H := pointwiseCoveredNamedBuildNonempty
    D S old L M atoms hatoms hsep
  have hEq : H.data =
      coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep :=
    pointwiseCoveredNamedBuildNonempty_data_eq
      D S old L M atoms hatoms hsep
  rw [← hEq]
  exact H.pointwise

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
