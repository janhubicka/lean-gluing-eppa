import GluingEPPA.Steiner.ChainValuation.PointwiseNamedBoundaryCharts
import GluingEPPA.Steiner.ChainValuation.AlignedNamedBoundaryFinite

/-!
# Pointwise named source coordinates at every finite historical boundary

Earlier alignment certified that each original historical interface
has the same source-mask names and the same embedded Cayley-block
ranges as its two named historical blocks. The new pointwise bridge
strengthens this to equality of the *actual embedding maps* under
the canonical source-mask equality casts.

This module carries that strong property through the original
finite LinkChain pair/next/tail recursion and proves that forgetting
the certificates recovers exactly alignedNamedBuildNonempty, and
hence the original manuscript's dependent quotient state.

The pointwise property is needed to read both entering and
outgoing interface parameters in their genuine original middle
group coordinates before applying normalized triple separation.
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

/-- All original historical boundary charts have pointwise
source-coordinate agreement with both named Cayley blocks. -/
def AlignedNamedHistory.AllPointwise
    {M : Proper S} (H : AlignedNamedHistory D S old L M) : Prop :=
  ∀ P : AlignedNamedBoundary D S old L M H.boundaryHistory.chain,
    P ∈ H.aligned →
      P.boundary.PointwiseNamed D S old L
        P.leftNamed P.rightNamed P.agree

/-- One original separated LinkChain step preserves the pointwise
agreement for EVERY old interface and provides the fresh interface
with its actual original source group coordinates. -/
theorem alignedNamedStep_allPointwise
    (M : Proper S) (H : AlignedNamedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.boundaryHistory.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
        H.boundaryHistory.chain.current y)
    (hOld : H.AllPointwise D S old L) :
    (alignedNamedStep D S old L M H y hsep).AllPointwise
      D S old L := by
  intro P hP
  have hmem : P ∈
      H.aligned.map (fun U =>
        U.transport D S old L y hsep H.boundaryHistory.lastInv) ++
      [alignedNamedBoundaryFresh D S old L M H.boundaryHistory.chain
        y hsep H.boundaryHistory.lastInv] := hP
  rcases List.mem_append.mp hmem with hPrev | hNew
  · obtain ⟨U, hU, hEq⟩ := List.mem_map.mp hPrev
    subst P
    exact U.boundary.transport_pointwiseNamed D S old L
      U.leftNamed U.rightNamed U.agree (hOld U hU)
      y hsep H.boundaryHistory.lastInv
  · have hEq : P = alignedNamedBoundaryFresh
        D S old L M H.boundaryHistory.chain
        y hsep H.boundaryHistory.lastInv :=
      List.mem_singleton.mp hNew
    subst P
    exact historicalStep_boundary_named_pointwise
      D S old L M H.boundaryHistory.chain
      y hsep H.boundaryHistory.lastInv

/-- The original aligned historical record with proofs that each
of its named source-block charts matches its boundary pointwise. -/
structure PointwiseAlignedHistory (M : Proper S) where
  data : AlignedNamedHistory D S old L M
  pointwise : data.AllPointwise D S old L

noncomputable def pointwiseAlignedInitial
    (M : Proper S) (x : Atom S old) :
    PointwiseAlignedHistory D S old L M where
  data := alignedNamedInitial D S old L M x
  pointwise := by
    intro P hP
    cases hP

noncomputable def pointwiseAlignedStep
    (M : Proper S) (H : PointwiseAlignedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.data.boundaryHistory.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
          H.data.boundaryHistory.chain.current y) :
    PointwiseAlignedHistory D S old L M where
  data := alignedNamedStep D S old L M H.data y hsep
  pointwise := alignedNamedStep_allPointwise
    D S old L M H.data y hsep H.pointwise

/-- Iterate the genuine finite historical pointwise-chart
invariant through every remaining original separated atom. -/
noncomputable def pointwiseAlignedBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : PointwiseAlignedHistory D S old L M)
    (hp : H.data.boundaryHistory.chain.previous = some p)
    (hc : H.data.boundaryHistory.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    PointwiseAlignedHistory D S old L M := by
  induction rest generalizing p c H with
  | nil => exact H
  | cons z zs ih =>
      have hstep :
          (match H.data.boundaryHistory.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.boundaryHistory.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := pointwiseAlignedStep D S old L M H z hstep
      have hnp : HN.data.boundaryHistory.chain.previous = some c := by
        change some H.data.boundaryHistory.chain.current = some c
        rw [hc]
      have hnc : HN.data.boundaryHistory.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- All actual original source-block interfaces of one finite
separated LinkChain retain their pointwise named Cayley maps. -/
noncomputable def pointwiseAlignedBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    PointwiseAlignedHistory D S old L M := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => exact pointwiseAlignedInitial D S old L M x
      | cons y ys =>
          let H0 := pointwiseAlignedInitial D S old L M x
          let H1 := pointwiseAlignedStep D S old L M H0 y trivial
          have hp : H1.data.boundaryHistory.chain.previous = some x := rfl
          have hc : H1.data.boundaryHistory.chain.current = y := rfl
          exact pointwiseAlignedBuildTail D S old L M x y H1
            hp hc ys hsep

/-- Pointwise certificates do not change the original named
historical boundary recursor, including its dependent quotient. -/
theorem pointwiseAlignedBuildTail_data_eq
    (M : Proper S) (p c : Atom S old)
    (H : PointwiseAlignedHistory D S old L M)
    (hp : H.data.boundaryHistory.chain.previous = some p)
    (hc : H.data.boundaryHistory.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (pointwiseAlignedBuildTail D S old L M p c H hp hc rest hsep).data =
      alignedNamedBuildTail D S old L M p c H.data hp hc rest hsep := by
  induction rest generalizing p c H with
  | nil => rfl
  | cons z zs ih =>
      have hstep :
          (match H.data.boundaryHistory.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.data.boundaryHistory.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := pointwiseAlignedStep D S old L M H z hstep
      have hnp : HN.data.boundaryHistory.chain.previous = some c := by
        change some H.data.boundaryHistory.chain.current = some c
        rw [hc]
      have hnc : HN.data.boundaryHistory.chain.current = z := rfl
      change
        (pointwiseAlignedBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).data =
        alignedNamedBuildTail D S old L M c z
          HN.data hnp hnc zs hsep.2
      exact ih c z HN hnp hnc hsep.2

/-- The full finite pointwise enrichment is exactly the original
aligned named history after forgetting its pointwise certificates. -/
theorem pointwiseAlignedBuildNonempty_data_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (pointwiseAlignedBuildNonempty D S old L M atoms hne hsep).data =
      alignedNamedBuildNonempty D S old L M atoms hne hsep := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          let H0 := pointwiseAlignedInitial D S old L M x
          let H1 := pointwiseAlignedStep D S old L M H0 y trivial
          have hp : H1.data.boundaryHistory.chain.previous = some x := rfl
          have hc : H1.data.boundaryHistory.chain.current = y := rfl
          change
            (pointwiseAlignedBuildTail D S old L M x y H1
              hp hc ys hsep).data =
            alignedNamedBuildTail D S old L M x y
              H1.data hp hc ys hsep
          exact pointwiseAlignedBuildTail_data_eq
            D S old L M x y H1 hp hc ys hsep

/-- Every original historical boundary of the literal
LinkChain.buildNonempty has pointwise correct left and right
source Cayley coordinates, in one and the same original quotient. -/
theorem buildNonempty_all_pointwise_named_boundaries
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    ∃ H : AlignedNamedHistory D S old L M,
      (⟨H.boundaryHistory.chain.current,
         H.boundaryHistory.chain.state⟩ : SomeState S old) =
        buildNonempty D S old L atoms hne hsep ∧
      H.AllPointwise D S old L := by
  let H := pointwiseAlignedBuildNonempty D S old L M atoms hne hsep
  refine ⟨H.data, ?_, H.pointwise⟩
  rw [pointwiseAlignedBuildNonempty_data_eq
    D S old L M atoms hne hsep]
  exact alignedNamedBuildNonempty_original D S old L M atoms hne hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
