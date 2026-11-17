import GluingEPPA.Steiner.ChainValuation.CoveredNamedAlignedHistory
import GluingEPPA.Steiner.ChainValuation.ActualNormalizedBoundary

/-!
# Multiplication along the actual historical interfaces

The historical boundary record keeps its original parameter maps through
later attachments.  This file proves their multiplication laws on the
restricted common group, first at a new attachment and then throughout
the original finite chain.  These laws identify the whole normalized
interface, rather than just its chosen base point.
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

/-- The two original parameter maps respect multiplication by every
element of the full restricted common-interface group. -/
def HistoricalLinkBoundary.ParameterMultiplicative
    {M : Proper S} {R : BuildResult D S old L}
    (B : HistoricalLinkBoundary D S old L M R) : Prop :=
  (∀ (k : (old (common S B.leftMask B.rightMask)).Carrier)
      (t : (old (Step.meet S M (common S B.leftMask B.rightMask))).Carrier),
    B.leftParam (k * normalizedCommonInterface D S old L M B.leftMask B.rightMask t) =
      B.leftParam k *
        (L (Step.meet S M B.leftMask) B.leftMask Finset.inter_subset_right).incl
          (normalizedCommonLeft D S old L M B.leftMask B.rightMask t)) ∧
  (∀ (k : (old (common S B.leftMask B.rightMask)).Carrier)
      (t : (old (Step.meet S M (common S B.leftMask B.rightMask))).Carrier),
    B.rightParam (k * normalizedCommonInterface D S old L M B.leftMask B.rightMask t) =
      B.rightParam k *
        (L (Step.meet S M B.rightMask) B.rightMask Finset.inter_subset_right).incl
          (normalizedCommonRight D S old L M B.leftMask B.rightMask t))

theorem historicalLinkBoundary_step_parameterMultiplicative
    (M : Proper S) (R : BuildResult D S old L) (y : Atom S old)
    (hsep : match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (historicalLinkBoundary_step D S old L M R y hsep hcoset).ParameterMultiplicative
      D S old L := by
  dsimp only [HistoricalLinkBoundary.ParameterMultiplicative,
    historicalLinkBoundary_step]
  constructor
  · intro k t
    change R.current.2 * left D S old L R.current.1 y.1
        (k * normalizedCommonInterface D S old L M R.current.1 y.1 t) =
      (R.current.2 * left D S old L R.current.1 y.1 k) *
        (L (Step.meet S M R.current.1) R.current.1 Finset.inter_subset_right).incl
          (normalizedCommonLeft D S old L M R.current.1 y.1 t)
    have hcomm := DFunLike.congr_fun
      (normalizedCommon_left_square D S old L M R.current.1 y.1) t
    simpa only [MonoidHom.comp_apply, map_mul, mul_assoc] using
      congrArg (fun z => R.current.2 * (left D S old L R.current.1 y.1 k) * z)
        hcomm.symm
  · intro k t
    change right D S old L R.current.1 y.1
        (k * normalizedCommonInterface D S old L M R.current.1 y.1 t) =
      right D S old L R.current.1 y.1 k *
        (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl
          (normalizedCommonRight D S old L M R.current.1 y.1 t)
    have hcomm := DFunLike.congr_fun
      (normalizedCommon_right_square D S old L M R.current.1 y.1) t
    simpa only [MonoidHom.comp_apply, map_mul] using
      congrArg (fun z => right D S old L R.current.1 y.1 k * z) hcomm.symm

theorem HistoricalLinkBoundary.transport_parameterMultiplicative
    {M : Proper S} {R : BuildResult D S old L}
    (B : HistoricalLinkBoundary D S old L M R)
    (hB : B.ParameterMultiplicative D S old L)
    (y : Atom S old)
    (hsep : match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (B.transport D S old L y hsep hcoset).ParameterMultiplicative D S old L :=
  hB

def CoveredNamedAlignedHistory.AllParameterMultiplicative
    {M : Proper S} (H : CoveredNamedAlignedHistory D S old L M) : Prop :=
  ∀ P ∈ H.aligned, P.boundary.ParameterMultiplicative D S old L

theorem coveredNamedAlignedStep_allParameterMultiplicative
    (M : Proper S) (H : CoveredNamedAlignedHistory D S old L M)
    (y : Atom S old)
    (hsep : match H.named.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.named.data.chain.current y)
    (hOld : H.AllParameterMultiplicative D S old L) :
    (coveredNamedAlignedStep D S old L M H y hsep).AllParameterMultiplicative
      D S old L := by
  intro P hP
  change P ∈ H.aligned.map (fun U =>
      U.transport D S old L y hsep H.named.data.lastInv) ++
      [alignedNamedBoundaryFresh D S old L M H.named.data.chain
        y hsep H.named.data.lastInv] at hP
  rcases List.mem_append.mp hP with hPrev | hNew
  · obtain ⟨U, hU, hEq⟩ := List.mem_map.mp hPrev
    subst P
    exact U.boundary.transport_parameterMultiplicative
      D S old L (hOld U hU) y hsep H.named.data.lastInv
  · have hEq := List.mem_singleton.mp hNew
    subst P
    exact historicalLinkBoundary_step_parameterMultiplicative
      D S old L M H.named.data.chain y hsep H.named.data.lastInv

theorem coveredNamedAlignedBuildTail_allParameterMultiplicative
    (M : Proper S) (p c : Atom S old)
    (H : CoveredNamedAlignedHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest))
    (hOld : H.AllParameterMultiplicative D S old L) :
    (coveredNamedAlignedBuildTail D S old L M p c H hp hc rest hsep).AllParameterMultiplicative
      D S old L := by
  induction rest generalizing p c H with
  | nil => exact hOld
  | cons z zs ih =>
      have hstep : (match H.named.data.chain.previous with
        | none => True
        | some previous => tripleSeparated D S old L previous
            H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coveredNamedAlignedStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2
        (coveredNamedAlignedStep_allParameterMultiplicative
          D S old L M H z hstep hOld)

/-- Every boundary of the actual finite separated chain retains the
whole restricted-interface multiplication laws. -/
theorem coveredNamedAlignedBuildNonempty_allParameterMultiplicative
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ []) (hsep : separatedList D S old L atoms) :
    (coveredNamedAlignedBuildNonempty D S old L M atoms hne hsep).AllParameterMultiplicative
      D S old L := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          intro P hP
          cases hP
      | cons y ys =>
          let H0 := coveredNamedAlignedInitial D S old L M x
          let H1 := coveredNamedAlignedStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          exact coveredNamedAlignedBuildTail_allParameterMultiplicative
            D S old L M x y H1 hp hc ys hsep
            (coveredNamedAlignedStep_allParameterMultiplicative D S old L M H0 y
              trivial (by intro P hP; cases hP))

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
