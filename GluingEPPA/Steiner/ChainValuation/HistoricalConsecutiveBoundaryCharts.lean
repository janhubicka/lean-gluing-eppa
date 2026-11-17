import GluingEPPA.Steiner.ChainValuation.HistoricalInterfaceEquivalence
import GluingEPPA.Steiner.ChainValuation.CoupledHistoryOriginalCorrespondence

/-!
# Actual consecutive historical Link boundaries share the same Cayley chart

The finite boundary-list source-mask theorem identifies adjacent
source masks but not, by itself, the actual vertex maps on their
common middle source block. Here we check the missing local identity.

When two original LinkChain steps attach consecutive blocks, the
right-hand historical chart of the first interface, after being
transported through the second attachment, is IDENTICALLY the
left-hand chart of the second interface. The equality holds
pointwise in the literal original quotient, not merely as equality
of sets of source masks or abstract groups.

Further genuine chain steps preserve this adjacent-range identity,
since they compose both historical charts with the same old
pushout embedding. These are the compatibility inputs for assembling
all interior normalized shifts over an arbitrary active interval.
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

/-- Two historical boundaries are aligned when their overlapping
source mask is the same and the corresponding two historical source
charts have the same ACTUAL image in the current chain quotient. -/
def HistoricalLinkBoundary.AdjacentRanges
    {M : Proper S} {R : BuildResult D S old L}
    (T U : HistoricalLinkBoundary D S old L M R) : Prop :=
  T.rightMask = U.leftMask ∧
    Set.range T.rightChart = Set.range U.leftChart

/-- Two adjacent original Link attachments have literally identical
middle-block chart maps after both are viewed in the second, actual
pushout state. In particular their overlap is not merely a chosen
isomorphism or an arbitrary matching of coordinate sets. -/
theorem consecutiveHistoricalBoundary_pointwise
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (z : Atom S old)
    (hsep2 :
      match (step D S old L R y hsep).previous with
      | none => True
      | some p => tripleSeparated D S old L p
          (step D S old L R y hsep).current z) :
    let R1 := step D S old L R y hsep
    let hcoset1 := step_lastMaskCoset D S old L M R y hsep hprev
    let T := (historicalLinkBoundary_step
      D S old L M R y hsep hprev).transport
      D S old L z hsep2 hcoset1
    let U := historicalLinkBoundary_step
      D S old L M R1 z hsep2 hcoset1
    T.rightMask = U.leftMask ∧
      ∀ x : (old y.1).Carrier,
        T.rightChart x = U.leftChart x := by
  constructor
  · rfl
  · intro x
    rfl

/-- In particular the two fresh consecutive boundaries have the
same middle source chart range in the full original quotient. -/
theorem consecutiveHistoricalBoundary_adjacentRanges
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (z : Atom S old)
    (hsep2 :
      match (step D S old L R y hsep).previous with
      | none => True
      | some p => tripleSeparated D S old L p
          (step D S old L R y hsep).current z) :
    let R1 := step D S old L R y hsep
    let hcoset1 := step_lastMaskCoset D S old L M R y hsep hprev
    let T := (historicalLinkBoundary_step
      D S old L M R y hsep hprev).transport
      D S old L z hsep2 hcoset1
    let U := historicalLinkBoundary_step
      D S old L M R1 z hsep2 hcoset1
    T.AdjacentRanges D S old L U := by
  let R1 := step D S old L R y hsep
  let hcoset1 := step_lastMaskCoset D S old L M R y hsep hprev
  let T := (historicalLinkBoundary_step
    D S old L M R y hsep hprev).transport
    D S old L z hsep2 hcoset1
  let U := historicalLinkBoundary_step
    D S old L M R1 z hsep2 hcoset1
  have heq : T.rightMask = U.leftMask ∧
      ∀ x : (old y.1).Carrier,
        T.rightChart x = U.leftChart x :=
    consecutiveHistoricalBoundary_pointwise
      D S old L M R y hsep hprev z hsep2
  constructor
  · exact heq.1
  · have hfun : T.rightChart = U.leftChart := by
      funext x
      exact heq.2 x
    exact congrArg Set.range hfun

/-- Once two genuinely historical boundaries agree on their middle
source chart range, every later literal LinkChain attachment
preserves this agreement, with both sides composed by the same
old-chain pushout embedding. -/
theorem HistoricalLinkBoundary.transport_adjacentRanges
    {M : Proper S} {R : BuildResult D S old L}
    (T U : HistoricalLinkBoundary D S old L M R)
    (h : T.AdjacentRanges D S old L U)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (T.transport D S old L y hsep hcoset).AdjacentRanges
      D S old L (U.transport D S old L y hsep hcoset) := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hi := left_injective D S old L R.current.1 y.1
  let hj := right_injective D S old L R.current.1 y.1
  let emb := GluingEPPA.Steiner.ChainValuation.oldEmbed
    A B R.state R.current.2 i j hi hj
  constructor
  · exact h.1
  · change Set.range (fun x => emb (T.rightChart x)) =
      Set.range (fun x => emb (U.leftChart x))
    ext p
    constructor
    · rintro ⟨x, hx⟩
      have hm : T.rightChart x ∈ Set.range U.leftChart := by
        rw [← h.2]
        exact ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := hm
      exact ⟨w, by simpa [hw] using hx⟩
    · rintro ⟨x, hx⟩
      have hm : U.leftChart x ∈ Set.range T.rightChart := by
        rw [h.2]
        exact ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := hm
      exact ⟨w, by simpa [hw] using hx⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
