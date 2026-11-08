import GluingEPPA.Steiner.ChainValuation.LinkHistoryStep

/-!
# Historical Cayley charts indexed by their actual earlier masks

The generic HistoricalBlock record remembers a heterogeneous group,
subgroup and chart, but not the original earlier alphabet A of that
group. To state a finite-chain normalization along adjacent historical
Link attachments, one needs to know *which* K_A each historical chart
came from, and hence which actual K_(A∩B) glued it to its neighbour.

A NamedHistoricalBlock retains its original A : Proper S and has
carrier definitionally K_A, with the exact restricted subgroup
K_(M∩A). Its forgetful map is a genuine generic HistoricalBlock.

An actual LinkChain.step transports all old named charts and adds
one named chart for the new K_B block. The underlying ordered mask
list is therefore unchanged except for appending B. No top-stage
group or isomorphism of unrelated carriers is assumed.

This supplies the provenance data for the still-pending adjacent
interface witness and all-length normalized component chart.
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

/-- A historical component chart retaining the exact mask of its
source group K_A, rather than an existential arbitrary group. -/
structure NamedHistoricalBlock
    (M : Proper S) (R : BuildResult D S old L) where
  source : Proper S
  chart : HistoricalCosetChart
    (block S old R.current.1) R.state M.val
    (restrictedSubgroup D S old L M source)

/-- Forget the mask label while retaining the literal carrier,
restricted subgroup, and actual embedding into the chain quotient. -/
def NamedHistoricalBlock.toHistorical
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R) :
    HistoricalBlock (block S old R.current.1) R.state M.val where
  Carrier := (old T.source).Carrier
  group := inferInstance
  subgroup := restrictedSubgroup D S old L M T.source
  chart := T.chart

/-- The true last Cayley block is a named historical block. -/
def namedHistoricalLast
    (M : Proper S) (R : BuildResult D S old L)
    (hcoset : LastMaskCoset D S old L M R) :
    NamedHistoricalBlock D S old L M R where
  source := R.current.1
  chart := historicalLastChart
    (block S old R.current.1) R.state M.val
    (restrictedSubgroup D S old L M R.current.1) hcoset

/-- Transport a named historical block through an actual separated
LinkChain.step, keeping the original source mask unchanged. -/
noncomputable def namedHistoricalTransport
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (T : NamedHistoricalBlock D S old L M R) :
    NamedHistoricalBlock D S old L M (step D S old L R y hsep) := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi := left_injective D S old L R.current.1 y.1
  have hj := right_injective D S old L R.current.1 y.1
  have hd := step_attachment_disjoint D S old L R y hsep
  have hs : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : (old (common S R.current.1 y.1)).Carrier,
        i k = A.edge e ∧ j k = B.edge e := by
    intro e heA heB
    exact shared_edge D S old L R.current.1 y.1 e heA heB
  have hpull := step_attachment_compatible D S old L M R y hcoset
  exact
    { source := T.source
      chart := T.chart.extend
        A B R.state R.current.2 i j hi hj hd hs
        M.val hpull
        (restrictedSubgroup D S old L M T.source) }

/-- The complete named historical list at a genuine chain extension:
old source labels remain in order and the new source mask is y.1. -/
noncomputable def namedHistoricalStepList
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (history : List (NamedHistoricalBlock D S old L M R)) :
    List (NamedHistoricalBlock D S old L M
      (step D S old L R y hsep)) :=
  history.map (fun T =>
    namedHistoricalTransport D S old L M R y hsep hcoset T) ++
  [namedHistoricalLast D S old L M
    (step D S old L R y hsep)
    (step_lastMaskCoset D S old L M R y hsep hcoset)]

/-- The one-block history starts with the literal source mask x.1. -/
theorem namedHistoricalInitial_source
    (M : Proper S) (x : Atom S old) :
    (namedHistoricalLast D S old L M (initial D S old L x)
      (initial_lastMaskCoset D S old L M x)).source = x.1 := rfl

/-- Source provenance is stable under transport. -/
theorem namedHistoricalTransport_source
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (T : NamedHistoricalBlock D S old L M R) :
    (namedHistoricalTransport D S old L M R y hsep hcoset T).source =
      T.source := rfl

/-- The sequence of original source masks in an extended history is
exactly the old sequence followed by the new literal block mask. -/
theorem namedHistoricalStep_sourceList
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (history : List (NamedHistoricalBlock D S old L M R)) :
    (namedHistoricalStepList D S old L M R y hsep hcoset
      history).map NamedHistoricalBlock.source =
    history.map NamedHistoricalBlock.source ++ [y.1] := by
  simp [namedHistoricalStepList, namedHistoricalTransport,
    namedHistoricalLast]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
