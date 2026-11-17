import GluingEPPA.Steiner.ChainValuation.NamedHistoryStepBridge

/-!
# Genuine letter edges for every original historical Cayley chart

The old named history recorded the complete M-component/coset
equivalence, but that condition alone does not say that the embedded
old Cayley block continues to exhibit its actual individual
letter edges. The normalization's full-M alternative needs exactly
this stronger property: each original generator of K_A acts by
its genuine edge on the embedded historical K_A chart.

This module proves the property at the initial/last Cayley block
and transports it through the literal ChainState.extend quotient.
It does not infer edges from reachability alone, which would be
invalid for a given label.

The finite-list induction is in NamedHistoryLetterEdgesFinite.lean.
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

/-- Every original active letter has its *actual* directed matching
edge in the final quotient, on each occurrence of the named Cayley
block, rather than only an abstract M-reachability path. -/
def NamedHistoricalBlock.HasGenuineLetterEdges
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R) : Prop :=
  ∀ (e : E), e ∈ T.source.val →
    ∀ (x : (old T.source).Carrier),
      (R.state.matching e).Rel (T.chart.embed x)
        (T.chart.embed (x * (old T.source).edge e))

/-- The last historical block in any literal chain has genuine
edges from the ChainState's already checked last_active field. -/
theorem namedHistoricalLast_hasGenuineLetterEdges
    (M : Proper S) (R : BuildResult D S old L)
    (hcoset : LastMaskCoset D S old L M R) :
    (namedHistoricalLast D S old L M R hcoset).HasGenuineLetterEdges
      D S old L := by
  -- Reduce the *dependent* source name before introducing x: otherwise
  -- x and the current-block generator elaborate at different carrier types.
  change ∀ (e : E), e ∈ R.current.1.val →
    ∀ x : (old R.current.1).Carrier,
      (R.state.matching e).Rel
        (R.state.lastEmbed x)
        (R.state.lastEmbed (x * (old R.current.1).edge e))
  intro e he x
  exact R.state.last_active e he x

/-- Subsequent literal LinkChain steps do not destroy an active
letter edge of any historical Cayley block. The original old-side
edge is a defining disjunct of the genuine extended matching. -/
theorem namedHistoricalTransport_hasGenuineLetterEdges
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (T : NamedHistoricalBlock D S old L M R)
    (hT : T.HasGenuineLetterEdges D S old L) :
    (namedHistoricalTransport D S old L M R y hsep hcoset T).HasGenuineLetterEdges
      D S old L := by
  -- The transported chart's source is definitionally T.source.
  -- Establish that equality in the goal before elaborating its
  -- source-generator multiplication.
  change ∀ (e : E), e ∈ T.source.val →
    ∀ x : (old T.source).Carrier,
      extendedEdgeRel
        (block S old R.current.1) (block S old y.1)
        R.state R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1) e
        (oldEmbed (block S old R.current.1) (block S old y.1)
          R.state R.current.2
          (left D S old L R.current.1 y.1)
          (right D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1)
          (right_injective D S old L R.current.1 y.1)
          (T.chart.embed x))
        (oldEmbed (block S old R.current.1) (block S old y.1)
          R.state R.current.2
          (left D S old L R.current.1 y.1)
          (right D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1)
          (right_injective D S old L R.current.1 y.1)
          (T.chart.embed (x * (old T.source).edge e)))
  intro e he x
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hi := left_injective D S old L R.current.1 y.1
  let hj := right_injective D S old L R.current.1 y.1
  change extendedEdgeRel A B R.state R.current.2 i j hi hj e
    (oldEmbed A B R.state R.current.2 i j hi hj (T.chart.embed x))
    (oldEmbed A B R.state R.current.2 i j hi hj
      (T.chart.embed (x * (old T.source).edge e)))
  exact Or.inl ⟨T.chart.embed x,
    T.chart.embed (x * (old T.source).edge e),
    hT e he x, rfl, rfl⟩

/-- Genuine letter-edge existence is preserved for the *whole*
ordered list of original historical charts in one actual step.
No old source block is silently replaced by an isomorphic group. -/
def NamedHistoryBuildResult.AllGenuineLetterEdges
    {M : Proper S} (H : NamedHistoryBuildResult D S old L M) : Prop :=
  ∀ T : NamedHistoricalBlock D S old L M H.data.chain,
    T ∈ H.named → T.HasGenuineLetterEdges D S old L

theorem namedHistoryInitial_allGenuineLetterEdges
    (M : Proper S) (x : Atom S old) :
    (namedHistoryInitial D S old L M x).AllGenuineLetterEdges
      D S old L := by
  intro T hT
  have hEq :
      T = namedHistoricalLast D S old L M
        (initial D S old L x) (initial_lastMaskCoset D S old L M x) := by
    exact List.mem_singleton.mp hT
  subst T
  exact namedHistoricalLast_hasGenuineLetterEdges
    D S old L M (initial D S old L x)
    (initial_lastMaskCoset D S old L M x)

/-- Actual historical letter edges and provenance persist
through one synchronously named chain extension. -/
theorem namedHistoryStep_allGenuineLetterEdges
    (M : Proper S) (H : NamedHistoryBuildResult D S old L M)
    (y : Atom S old)
    (hsep :
      match H.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.data.chain.current y)
    (hOld : H.AllGenuineLetterEdges D S old L) :
    (namedHistoryStep D S old L M H y hsep).AllGenuineLetterEdges
      D S old L := by
  intro T hT
  have hmem : T ∈
      (namedHistoricalStepList D S old L M
        H.data.chain y hsep H.data.lastInv H.named) := hT
  rcases List.mem_append.mp hmem with hPrev | hNew
  · obtain ⟨U, hU, hEq⟩ := List.mem_map.mp hPrev
    subst T
    exact namedHistoricalTransport_hasGenuineLetterEdges
      D S old L M H.data.chain y hsep H.data.lastInv U
      (hOld U hU)
  · have hEq : T = namedHistoricalLast D S old L M
        (step D S old L H.data.chain y hsep)
        (step_lastMaskCoset D S old L M
          H.data.chain y hsep H.data.lastInv) :=
      List.mem_singleton.mp hNew
    subst T
    exact namedHistoricalLast_hasGenuineLetterEdges
      D S old L M (step D S old L H.data.chain y hsep)
      (step_lastMaskCoset D S old L M
        H.data.chain y hsep H.data.lastInv)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
