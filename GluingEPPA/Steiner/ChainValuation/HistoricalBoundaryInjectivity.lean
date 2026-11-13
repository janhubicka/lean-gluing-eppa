import GluingEPPA.Steiner.ChainValuation.FiniteBoundarySourcePairs

/-!
# Every actual historical boundary retains injective Cayley charts

The persistent historical Link boundary record contains its genuine
two-sided internal M-path criterion and its original source masks,
but its type alone does *not* declare that its two charts are injective.
Injectivity is indispensable when using these charts to build
edge-reflecting equivalences with normalized smaller-mask chains.

We establish it for the actual new boundary, prove that it persists
under every later old-chain embedding, and transfer it through the
literal historical boundary-list construction. No extra injectivity
axiom or isomorphic surrogate chain is introduced.
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

/-- Both genuine historical Cayley group charts are embeddings of
their carriers into the current chain quotient. -/
def HistoricalLinkBoundary.Embeds
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R) : Prop :=
  Function.Injective T.leftChart ∧
  Function.Injective T.rightChart

/-- The freshly created boundary embeds both its original Cayley
blocks into the literal LinkChain.step quotient. -/
theorem historicalLinkBoundary_step_embeds
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (historicalLinkBoundary_step D S old L M R y hsep hcoset).Embeds
      D S old L := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi := left_injective D S old L R.current.1 y.1
  have hj := right_injective D S old L R.current.1 y.1
  constructor
  · intro x x' hxx'
    have hh : oldEmbed A B R.state R.current.2 i j hi hj
        (R.state.lastEmbed x) =
        oldEmbed A B R.state R.current.2 i j hi hj
        (R.state.lastEmbed x') := by
      exact hxx'
    exact R.state.lastInjective
      ((oldEmbed_injective A B R.state R.current.2 i j hi hj) hh)
  · intro y0 y1 hyy
    have hh : newEmbed A B R.state R.current.2 i j hi hj y0 =
        newEmbed A B R.state R.current.2 i j hi hj y1 := by
      exact hyy
    exact (newEmbed_injective A B R.state R.current.2 i j hi hj) hh

/-- Old historical boundary embeddings stay injective after one
further genuine separated LinkChain attachment. -/
theorem HistoricalLinkBoundary.transport_embeds
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (hEmb : T.Embeds D S old L) :
    (T.transport D S old L y hsep hcoset).Embeds D S old L := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi := left_injective D S old L R.current.1 y.1
  have hj := right_injective D S old L R.current.1 y.1
  constructor
  · intro x x' hxx'
    have hh : T.leftChart x = T.leftChart x' :=
      (oldEmbed_injective A B R.state R.current.2 i j hi hj) hxx'
    exact hEmb.1 hh
  · intro x x' hxx'
    have hh : T.rightChart x = T.rightChart x' :=
      (oldEmbed_injective A B R.state R.current.2 i j hi hj) hxx'
    exact hEmb.2 hh

/-- All boundary charts in a historical list are injective. -/
def HistoricalBoundariesEmbedded
    (M : Proper S) (R : BuildResult D S old L)
    (boundaries : List (HistoricalLinkBoundary D S old L M R)) : Prop :=
  ∀ T, T ∈ boundaries → T.Embeds D S old L

/-- The actual boundary-list step carries injectivity of every old
historical chart forward and supplies a new injective last pair. -/
theorem historicalBoundaries_step_embedded
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (boundaries : List (HistoricalLinkBoundary D S old L M R))
    (hOld : HistoricalBoundariesEmbedded D S old L M R boundaries) :
    HistoricalBoundariesEmbedded D S old L M
      (step D S old L R y hsep)
      (historicalBoundaries_step D S old L M R y hsep hcoset
        boundaries) := by
  intro T hT
  have hmem :
      T ∈ boundaries.map (fun B =>
        B.transport D S old L y hsep hcoset) ++
        [historicalLinkBoundary_step D S old L M R y hsep hcoset] := hT
  rcases List.mem_append.mp hmem with hTold | hTnew
  · obtain ⟨U, hU, hEq⟩ := List.mem_map.mp hTold
    subst T
    exact U.transport_embeds D S old L y hsep hcoset
      (hOld U hU)
  · have hEq :
        T = historicalLinkBoundary_step D S old L M R y hsep hcoset :=
      List.mem_singleton.mp hTnew
    subst T
    exact historicalLinkBoundary_step_embeds D S old L M R y hsep hcoset

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
