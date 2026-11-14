import GluingEPPA.Steiner.ChainValuation.NamedHistoryOriginalCorrespondence
import GluingEPPA.Steiner.ChainValuation.SaturatedMatchingComponent
import GluingEPPA.Steiner.ChainValuation.MatchedLinkCosetSaturation

/-!
# The complete K_M alternative of the finite chain restriction lemma

Consider an actual finite separated LinkChain H, an M-component,
and a historical block K_A met by that component. If M ⊆ A,
the component is exactly the translated coset of the original
K_M inside K_A: its M-letters have all their neighbours inside
the coset, and the recorded historical chart proves that coset
is connected by M-paths.

The essential subtlety is saturation, not merely historical
reachability. NamedHistoryLetterEdgesFinite gives genuine e-edges
of every original K_A chart in the *final* quotient. Those edges
stay in the same literal restricted coset by the earlier Link
Cayley reachability theorem. Matching uniqueness then proves
that NO M-edge can leave this coset via any other attached block.

This formalizes the geometric first alternative in
lem:chain-restriction; the other (proper-mask interval) alternative
still needs a globally assembled normalized chain equivalence.
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

/-- The image of one genuine earlier M-restricted coset under a
particular original historical K_A chart. This is a subset of the
actual finite-chain quotient, never an auxiliary component type. -/
def NamedHistoricalBlock.restrictedCosetImage
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (base : (old T.source).Carrier) :
    Set R.state.Space :=
  T.chart.embed '' leftCoset
    (restrictedSubgroup D S old L M T.source) base

/-- If A contains M, every M-letter at every vertex of the
historical K_(M∩A) coset has its genuine neighbour in that SAME
coset. This is the additional saturation fact missing from the
historical reachability/coset record. -/
theorem NamedHistoricalBlock.restrictedCosetImage_saturated
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (hEdges : T.HasGenuineLetterEdges D S old L)
    (hfull : M.val ⊆ T.source.val)
    (base : (old T.source).Carrier) :
    MatchingSaturated R.state.matching M.val
      (T.restrictedCosetImage D S old L base) := by
  intro e he v hv
  obtain ⟨x, hx, rfl⟩ := hv
  have heA : e ∈ T.source.val := hfull he
  let y : (old T.source).Carrier := x * (old T.source).edge e
  have hxy : ((block S old T.source).matching e).Rel x y :=
    (block S old T.source).matching_rel heA x
  have hy : y ∈ leftCoset
      (restrictedSubgroup D S old L M T.source) base :=
    restrictedBlockCoset_edge_closed D S old L M T.source
      base x y e he hxy hx
  refine ⟨T.chart.embed y, ?_, ?_⟩
  · exact ⟨y, hy, rfl⟩
  · exact hEdges e heA x

/-- All vertices in one selected historical restricted coset are
genuinely M-connected in the final original quotient, using
the previously checked historical coset chart. -/
theorem NamedHistoricalBlock.restrictedCosetImage_connected
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (base : (old T.source).Carrier)
    (x : R.state.Space)
    (hx : x ∈ T.restrictedCosetImage D S old L base)
    (y : R.state.Space)
    (hy : y ∈ T.restrictedCosetImage D S old L base) :
    LabelReach (fun e => (R.state.matching e).Rel) M.val x y := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  let P := restrictedSubgroup D S old L M T.source
  have hA : leftCoset P base = leftCoset P a :=
    leftCoset_eq_of_mem ha
  have hB : b ∈ leftCoset P a := by
    rw [← hA]
    exact hb
  exact (T.chart.reach_iff a b).mpr hB

/-- FIRST ALTERNATIVE, in the actual final quotient:
if the source mask A of an occupied historical block contains M,
then the whole M-component of any vertex in its selected coset
is precisely that coset. It cannot extend to another block. -/
theorem NamedHistoricalBlock.fullMask_component_iff
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (hEdges : T.HasGenuineLetterEdges D S old L)
    (hfull : M.val ⊆ T.source.val)
    (base : (old T.source).Carrier)
    (v : R.state.Space) :
    LabelReach (fun e => (R.state.matching e).Rel) M.val
      (T.chart.embed base) v ↔
    v ∈ T.restrictedCosetImage D S old L base := by
  let W := T.restrictedCosetImage D S old L base
  have hsat : MatchingSaturated R.state.matching M.val W :=
    T.restrictedCosetImage_saturated D S old L hEdges hfull base
  have hconnected :
      ∀ x ∈ W, ∀ y ∈ W,
        LabelReach (fun e => (R.state.matching e).Rel) M.val x y :=
    fun x hx y hy =>
      T.restrictedCosetImage_connected D S old L base x hx y hy
  have hbase : T.chart.embed base ∈ W :=
    ⟨base, self_mem_leftCoset
      (restrictedSubgroup D S old L M T.source) base, rfl⟩
  exact MatchingSaturated.component_iff
    R.state.matching M.val W hsat hconnected
    (T.chart.embed base) hbase v

/-- The full-mask component alternative is available on EVERY
named historical block of EVERY genuine finite separated Link
chain. The source-edge witness is constructed by the exact
finite-list induction, not supplied as an external hypothesis. -/
theorem namedHistoryBuildNonempty_fullMask_component_iff
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms)
    (T : NamedHistoricalBlock D S old L M
      (namedHistoryBuildNonempty D S old L M atoms hne hsep).data.chain)
    (hT : T ∈ (namedHistoryBuildNonempty
      D S old L M atoms hne hsep).named)
    (hfull : M.val ⊆ T.source.val)
    (base : (old T.source).Carrier)
    (v : (namedHistoryBuildNonempty
      D S old L M atoms hne hsep).data.chain.state.Space) :
    LabelReach
      (fun e => ((namedHistoryBuildNonempty
        D S old L M atoms hne hsep).data.chain.state.matching e).Rel)
      M.val (T.chart.embed base) v ↔
    v ∈ T.restrictedCosetImage D S old L base := by
  exact T.fullMask_component_iff D S old L
    (namedHistoryBuildNonempty_allGenuineLetterEdges
      D S old L M atoms hne hsep T hT)
    hfull base v

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
