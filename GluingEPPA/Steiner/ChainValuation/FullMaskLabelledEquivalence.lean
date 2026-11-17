import GluingEPPA.Steiner.ChainValuation.FiniteHistoricalComponentDichotomy
import GluingEPPA.Steiner.ChainValuation.ReachComponentWords
import GluingEPPA.Steiner.ChainValuation.LinkCosetEquiv

/-!
# Full historical K_M component as a labelled Cayley chart

The full-M alternative needs an equivalence of labelled transition
systems, not just equality of component point sets. Genuine source
edges persist in the finite original chain, and matching uniqueness
ensures that the original historical chart also REFLECTS those edges.

The actual entire M-component is therefore equivalent to the
literal earlier group K_(M intersect A), with its genuine M-letter
edges and completed actions. Under M subset A, the mask M intersect A
equals M. This does not prove the remaining proper-mask case.
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

theorem normalizedFullMask_eq
    (M A : Proper S) (hMA : M.val ⊆ A.val) :
    Step.meet S M A = M := by
  apply Subtype.ext
  exact Finset.inter_eq_left.mpr hMA

/-- Restriction of the final matching to an embedded historical source
block reflects its genuine generator edges, by uniqueness of neighbours. -/
theorem NamedHistoricalBlock.genuine_source_edge_iff
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (hEdges : T.HasGenuineLetterEdges D S old L)
    (e : E) (he : e ∈ T.source.val)
    (x y : (old T.source).Carrier) :
    ((block S old T.source).matching e).Rel x y ↔
      (R.state.matching e).Rel (T.chart.embed x) (T.chart.embed y) := by
  constructor
  · intro h
    rcases h with ⟨_, hy⟩
    subst y
    exact hEdges e he x
  · intro h
    have hnext : (R.state.matching e).Rel (T.chart.embed x)
        (T.chart.embed (x * (old T.source).edge e)) :=
      hEdges e he x
    have heq : T.chart.embed y =
        T.chart.embed (x * (old T.source).edge e) :=
      (R.state.matching e).unique h hnext
    have hy : y = x * (old T.source).edge e :=
      T.chart.injective heq
    exact ⟨he, hy⟩

/-- A full historical M-component is the literal earlier Cayley
group K_(M intersect A), translated by the coset base and embedded
in the final actual LinkChain quotient. -/
noncomputable def NamedHistoricalBlock.fullMask_component_equiv
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (hEdges : T.HasGenuineLetterEdges D S old L)
    (hfull : M.val ⊆ T.source.val)
    (base : (old T.source).Carrier) :
    (old (Step.meet S M T.source)).Carrier ≃
      MatchingReachComponent R.state.matching M.val
        (T.chart.embed base) := by
  let F := restrictedBlock_cosetEquiv
    D S old L M T.source base
  let G :
      {x : (old T.source).Carrier //
        x ∈ leftCoset (restrictedSubgroup D S old L M T.source) base} →
      MatchingReachComponent R.state.matching M.val
        (T.chart.embed base) :=
    fun x => ⟨T.chart.embed x.val,
      (T.fullMask_component_iff D S old L
        hEdges hfull base (T.chart.embed x.val)).mpr
        ⟨x.val, x.property, rfl⟩⟩
  have hinj : Function.Injective G := by
    intro x y hxy
    apply Subtype.ext
    apply T.chart.injective
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective G := by
    intro v
    have hv : v.val ∈ T.restrictedCosetImage D S old L base :=
      (T.fullMask_component_iff D S old L
        hEdges hfull base v.val).mp v.property
    obtain ⟨x, hx, hval⟩ := hv
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hval
  exact F.trans (Equiv.ofBijective G ⟨hinj, hsurj⟩)

/-- The chart's value is exactly historical embedding after a left
coset translation of the genuine earlier Link inclusion. -/
theorem NamedHistoricalBlock.fullMask_component_equiv_val
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (hEdges : T.HasGenuineLetterEdges D S old L)
    (hfull : M.val ⊆ T.source.val)
    (base : (old T.source).Carrier)
    (x : (old (Step.meet S M T.source)).Carrier) :
    ((T.fullMask_component_equiv D S old L
      hEdges hfull base) x).val =
      T.chart.embed
        ((restrictedBlock_cosetEquiv
          D S old L M T.source base x).val) := by
  rfl

/-- A genuine e-edge for e in M is reflected as well as preserved
by the full-M component chart in the FINAL original quotient. -/
theorem NamedHistoricalBlock.fullMask_component_equiv_edge_iff
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (hEdges : T.HasGenuineLetterEdges D S old L)
    (hfull : M.val ⊆ T.source.val)
    (base : (old T.source).Carrier)
    (e : E) (he : e ∈ M.val)
    (x y : (old (Step.meet S M T.source)).Carrier) :
    ((block S old (Step.meet S M T.source)).matching e).Rel x y ↔
      (R.state.matching e).Rel
        ((T.fullMask_component_equiv D S old L
          hEdges hfull base) x).val
        ((T.fullMask_component_equiv D S old L
          hEdges hfull base) y).val := by
  rw [T.fullMask_component_equiv_val D S old L hEdges hfull base x,
    T.fullMask_component_equiv_val D S old L hEdges hfull base y]
  exact
    (restrictedBlock_cosetEquiv_edge_iff
      D S old L M T.source base e he x y).trans
    (T.genuine_source_edge_iff D S old L
      hEdges e (hfull he)
      ((restrictedBlock_cosetEquiv
        D S old L M T.source base x).val)
      ((restrictedBlock_cosetEquiv
        D S old L M T.source base y).val))

/-- All finite M-word actions agree under the full-M historical
component chart, including completed matching fixed points. -/
theorem NamedHistoricalBlock.fullMask_component_word_val
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (hEdges : T.HasGenuineLetterEdges D S old L)
    (hfull : M.val ⊆ T.source.val)
    (base : (old T.source).Carrier)
    (word : List E)
    (hw : ∀ e ∈ word, e ∈ M.val)
    (x : (old (Step.meet S M T.source)).Carrier) :
    ((T.fullMask_component_equiv D S old L hEdges hfull base)
      (matchingWordApply
        (fun e => (block S old (Step.meet S M T.source)).matching e)
        word x)).val =
    matchingWordApply R.state.matching word
      ((T.fullMask_component_equiv D S old L
        hEdges hfull base) x).val := by
  let F := T.fullMask_component_equiv D S old L hEdges hfull base
  exact componentChart_word_perm_val
    R.state.matching M.val (T.chart.embed base)
    (fun e => (block S old (Step.meet S M T.source)).matching e)
    F
    (fun letter hletter a b =>
      T.fullMask_component_equiv_edge_iff
        D S old L hEdges hfull base letter hletter a b)
    word hw x

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
