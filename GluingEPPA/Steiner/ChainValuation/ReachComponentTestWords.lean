import GluingEPPA.Steiner.ChainValuation.ReachComponentWords
import GluingEPPA.Steiner.ChainValuation.EquivariantTestCovers

/-!
# Actual recursive test-word action of a normalized component

The recursive valuation's word action is testWordPerm, defined in
WordAction. The M-component chart results must intertwine exactly
this pre-existing definition, rather than only a parallel list
recursor. This is the bridge needed when applying the earlier
joint-equivariant-cover lemma to the finite ChainTests package.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {E : Type u} {X : Type v} {U : Type w}

/-- An edge-reflecting chart on a genuine M-component transports
the exact recursive valuation testWordPerm action. We reuse the
previously verified generic generator-to-word equivariance theorem,
rather than reproving a separate word induction. -/
theorem componentChart_testWordPerm_val
    (P : E → Matching X) (M : Finset E) (q : X)
    (Q : E → Matching U)
    (F : U ≃ MatchingReachComponent P M q)
    (hRel : ∀ e ∈ M, ∀ x y : U,
      (Q e).Rel x y ↔ (P e).Rel (F x).val (F y).val)
    (word : List E) (hw : ∀ e ∈ word, e ∈ M) (x : U) :
    (F (GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (Q e).perm) word x)).val =
      GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (P e).perm) word (F x).val := by
  exact
    GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm_map_of_generator_intertwining
      (fun e => (Q e).perm) (fun e => (P e).perm)
      M (fun z : U => (F z).val)
      (fun e he z =>
        componentChart_perm_val_of_edge_iff P M q Q F hRel e he z)
      word hw x

end GluingEPPA.Steiner.ChainValuation
