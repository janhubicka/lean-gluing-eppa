import GluingEPPA.Steiner.ChainValuation.ProperSubsetRelabel

/-!
# Relabelling preserves proper predecessor intersections

The canonical proper-subset equivalence commutes with the actual
meet operation. This dependent index equality is needed to identify
the earlier group on an attachment interface on both sides of a
relabelled separated chain.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

universe u
variable {E E' : Type u} [Fintype E] [DecidableEq E]
  [Fintype E'] [DecidableEq E']

/-- Pullback along a bijection preserves finite-set intersections. -/
theorem pullbackSubset_inter (p : E ≃ E') (A B : Finset E') :
    pullbackSubset p (A ∩ B) =
      pullbackSubset p A ∩ pullbackSubset p B := by
  ext e
  constructor
  · intro h
    have hab : p e ∈ A ∩ B := (pullback_mem p (A ∩ B) e).1 h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hab
    exact Finset.mem_inter.mpr
      ⟨(pullback_mem p A e).2 ha, (pullback_mem p B e).2 hb⟩
  · intro h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp h
    exact (pullback_mem p (A ∩ B) e).2
      (Finset.mem_inter.mpr
        ⟨(pullback_mem p A e).1 ha, (pullback_mem p B e).1 hb⟩)

/-- Relabelling the actual proper predecessors respects their meet,
not merely the isomorphism type of the intersection group. -/
theorem properRelabel_meet (p : E ≃ E') (S : Finset E) (T : Finset E')
    (hST : ∀ e, p e ∈ T ↔ e ∈ S)
    (i j : Proper S) :
    properRelabel p S T hST (Step.meet S i j) =
      Step.meet T (properRelabel p S T hST i)
        (properRelabel p S T hST j) := by
  apply Subtype.ext
  change pullbackSubset p.symm (i.val ∩ j.val) =
    pullbackSubset p.symm i.val ∩ pullbackSubset p.symm j.val
  exact pullbackSubset_inter p.symm i.val j.val

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
