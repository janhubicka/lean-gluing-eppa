import GluingEPPA.Steiner.RecursiveNaturality
import GluingEPPA.Steiner.ChainValuation.ChainIndexRelabel

/-!
# Equivalence on the actual proper-alphabet index types

An equivalence of edge names carrying S onto T induces an equivalence on
all actual proper subsets. The inverse is exactly the old pullback map.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

universe u
variable {E E' : Type u} [Fintype E] [DecidableEq E]
  [Fintype E'] [DecidableEq E']

/-- The true equivalence of all proper earlier stages under named-edge
relabeling, with no choices of subset representatives. -/
noncomputable def properRelabel (p : E ≃ E') (S : Finset E) (T : Finset E')
    (hST : ∀ e, p e ∈ T ↔ e ∈ S) : Proper S ≃ Proper T := by
  let hTS : ∀ e' : E', p.symm e' ∈ S ↔ e' ∈ T := by
    intro e'
    simpa using (hST (p.symm e')).symm
  refine
    { toFun := properPullback p.symm T S hTS
      invFun := properPullback p S T hST
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    apply Subtype.ext
    ext e
    have h1 := properPullback_membership p S T hST
      (properPullback p.symm T S hTS i) e
    have h2 := properPullback_membership p.symm T S hTS i (p e)
    simpa using (h1.symm.trans h2.symm)
  · intro j
    apply Subtype.ext
    ext e
    have h1 := properPullback_membership p.symm T S hTS
      (properPullback p S T hST j) e
    have h2 := properPullback_membership p S T hST j (p.symm e)
    simpa using (h1.symm.trans h2.symm)

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
