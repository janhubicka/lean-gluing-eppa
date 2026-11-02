import GluingEPPA.Steiner.ChainValuation.Cosets
import GluingEPPA.Steiner.CayleyLift

/-!
# Actual-walk assembly in the simplified reflection lemma

This validates the last step of the appendix's reflection proof using the
existing literal `EdgeGraph.WalkValue` and `componentSet`. The endpoint-repair
hypothesis is explicit. The component-record argument producing `v,q,r`, and
the construction of the augmented valuation itself, are separate obligations.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

universe u v w
variable {V : Type u} {E : Type v} {G : Type w} [Group G]
variable (D : EdgeGraph V E) (edgeValue : E → G)

/-- Walk values lie in a subgroup containing the values of their allowed edges. -/
theorem chain_walkValue_mem {M : Set E} (H : Subgroup G)
    (hgen : ∀ e ∈ M, edgeValue e ∈ H)
    {s t : V} {g : G} (p : D.WalkValue M edgeValue s t g) : g ∈ H := by
  induction p with
  | nil => exact H.one_mem
  | cons he hj p ih => exact H.mul_mem (hgen _ he) ih

/-- The common lifted vertex obtained after extracting a component representative.

No membership word is silently treated as an actual walk: `p` and `r` are
actual walks, and endpoint repair is used on their actual concatenation.
-/
theorem chain_reflection_witness
    (hinv : ∀ e, edgeValue e * edgeValue e = 1)
    {A B : Set E} (KA : Subgroup G)
    (hrepair : ∀ (s t : V) (k : G),
      D.WalkValue Set.univ edgeValue s t k → k ∈ KA →
        D.WalkValue A edgeValue s t k)
    {s t v : V} {h a b q : G}
    (p : D.WalkValue Set.univ edgeValue s t h)
    (ha : a ∈ KA) (hq : q ∈ KA) (hab : a = h * b)
    (r : D.WalkValue B edgeValue v t (q⁻¹ * b⁻¹)) :
    (v, a * q) ∈ D.componentSet A edgeValue (s, 1) ∩
      D.componentSet B edgeValue (t, h) := by
  have rr := r.symm (fun e _ => hinv e)
  have heq : (q⁻¹ * b⁻¹)⁻¹ = b * q := by group
  rw [heq] at rr
  have ptotal : D.WalkValue Set.univ edgeValue s v (a * q) := by
    have joined := p.trans (rr.mono (Set.subset_univ B))
    convert joined using 1 <;> rw [hab] <;> group
  have pa := hrepair s v (a * q) ptotal (KA.mul_mem ha hq)
  constructor
  · apply (D.mem_componentSet_iff A edgeValue s v 1 (a * q)).2
    simpa only [inv_one, one_mul] using pa
  · apply (D.mem_componentSet_iff B edgeValue t v h (a * q)).2
    convert rr using 1 <;> rw [hab] <;> group

end EdgeGraph
end GluingEPPA.Steiner
