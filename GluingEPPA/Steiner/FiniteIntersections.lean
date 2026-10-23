import GluingEPPA.Steiner.RecursiveNaturality

/-!
# The nonempty finite-family form of exact component intersection

The manuscript uses arbitrary edge subsets and a nonempty finite family of
them. This file passes from the checked finite-set binary theorem to exactly
that form. Every restricted walk keeps the same final valuation group.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E I : Type u} (D : EdgeGraph V E)
variable [Finite V] [Fintype E] [DecidableEq E]

noncomputable def edgeSubset (M : Set E) : Finset E :=
  Finset.univ.filter (fun e => e ∈ M)

@[simp] theorem edgeSubset_coe (M : Set E) : ((edgeSubset M : Finset E) : Set E) = M := by
  ext e
  simp [edgeSubset]

/-- The binary identity in the paper's set notation. -/
theorem set_component_intersection (M N : Set E)
    (z : V × (family D Finset.univ).Carrier) :
    D.componentSet M (family D Finset.univ).edge z ∩
        D.componentSet N (family D Finset.univ).edge z =
      D.componentSet (M ∩ N) (family D Finset.univ).edge z := by
  have h := component_intersection D (edgeSubset M) (edgeSubset N) z
  simpa only [Finset.coe_inter, edgeSubset_coe] using h

theorem set_exact_intersection_walk (M N : Set E) (u v : V)
    (g h : (family D Finset.univ).Carrier)
    (p : D.CayleyWalk M (family D Finset.univ).edge u g v h)
    (q : D.CayleyWalk N (family D Finset.univ).edge u g v h) :
    D.CayleyWalk (M ∩ N) (family D Finset.univ).edge u g v h := by
  have hy : (v,h) ∈ D.componentSet M (family D Finset.univ).edge (u,g) ∩
      D.componentSet N (family D Finset.univ).edge (u,g) := ⟨p,q⟩
  rw [set_component_intersection D M N (u,g)] at hy
  exact hy

/-- The family is nonempty, as required in the manuscript. Both endpoints stay fixed. -/
theorem finite_intersection_walk (J : Finset I) (hJ : J.Nonempty) (M : I → Set E)
    (u v : V) (g h : (family D Finset.univ).Carrier)
    (p : ∀ i ∈ J, D.CayleyWalk (M i) (family D Finset.univ).edge u g v h) :
    D.CayleyWalk {e | ∀ i ∈ J, e ∈ M i} (family D Finset.univ).edge u g v h := by
  classical
  revert hJ p
  induction J using Finset.induction_on with
  | empty =>
      intro hJ _
      obtain ⟨i, hi⟩ := hJ
      simp at hi
  | @insert i J hi ih =>
      intro _ p
      by_cases hJ : J.Nonempty
      · have q := ih hJ (fun j hj => p j (Finset.mem_insert_of_mem hj))
        have r := set_exact_intersection_walk D (M i) {e | ∀ j ∈ J, e ∈ M j}
          u v g h (p i (Finset.mem_insert_self i J)) q
        have heq : M i ∩ {e | ∀ j ∈ J, e ∈ M j} =
            {e | ∀ j ∈ insert i J, e ∈ M j} := by
          ext e
          simp
        rw [heq] at r
        exact r
      · have hJ0 : J = ∅ := by
          apply Finset.ext
          intro j
          constructor
          · intro hj
            exact (hJ ⟨j,hj⟩).elim
          · intro hj
            simp at hj
        subst J
        have heq : {e | ∀ j ∈ insert i (∅ : Finset I), e ∈ M j} = M i := by
          ext e
          simp
        rw [heq]
        exact p i (by simp)

/-- Exact intersections for any nonempty finite family, in component-set notation. -/
theorem component_finite_intersection (J : Finset I) (hJ : J.Nonempty) (M : I → Set E)
    (z : V × (family D Finset.univ).Carrier) :
    (⋂ i ∈ J, D.componentSet (M i) (family D Finset.univ).edge z) =
      D.componentSet {e | ∀ i ∈ J, e ∈ M i} (family D Finset.univ).edge z := by
  ext y
  simp only [Set.mem_iInter]
  change (∀ i ∈ J, D.CayleyWalk (M i) (family D Finset.univ).edge
      z.1 z.2 y.1 y.2) ↔
    D.CayleyWalk {e | ∀ i ∈ J, e ∈ M i} (family D Finset.univ).edge z.1 z.2 y.1 y.2
  constructor
  · exact finite_intersection_walk D J hJ M z.1 y.1 z.2 y.2
  · intro p i hi
    exact p.mono (show {e : E | ∀ j ∈ J, e ∈ M j} ⊆ M i from
      fun e he => he i hi)

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
