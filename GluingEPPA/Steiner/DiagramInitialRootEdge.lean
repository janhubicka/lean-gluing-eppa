import GluingEPPA.Steiner.DiagramInitialEdges

/-!
# The distinguished inclusion edges in the finite Steiner EPPA diagram

For each proper closed subset U of the original Steiner system, the
initial diagram contains exactly one edge e_U joining its distinguished
full copy to the induced subsystem on U. Its gluing domain is exactly U.

This is the edge used in the representative calculation of Section 6.
The case U=A is deliberately separate: no loop or imaginary edge is
introduced.
-/

namespace GluingEPPA.Steiner.InitialSites

universe u
variable {A : Type u} (R : A → A → A → Prop)

/-- The point set of the unrelabeled induced subsystem is U. -/
@[simp] theorem siteOf_points_id (U : Set A) (hU : Closed R U) :
    (siteOf R U hU (Equiv.refl A)).val.points = U := by
  rfl

/-- The triples in the induced subsystem are exactly those of R
which have all three vertices in U. -/
theorem siteOf_triple_id (U : Set A) (hU : Closed R U)
    (x y z : A) :
    (siteOf R U hU (Equiv.refl A)).val.triple x y z ↔
      R x y z ∧ x ∈ U ∧ y ∈ U ∧ z ∈ U := by
  rfl

/-- A closed subset gives a closed induced subsystem of the root. -/
theorem root_closed_subsite (U : Set A) (hU : Closed R U) :
    ClosedSubsite R (siteOf R U hU (Equiv.refl A)) (root R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    trivial
  · intro x y z hx hy hz
    change x ∈ U at hx
    change y ∈ U at hy
    change z ∈ U at hz
    change (R x y z ∧ x ∈ U ∧ y ∈ U ∧ z ∈ U) ↔
      (R x y z ∧ True ∧ True ∧ True)
    simp [hx, hy, hz]
  · intro x y z ht hx hy
    change x ∈ U at hx
    change y ∈ U at hy
    exact hU x y z ((root_triple R x y z).mp ht) hx hy

/-- The literal original edge from the full system to U. -/
def rootEdge (U : Set A) (hU : Closed R U)
    (hProper : U ≠ Set.univ) : Edge R :=
  ⟨⟨root R, siteOf R U hU (Equiv.refl A)⟩,
    ⟨root_full R, root_closed_subsite R U hU, by
      change U ≠ (Set.univ : Set A)
      exact hProper⟩⟩

@[simp] theorem rootEdge_source (U : Set A) (hU : Closed R U)
    (hProper : U ≠ Set.univ) :
    (graph R).source (rootEdge R U hU hProper) = root R := rfl

@[simp] theorem rootEdge_target (U : Set A) (hU : Closed R U)
    (hProper : U ≠ Set.univ) :
    (graph R).target (rootEdge R U hU hProper) =
      siteOf R U hU (Equiv.refl A) := rfl

@[simp] theorem rootEdge_overlap (U : Set A) (hU : Closed R U)
    (hProper : U ≠ Set.univ) :
    overlap R (rootEdge R U hU hProper) = U := by
  rfl

end GluingEPPA.Steiner.InitialSites
