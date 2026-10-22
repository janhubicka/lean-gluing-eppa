import GluingEPPA.Steiner.DiagramInitialSteiner

/-!
# The point represented by the root and by its closed subsystem

For every proper closed U, the distinguished edge e_U identifies each
point x in U of the original root with its occurrence in the local
copy at U. The second valuation coordinate is precisely the generator
named by e_U. This is the equality used in the three-step formula
P_W ∘ F_sigma ∘ P_U of Section 6.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord

universe u
variable {A : Type u} (P : Input A)

/-- Every ambient point label occurs at the distinguished full copy. -/
theorem root_present (x : A) :
    (localDiagram P).present (root P.triple) x := by
  change x ∈ (root P.triple).val.points
  rw [root_full]
  trivial

/-- A member of a closed subset occurs in its induced local copy. -/
theorem subsystem_present (U : Set A) (hU : Closed P.triple U)
    (x : A) (hx : x ∈ U) :
    (localDiagram P).present
      (siteOf P.triple U hU (Equiv.refl A)) x := by
  change x ∈ (siteOf P.triple U hU (Equiv.refl A)).val.points
  simpa only [siteOf_points_id] using hx

variable [Finite A] [Fintype (Edge P.triple)] [DecidableEq (Edge P.triple)]

/-- The two representatives of a root point are exactly equal in the
actual free quotient, not merely in a projection or another cover. -/
theorem root_point_eq_subsystem (U : Set A) (hU : Closed P.triple U)
    (hProper : U ≠ Set.univ) (x : A) (hx : x ∈ U) :
    canonicalPoint (graph P.triple) (localDiagram P)
      (root P.triple) 1 x (root_present P x) =
    canonicalPoint (graph P.triple) (localDiagram P)
      (siteOf P.triple U hU (Equiv.refl A))
      ((family (graph P.triple) Finset.univ).edge
        (rootEdge P.triple U hU hProper))
      x (subsystem_present P U hU x hx) := by
  let D := graph P.triple
  let e := rootEdge P.triple U hU hProper
  have he : e ∈ edgesCarrying (localDiagram P).overlap x := by
    change x ∈ overlap P.triple (rootEdge P.triple U hU hProper)
    simpa only [rootEdge_overlap] using hx
  have hj : D.Joins e (root P.triple)
      (siteOf P.triple U hU (Equiv.refl A)) := by
    exact D.joins_endpoints e
  apply (canonicalPoint_eq_iff D (localDiagram P)
    (root P.triple) (siteOf P.triple U hU (Equiv.refl A))
    1 ((family D Finset.univ).edge e) x x
    (root_present P x) (subsystem_present P U hU x hx)).2
  refine ⟨rfl, ?_⟩
  have ht : D.CayleyWalk (edgesCarrying (localDiagram P).overlap x)
      (family D Finset.univ).edge
      (siteOf P.triple U hU (Equiv.refl A))
      (1 * (family D Finset.univ).edge e)
      (siteOf P.triple U hU (Equiv.refl A))
      ((family D Finset.univ).edge e) := by
    simpa only [one_mul] using
      (CayleyWalk.nil (siteOf P.triple U hU (Equiv.refl A))
        ((family D Finset.univ).edge e))
  exact CayleyWalk.cons he hj ht

end GluingEPPA.Steiner.InitialSites
