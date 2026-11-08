import GluingEPPA.Steiner.DiagramExtensionPoints

/-!
# Concrete Steiner extensions on points of proper closed domains

We now combine the proved root-to-subsystem point identification,
the proved relabelling of the actual labelled subsystem by the
coherent completion sigma_f, and the three-factor extension formula.

This module handles proper source and target domains. The full-domain
convention P_A = identity is addressed separately, rather than
silently introducing a loop edge from the root to itself.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]
variable (P : Input A)
variable [Fintype (Edge P.triple)] [DecidableEq (Edge P.triple)]

/-- For proper closed domains U and W, the actual quotient
automorphism P_W F_(sigma_f) P_U maps every embedded x in U to
the embedded image f(x). -/
theorem extension_on_proper_subsystems
    (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (hproperU : (U : Set A) ≠ Set.univ)
    (hproperW : (W : Set A) ≠ Set.univ)
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (hf : ∀ (x y z : A) (hx : x ∈ U) (hy : y ∈ U)
      (hz : z ∈ U),
      P.triple x y z ↔ P.triple (f ⟨x,hx⟩).val
        (f ⟨y,hy⟩).val (f ⟨z,hz⟩).val)
    (x : A) (hx : x ∈ U) :
    (extensionMap (graph P.triple) (localDiagram P)
      ((family (graph P.triple) Finset.univ).edge
        (rootEdge P.triple (U : Set A) hU hproperU))
      ((family (graph P.triple) Finset.univ).edge
        (rootEdge P.triple (W : Set A) hW hproperW))
      (inputSymmetry P (OrderedCompletion.totalCompletion U W f)))
      (canonicalPoint (graph P.triple) (localDiagram P)
        (root P.triple) 1 x (root_present P x)) =
      canonicalPoint (graph P.triple) (localDiagram P)
        (root P.triple) 1 (f ⟨x,hx⟩).val
        (root_present P (f ⟨x,hx⟩).val) := by
  let D := graph P.triple
  let L := localDiagram P
  let σ := OrderedCompletion.totalCompletion U W f
  let sU := siteOf P.triple (U : Set A) hU (Equiv.refl A)
  let sW := siteOf P.triple (W : Set A) hW (Equiv.refl A)
  let kU := (family D Finset.univ).edge
    (rootEdge P.triple (U : Set A) hU hproperU)
  let kW := (family D Finset.univ).edge
    (rootEdge P.triple (W : Set A) hW hproperW)
  let t := inputSymmetry P σ
  let y := (f ⟨x,hx⟩).val
  have hxy : t.labels x = y := by
    change σ x = (f ⟨x,hx⟩).val
    exact OrderedCompletion.totalCompletion_domain U W f ⟨x,hx⟩
  have hsite : t.graph.vertex sU = sW := by
    change Site.relabel P.triple σ
      (siteOf P.triple (U : Set A) hU (Equiv.refl A)) =
      siteOf P.triple (W : Set A) hW (Equiv.refl A)
    exact totalCompletion_maps_site P U W hU hW f hf
  have hkU : kU * kU = 1 := by
    change (family D Finset.univ).edge
        (rootEdge P.triple (U : Set A) hU hproperU) *
      (family D Finset.univ).edge
        (rootEdge P.triple (U : Set A) hU hproperU) = 1
    exact family_square D Finset.univ
      (rootEdge P.triple (U : Set A) hU hproperU)
  have hxU : L.present sU x :=
    subsystem_present P (U : Set A) hU x hx
  have hyW : L.present sW y :=
    subsystem_present P (W : Set A) hW y (f ⟨x,hx⟩).property
  have hRU :
      canonicalPoint D L (root P.triple) 1 x (root_present P x) =
        canonicalPoint D L sU kU x hxU :=
    root_point_eq_subsystem P (U : Set A) hU hproperU x hx
  have hRW :
      canonicalPoint D L (root P.triple) 1 y (root_present P y) =
        canonicalPoint D L sW kW y hyW :=
    root_point_eq_subsystem P (W : Set A) hW hproperW y
      (f ⟨x,hx⟩).property
  have hmap :
      (extensionMap D L kU kW t) (canonicalPoint D L sU kU x hxU) =
        canonicalPoint D L sW kW y hyW :=
    extensionMap_on_local_point D L kU kW t hkU
      sU sW hsite x y hxU hyW hxy
  change (extensionMap D L kU kW t)
    (canonicalPoint D L (root P.triple) 1 x (root_present P x)) =
    canonicalPoint D L (root P.triple) 1 y (root_present P y)
  calc
    _ = (extensionMap D L kU kW t)
        (canonicalPoint D L sU kU x hxU) :=
      congrArg (extensionMap D L kU kW t) hRU
    _ = canonicalPoint D L sW kW y hyW := hmap
    _ = canonicalPoint D L (root P.triple) 1 y (root_present P y) :=
      hRW.symm

end GluingEPPA.Steiner.InitialSites
