import GluingEPPA.Steiner.DiagramConcreteProperExtension

/-!
# The full-domain case of the Steiner coherent extension

A partial bijection of a finite ambient set has a full source exactly
when it has a full target. In that case it is an automorphism of the
entire input triple system. The chosen prefix at both ends is 1; only
the compatible relabelling remains.

This lemma checks the full/full case of the three-factor formula
directly on the embedded root points. No fictitious root loop is used.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {A : Type u} [Fintype A] [DecidableEq A]
variable (P : Input A)
variable [Fintype (Edge P.triple)] [DecidableEq (Edge P.triple)]

/-- Every automorphism of the input Steiner triples fixes the
actual labelled root site, including its point set. -/
theorem inputSymmetry_fixes_root
    (σ : Equiv.Perm A)
    (hσ : ∀ x y z : A,
      P.triple x y z ↔ P.triple (σ x) (σ y) (σ z)) :
    (inputSymmetry P σ).graph.vertex (root P.triple) =
      root P.triple := by
  let htop : Closed P.triple (Set.univ : Set A) := by
    intro x y z _ _ _
    trivial
  change Site.relabel P.triple σ
    (siteOf P.triple Set.univ htop (Equiv.refl A)) =
      siteOf P.triple Set.univ htop (Equiv.refl A)
  apply relabel_induced_site P.triple
    Set.univ Set.univ htop htop σ
  · intro x
    simp
  · intro x y z _ _ _
    exact hσ x y z

/-- When the partial automorphism is defined on all of A, its
extension is just the relabelling, and it sends each embedded
root point to its prescribed image. -/
theorem extension_on_full_domain
    (σ : Equiv.Perm A)
    (hσ : ∀ x y z : A,
      P.triple x y z ↔ P.triple (σ x) (σ y) (σ z))
    (x : A) :
    (extensionMap (graph P.triple) (localDiagram P)
      1 1 (inputSymmetry P σ))
        (canonicalPoint (graph P.triple) (localDiagram P)
          (root P.triple) 1 x (root_present P x)) =
      canonicalPoint (graph P.triple) (localDiagram P)
        (root P.triple) 1 (σ x) (root_present P (σ x)) := by
  exact extensionMap_on_local_point (graph P.triple) (localDiagram P)
    1 1 (inputSymmetry P σ) (by simp)
    (root P.triple) (root P.triple)
    (inputSymmetry_fixes_root P σ hσ)
    x (σ x) (root_present P x) (root_present P (σ x)) rfl

end GluingEPPA.Steiner.InitialSites
