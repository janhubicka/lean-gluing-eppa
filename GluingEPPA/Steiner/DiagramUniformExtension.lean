import GluingEPPA.Steiner.DiagramCoherentFamily

/-!
# A common proof for proper and full domains

The two pointwise extension lemmas have already been checked. A partial
bijection between subsets of a finite set has full domain if and only
if it has full image. Therefore the source/target prefixes are either
both original root-edge involutions, or both identity.

This is the uniform final extension-on-embedded-points statement.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]
variable (P : Input A)
variable [Fintype (Edge P.triple)] [DecidableEq (Edge P.triple)]

/-- Full source and full target are equivalent for a finite partial
bijection, using the coherent increasing-complement completion. -/
theorem full_domain_iff_full_range (U W : Finset A)
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W}) :
    (U : Set A) = Set.univ ↔ (W : Set A) = Set.univ := by
  constructor
  · intro hU
    apply Set.eq_univ_of_forall
    intro y
    let σ := OrderedCompletion.totalCompletion U W f
    let x := σ.symm y
    have hx : x ∈ U := by
      change x ∈ (U : Set A)
      rw [hU]
      trivial
    have he := OrderedCompletion.totalCompletion_domain U W f ⟨x, hx⟩
    have hxy : σ x = y := σ.apply_symm_apply y
    rw [hxy] at he
    change y ∈ W
    rw [he]
    exact (f ⟨x, hx⟩).property
  · intro hW
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hcomp := ((OrderedCompletion.complementIso U W f) ⟨x, hx⟩).property
    have hw : ((OrderedCompletion.complementIso U W f) ⟨x, hx⟩).val ∈ W := by
      change ((OrderedCompletion.complementIso U W f) ⟨x, hx⟩).val ∈
        (W : Set A)
      rw [hW]
      trivial
    exact hcomp hw

/-- The three-factor coherent extension agrees with the original
partial automorphism on every embedded root point, for *all* closed
source and target subsystems. -/
theorem coherentExtension_on_root
    (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (hf : ∀ (x y z : A) (hx : x ∈ U) (hy : y ∈ U)
      (hz : z ∈ U),
      P.triple x y z ↔ P.triple (f ⟨x, hx⟩).val
        (f ⟨y, hy⟩).val (f ⟨z, hz⟩).val)
    (x : A) (hx : x ∈ U) :
    (coherentExtension P U W hU hW f)
      (canonicalPoint (graph P.triple) (localDiagram P)
        (root P.triple) 1 x (root_present P x)) =
      canonicalPoint (graph P.triple) (localDiagram P)
        (root P.triple) 1 (f ⟨x, hx⟩).val
        (root_present P (f ⟨x, hx⟩).val) := by
  by_cases hFull : (U : Set A) = Set.univ
  · have hFullW : (W : Set A) = Set.univ :=
      (full_domain_iff_full_range U W f).mp hFull
    let σ := OrderedCompletion.totalCompletion U W f
    have hσ : ∀ a b c : A,
        P.triple a b c ↔ P.triple (σ a) (σ b) (σ c) := by
      intro a b c
      have ha : a ∈ U := by
        change a ∈ (U : Set A)
        rw [hFull]
        trivial
      have hb : b ∈ U := by
        change b ∈ (U : Set A)
        rw [hFull]
        trivial
      have hc : c ∈ U := by
        change c ∈ (U : Set A)
        rw [hFull]
        trivial
      change P.triple a b c ↔
        P.triple (OrderedCompletion.totalCompletion U W f a)
          (OrderedCompletion.totalCompletion U W f b)
          (OrderedCompletion.totalCompletion U W f c)
      rw [OrderedCompletion.totalCompletion_domain U W f ⟨a,ha⟩,
        OrderedCompletion.totalCompletion_domain U W f ⟨b,hb⟩,
        OrderedCompletion.totalCompletion_domain U W f ⟨c,hc⟩]
      exact hf a b c ha hb hc
    have hpoint := extension_on_full_domain P σ hσ x
    have hfx : σ x = (f ⟨x,hx⟩).val := by
      exact OrderedCompletion.totalCompletion_domain U W f ⟨x,hx⟩
    simpa [coherentExtension, domainPrefix, hFull, hFullW, hfx] using hpoint
  · have hNotW : (W : Set A) ≠ Set.univ := by
      intro hWFull
      exact hFull ((full_domain_iff_full_range U W f).mpr hWFull)
    have hpoint := extension_on_proper_subsystems P U W hU hW
      hFull hNotW f hf x hx
    simpa [coherentExtension, domainPrefix, hFull, hNotW] using hpoint

end GluingEPPA.Steiner.InitialSites
