import GluingEPPA.Steiner.DiagramInitialSymmetry

/-!
# Partial automorphisms send actual labelled subsystems to their ranges

The initial Steiner diagram has *extensional* vertices: point sets and
triples, rather than tagged (permutation, subset) occurrences. This
module proves that a permutation extending a partial automorphism
sends the source labelled subsystem to the target labelled subsystem.
It is the missing site-identity step in the final coherent EPPA proof.

The second theorem uses the already checked coherent
increasing-complement completion, not an arbitrary extension.
-/

namespace GluingEPPA.Steiner.InitialSites

universe u
variable {A : Type u}

/-- Equality of labelled systems follows from equality of their two
fields. This elementary extensional lemma is independent of EPPA. -/
theorem SiteData.eq_of_fields (s t : SiteData A)
    (hp : s.points = t.points) (ht : s.triple = t.triple) : s = t := by
  cases s with
  | mk sp st =>
    cases t with
    | mk tp tt =>
      cases hp
      cases ht
      rfl

/-- A permutation sending U to W and preserving the induced triples
sends the actual labelled source subsystem to the target subsystem. -/
theorem relabel_induced_site
    (R : A → A → A → Prop)
    (U W : Set A) (hU : Closed R U) (hW : Closed R W)
    (σ : Equiv.Perm A)
    (hpts : ∀ x : A, x ∈ U ↔ σ x ∈ W)
    (htr : ∀ x y z : A, x ∈ U → y ∈ U → z ∈ U →
      (R x y z ↔ R (σ x) (σ y) (σ z))) :
    Site.relabel R σ (siteOf R U hU (Equiv.refl A)) =
      siteOf R W hW (Equiv.refl A) := by
  apply Subtype.ext
  change SiteData.relabel σ (induced R U) = induced R W
  apply SiteData.eq_of_fields
  · apply Set.ext
    intro x
    change (σ.symm x ∈ U) ↔ x ∈ W
    simpa only [Equiv.apply_symm_apply] using hpts (σ.symm x)
  · funext x y z
    apply propext
    change (R (σ.symm x) (σ.symm y) (σ.symm z) ∧
      σ.symm x ∈ U ∧ σ.symm y ∈ U ∧ σ.symm z ∈ U) ↔
      (R x y z ∧ x ∈ W ∧ y ∈ W ∧ z ∈ W)
    have hx : (σ.symm x ∈ U) ↔ x ∈ W := by
      simpa only [Equiv.apply_symm_apply] using hpts (σ.symm x)
    have hy : (σ.symm y ∈ U) ↔ y ∈ W := by
      simpa only [Equiv.apply_symm_apply] using hpts (σ.symm y)
    have hz : (σ.symm z ∈ U) ↔ z ∈ W := by
      simpa only [Equiv.apply_symm_apply] using hpts (σ.symm z)
    constructor
    · rintro ⟨ht, hu, hv, hw⟩
      have h := (htr (σ.symm x) (σ.symm y) (σ.symm z) hu hv hw).mp ht
      refine ⟨?_, hx.mp hu, hy.mp hv, hz.mp hw⟩
      simpa only [Equiv.apply_symm_apply] using h
    · rintro ⟨ht, hu, hv, hw⟩
      have hu' : σ.symm x ∈ U := hx.mpr hu
      have hv' : σ.symm y ∈ U := hy.mpr hv
      have hw' : σ.symm z ∈ U := hz.mpr hw
      refine ⟨?_, hu', hv', hw'⟩
      apply (htr (σ.symm x) (σ.symm y) (σ.symm z)
        hu' hv' hw').mpr
      simpa only [Equiv.apply_symm_apply] using ht

variable [Fintype A] [LinearOrder A] [DecidableEq A]

/-- The coherent increasing-complement completion sends the
induced subsystem on U to the induced subsystem on W, provided f
is a partial automorphism between those closed subsystems. -/
theorem totalCompletion_maps_site
    (P : Input A) (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (hf : ∀ (x y z : A) (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U),
      P.triple x y z ↔
        P.triple (f ⟨x,hx⟩).val (f ⟨y,hy⟩).val (f ⟨z,hz⟩).val) :
    Site.relabel P.triple (OrderedCompletion.totalCompletion U W f)
        (siteOf P.triple (U : Set A) hU (Equiv.refl A)) =
      siteOf P.triple (W : Set A) hW (Equiv.refl A) := by
  let σ := OrderedCompletion.totalCompletion U W f
  have hp : ∀ x : A, x ∈ (U : Set A) ↔ σ x ∈ (W : Set A) := by
    intro x
    change x ∈ U ↔ σ x ∈ W
    constructor
    · intro hx
      have he := OrderedCompletion.totalCompletion_domain U W f ⟨x,hx⟩
      change σ x = (f ⟨x,hx⟩).val at he
      rw [he]
      exact (f ⟨x,hx⟩).property
    · intro hw
      by_contra hn
      have he := OrderedCompletion.totalCompletion_complement U W f ⟨x,hn⟩
      change σ x = ((OrderedCompletion.complementIso U W f) ⟨x,hn⟩).val at he
      rw [he] at hw
      exact ((OrderedCompletion.complementIso U W f) ⟨x,hn⟩).property hw
  have ht : ∀ x y z : A, x ∈ (U : Set A) →
      y ∈ (U : Set A) → z ∈ (U : Set A) →
      (P.triple x y z ↔ P.triple (σ x) (σ y) (σ z)) := by
    intro x y z hx hy hz
    change x ∈ U at hx
    change y ∈ U at hy
    change z ∈ U at hz
    change P.triple x y z ↔
      P.triple (OrderedCompletion.totalCompletion U W f x)
        (OrderedCompletion.totalCompletion U W f y)
        (OrderedCompletion.totalCompletion U W f z)
    rw [OrderedCompletion.totalCompletion_domain U W f ⟨x,hx⟩,
      OrderedCompletion.totalCompletion_domain U W f ⟨y,hy⟩,
      OrderedCompletion.totalCompletion_domain U W f ⟨z,hz⟩]
    exact hf x y z hx hy hz
  exact relabel_induced_site P.triple
    (U : Set A) (W : Set A) hU hW σ hp ht

end GluingEPPA.Steiner.InitialSites
