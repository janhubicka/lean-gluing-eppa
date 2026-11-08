import GluingEPPA.BinaryOrbitSaturatedWitness

/-!
# EPPA with exact overlaps and a covering family in one binary relation

This theorem uses the standard RelStructure / Embedding / RelPartialAut
interface. It upgrades the class-specific EPPA theorem by restricting the
finite witness to those six-colour C4 orbits attained by the input. Thus
every witness point lies in an automorphic copy of the input.

The n-locally forest carrier theorem is not asserted.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

universe u

/-- The canonical embedding in the colour-saturated finite witness. -/
def activeEmbedding {A : Type u} (colour : A → Fin 6) :
    Embedding (binaryStructure colour)
      (binaryStructure (fun v : ActiveWitness colour => v.1.val)) where
  toFun := activeRoot colour
  injective := activeRoot_injective colour
  rel_iff := by
    intro n r q
    cases r
    rfl

/-- EPPA with exact intersections and a transitive covering orbit of copies.
    The last clause is expressed pointwise: every witness vertex is the
    image of an input point under a relation-preserving automorphism. -/
theorem finite_binary_orbit_eppa_with_covering
    {A : Type u} [Finite A] (colour : A → Fin 6) :
    ∃ (B : Type u) (T : RelStructure BinaryLanguage B)
      (ι : Embedding (binaryStructure colour) T),
      Finite B ∧
      (∀ f : RelPartialAut (binaryStructure colour),
        ∃ φ : B ≃ B,
          (∀ {n : Nat} (r : BinaryLanguage n) (q : Fin n → B),
            T.rel r (fun j => φ (q j)) ↔ T.rel r q) ∧
          (∀ x y : A,
            (φ (ι.toFun x) = ι.toFun y ↔ f.val x = some y))) ∧
      (∀ v : B,
        ∃ (a : A) (φ : B ≃ B),
          (∀ {n : Nat} (r : BinaryLanguage n) (q : Fin n → B),
            T.rel r (fun j => φ (q j)) ↔ T.rel r q) ∧
          φ (ι.toFun a) = v) := by
  let B := ActiveWitness colour
  let T : RelStructure BinaryLanguage B :=
    binaryStructure (fun v : B => v.1.val)
  let ι : Embedding (binaryStructure colour) T :=
    activeEmbedding colour
  refine ⟨B, T, ι, inferInstance, ?_, ?_⟩
  · intro f
    obtain ⟨k, hk⟩ :=
      partial_relation_map_has_global_shift colour f.val
        (pairwise_of_relPartialAut colour f)
    obtain ⟨φ, hpres, hoverlap⟩ :=
      exists_active_exact_extension colour k f.val
        (injective_of_relPartialAut colour f) hk
    refine ⟨φ, ?_, ?_⟩
    · intro n r q
      cases r
      change templateRel (φ (q 0)).1.val (φ (q 1)).1.val ↔
        templateRel (q 0).1.val (q 1).1.val
      exact hpres (q 0) (q 1)
    · intro x y
      exact hoverlap x y
  · intro v
    obtain ⟨a, φ, hpres, hhit⟩ := active_orbit_covers colour v
    refine ⟨a, φ, ?_, hhit⟩
    intro n r q
    cases r
    change templateRel (φ (q 0)).1.val (φ (q 1)).1.val ↔
      templateRel (q 0).1.val (q 1).1.val
    exact hpres (q 0) (q 1)

end GluingEPPA.BinaryOrbitNoncoherence
