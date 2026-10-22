import GluingEPPA.Steiner.DiagramOrderedCompletion

/-!
# Coherent completion of finite partial bijections

A partial bijection between subsets of a finite linearly ordered set
extends to a permutation by mapping the complements increasingly.
The extension preserves the prescribed partial map, sends the identity
to the identity, and commutes with composition. This constructs
the coherent permutations used in Section 6 of the Steiner proof.
-/

namespace GluingEPPA.Steiner.OrderedCompletion

universe u
variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]

/-- Extend a bijection of subsets by the unique increasing bijection
between their complements. -/
noncomputable def totalCompletion (U W : Finset A)
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W}) : Equiv.Perm A := by
  classical
  exact ((Equiv.sumCompl (fun x : A => x ∈ U)).symm.trans
    (Equiv.sumCongr f (complementIso U W f).toEquiv)).trans
    (Equiv.sumCompl (fun x : A => x ∈ W))

/-- The total completion agrees with the given partial bijection. -/
theorem totalCompletion_domain (U W : Finset A)
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (x : {x : A // x ∈ U}) :
    totalCompletion U W f x.val = (f x).val := by
  classical
  simp [totalCompletion]

/-- Outside the domain, the completion is the increasing bijection. -/
theorem totalCompletion_complement (U W : Finset A)
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (x : {x : A // x ∉ U}) :
    totalCompletion U W f x.val = ((complementIso U W f) x).val := by
  classical
  simp [totalCompletion]

/-- The extension of the identity partial bijection is the identity. -/
theorem totalCompletion_id (U : Finset A) :
    totalCompletion U U (Equiv.refl {x : A // x ∈ U}) =
      Equiv.refl A := by
  apply Equiv.ext
  intro a
  by_cases ha : a ∈ U
  · have h := totalCompletion_domain U U
        (Equiv.refl {x : A // x ∈ U}) ⟨a, ha⟩
    simpa using h
  · have h := totalCompletion_complement U U
        (Equiv.refl {x : A // x ∈ U}) ⟨a, ha⟩
    rw [complementIso_refl] at h
    simpa using h

/-- The increasing complement extensions are exactly coherent under
composition, not just compatible up to an arbitrary permutation. -/
theorem totalCompletion_trans (U W T : Finset A)
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (g : {x : A // x ∈ W} ≃ {x : A // x ∈ T}) :
    (totalCompletion U W f).trans (totalCompletion W T g) =
      totalCompletion U T (f.trans g) := by
  apply Equiv.ext
  intro a
  change totalCompletion W T g (totalCompletion U W f a) =
    totalCompletion U T (f.trans g) a
  by_cases ha : a ∈ U
  · let ua : {x : A // x ∈ U} := ⟨a, ha⟩
    have h1 := totalCompletion_domain U W f ua
    have h2 := totalCompletion_domain W T g (f ua)
    have h3 := totalCompletion_domain U T (f.trans g) ua
    calc
      totalCompletion W T g (totalCompletion U W f a) =
          totalCompletion W T g (f ua).val := by rw [h1]
      _ = (g (f ua)).val := h2
      _ = totalCompletion U T (f.trans g) a := by
        simpa only [Equiv.trans_apply] using h3.symm
  · let ua : {x : A // x ∉ U} := ⟨a, ha⟩
    have h1 := totalCompletion_complement U W f ua
    have h2 := totalCompletion_complement W T g (complementIso U W f ua)
    have h3 := totalCompletion_complement U T (f.trans g) ua
    have hc := congrArg
      (fun h : {x : A // x ∉ U} ≃o {x : A // x ∉ T} => (h ua : A))
      (complementIso_trans U W T f g)
    calc
      totalCompletion W T g (totalCompletion U W f a) =
          totalCompletion W T g ((complementIso U W f) ua).val := by rw [h1]
      _ = ((complementIso W T g) ((complementIso U W f) ua)).val := h2
      _ = ((complementIso U T (f.trans g)) ua).val := hc
      _ = totalCompletion U T (f.trans g) a := h3.symm

end GluingEPPA.Steiner.OrderedCompletion
