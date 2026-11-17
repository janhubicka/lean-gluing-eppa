import GluingEPPA.Steiner.RecordIsomorphism
import GluingEPPA.Steiner.ChainValuation.AugmentedStep
import GluingEPPA.Steiner.ChainValuation.AugmentedTestKernelTransport

/-!
# Relabelling word equalities in the full augmented record

The old direct-record coordinates transform by the original verified
record-naturality theorem. The added test coordinates transform by an
equivariant relabelling of the test package. This lemma combines both,
establishing that every *full augmented word equality* survives
relabelling, once test-coordinate transport has been constructed.

It is intentionally independent of a particular chain builder. The
remaining geometric task is to provide the test-index and chain-space
bijections from a diagram isomorphism of the actual recursive family.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.AugmentedStep

attribute [local instance] Classical.propDecidable

universe u
variable {V E V' E' J J' : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (X : J → Type u) [Finite J] [∀ j, Finite (X j)]
variable (τ : ∀ j, E → Equiv.Perm (X j))
variable (hτ : ∀ j e, τ j e * τ j e = 1)

/-- An equality of the augmented generated group is exactly equality of the
original direct record and every finite test permutation at that stage. -/
theorem word_values_eq_iff (p q : List E)
    (hp : ∀ e ∈ p, e ∈ S) (hq : ∀ e ∈ q, e ∈ S) :
    (p.map (data D S old X τ hτ).edge).prod =
      (q.map (data D S old X τ hτ).edge).prod ↔
    AugmentedRecord.value D (Step.sets S) (Step.groups S old)
      (Step.edges S old) (Step.involutions S old) X τ p =
    AugmentedRecord.value D (Step.sets S) (Step.groups S old)
      (Step.edges S old) (Step.involutions S old) X τ q := by
  have hP := AugmentedRecord.totalGenerator_product D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E) p hp
  have hQ := AugmentedRecord.totalGenerator_product D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E) q hq
  constructor
  · intro h
    have hv := congrArg
      (fun g : (data D S old X τ hτ).Carrier => g.val) h
    exact hP.symm.trans (hv.trans hQ)
  · intro h
    apply Subtype.ext
    exact hP.trans (h.trans hQ.symm)

/-- A full augmented-record word equality is preserved by a relabelling
whenever earlier groups have compatible generator isomorphisms and the
added finite tests have generator-compatible injective coordinate maps.
The statement discharges the full new-stage record comparison, but not
the construction of those maps from actual separated chains. -/
theorem preserves_word_equalities
    (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']
    (f : Iso D D') (T : Finset E')
    (old' : ∀ j : Proper T, Data E' j.val)
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S)
    (earlier : ∀ j : Proper T, ∃ i : Proper S,
      ∃ F : (old i).Carrier ≃* (old' j).Carrier,
        (∀ e, f.edge e ∈ j.val ↔ e ∈ i.val) ∧
        (∀ e ∈ i.val, F ((old i).edge e) =
          (old' j).edge (f.edge e)))
    (X' : J' → Type u) [Finite J'] [∀ j, Finite (X' j)]
    (τ' : ∀ j, E' → Equiv.Perm (X' j))
    (hτ' : ∀ j e, τ' j e * τ' j e = 1)
    (q : J ≃ J')
    (F : ∀ j : J,
      (Equiv.Perm (X j))ᵐᵒᵖ →*
        (Equiv.Perm (X' (q j)))ᵐᵒᵖ)
    (hF : ∀ j e, F j (MulOpposite.op (τ j e)) =
      MulOpposite.op (τ' (q j) (f.edge e)))
    (hInj : ∀ j, Function.Injective (F j))
    (p r : List E)
    (hp : ∀ e ∈ p, e ∈ S) (hr : ∀ e ∈ r, e ∈ S)
    (hvalue : (p.map (data D S old X τ hτ).edge).prod =
      (r.map (data D S old X τ hτ).edge).prod) :
    (p.map (fun e => (data D' T old' X' τ' hτ').edge (f.edge e))).prod =
      (r.map (fun e => (data D' T old' X' τ' hτ').edge (f.edge e))).prod := by
  have hsource := (word_values_eq_iff D S old X τ hτ p r hp hr).1 hvalue
  have hOldSource :
      DirectRecord.value D (Step.sets S) (Step.groups S old)
        (Step.edges S old) (Step.involutions S old) p =
      DirectRecord.value D (Step.sets S) (Step.groups S old)
        (Step.edges S old) (Step.involutions S old) r :=
    congrArg Prod.fst hsource
  have hSourceStep : (p.map (Step.data D S old).edge).prod =
      (r.map (Step.data D S old).edge).prod :=
    (Step.word_values_eq_iff D S old p r hp hr).2 hOldSource
  have hTargetStep := Step.preserves_word_equalities
    D S old D' f T old' hST earlier p r hp hr hSourceStep
  have hp' : ∀ e ∈ p.map f.edge, e ∈ T := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact (hST d).2 (hp d hd)
  have hr' : ∀ e ∈ r.map f.edge, e ∈ T := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact (hST d).2 (hr d hd)
  have hTargetOld :
      DirectRecord.value D' (Step.sets T) (Step.groups T old')
        (Step.edges T old') (Step.involutions T old') (p.map f.edge) =
      DirectRecord.value D' (Step.sets T) (Step.groups T old')
        (Step.edges T old') (Step.involutions T old') (r.map f.edge) := by
    apply (Step.word_values_eq_iff D' T old'
      (p.map f.edge) (r.map f.edge) hp' hr').1
    simpa only [List.map_map, Function.comp_def] using hTargetStep
  have hSourceTest :
      AugmentedRecord.testValue X τ p =
        AugmentedRecord.testValue X τ r :=
    congrArg Prod.snd hsource
  have hTargetTest :
      AugmentedRecord.testValue X' τ' (p.map f.edge) =
        AugmentedRecord.testValue X' τ' (r.map f.edge) :=
    (AugmentedRecord.testValue_kernel_iff
      f.edge q τ τ' F hF hInj p r).1 hSourceTest
  have hTargetRecord :
      AugmentedRecord.value D' (Step.sets T) (Step.groups T old')
        (Step.edges T old') (Step.involutions T old') X' τ' (p.map f.edge) =
      AugmentedRecord.value D' (Step.sets T) (Step.groups T old')
        (Step.edges T old') (Step.involutions T old') X' τ' (r.map f.edge) := by
    apply Prod.ext
    · exact hTargetOld
    · exact hTargetTest
  have hTargetGen := (word_values_eq_iff D' T old' X' τ' hτ'
    (p.map f.edge) (r.map f.edge) hp' hr').2 hTargetRecord
  simpa only [List.map_map, Function.comp_def] using hTargetGen

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.AugmentedStep
