import GluingEPPA.Marker4

/-!
Build the concrete labelled permutation diagram from finite partial transports
with given inverse-compatible extensions on A, using independent ZMod4 marker
translations. The markers enforce pairwise distinctness and nonidentity.

This uses more marker points than the private 2/3-cycle padding in the
manuscript; it validates existence, not the manuscript's numerical bound.
-/
namespace GluingEPPA
universe u v w

structure BaseFamily {L : Nat → Type u} {A : Type v}
    (S : RelStructure L A) (I : Type w) where
  labels : InverseLabels I
  base : I → (A ≃ A)
  base_inverse : ∀ i, base (labels.inv i) = (base i).symm
  transport : I → A → A → Prop
  transport_inverse : ∀ i x y,
    transport i x y ↔ transport (labels.inv i) y x
  transport_base : ∀ i x y, transport i x y → base i x = y
  transport_rel : ∀ {n} (r : L n) (i : I) (x y : Fin n → A),
    (∀ j, transport i (x j) (y j)) → (S.rel r x ↔ S.rel r y)

namespace BaseFamily
variable {L : Nat → Type u} {A : Type v} {I : Type w}
variable {S : RelStructure L A} (F : BaseFamily S I) [DecidableEq I]

abbrev PaddedCarrier (A : Type v) (I : Type w) :=
  A ⊕ InverseLabels.Marker I

def paddedSigma (i : I) : PaddedCarrier A I ≃ PaddedCarrier A I :=
  Equiv.sumCongr (F.base i) (F.labels.markerPerm i)

theorem paddedSigma_injective : Function.Injective F.paddedSigma := by
  intro i j h
  apply F.labels.markerPerm_injective
  apply Equiv.ext
  intro v
  have hh : F.paddedSigma i (Sum.inr v) = F.paddedSigma j (Sum.inr v) :=
    congrArg (fun p => p (Sum.inr v)) h
  exact Sum.inr.inj hh

theorem paddedSigma_inverse (i : I) :
    F.paddedSigma (F.labels.inv i) = (F.paddedSigma i).symm := by
  apply Equiv.ext
  intro v
  cases v with
  | inl x =>
    change Sum.inl (F.base (F.labels.inv i) x) = Sum.inl ((F.base i).symm x)
    rw [F.base_inverse i]
  | inr x =>
    change Sum.inr (F.labels.markerPerm (F.labels.inv i) x) =
      Sum.inr ((F.labels.markerPerm i).symm x)
    rw [F.labels.markerPerm_inverse i]

/-- Inject A as the original summand and use the marker summand solely
to distinguish generators. -/
def paddedData : PermutationDiagramData S (PaddedCarrier A I) I where
  incl := ⟨Sum.inl, Sum.inl_injective⟩
  sigma := F.paddedSigma
  sigma_injective := F.paddedSigma_injective
  inverse := F.labels.inv
  sigma_inverse := F.paddedSigma_inverse
  transport := F.transport
  transport_inverse := F.transport_inverse
  transport_sigma := by
    intro i x y h
    change Sum.inl (F.base i x) = Sum.inl y
    rw [F.transport_base i x y h]
  transport_rel := F.transport_rel

theorem paddedSigma_ne_refl (i : I) : F.paddedSigma i ≠ Equiv.refl _ := by
  intro h
  apply F.labels.markerPerm_ne_refl i
  apply Equiv.ext
  intro v
  have hh : F.paddedSigma i (Sum.inr v) =
      (Equiv.refl (PaddedCarrier A I)) (Sum.inr v) :=
    congrArg (fun p => p (Sum.inr v)) h
  exact Sum.inr.inj hh

end BaseFamily
end GluingEPPA
