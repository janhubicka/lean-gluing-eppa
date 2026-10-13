import GluingEPPA.PrivateCycleInjection
import GluingEPPA.PaddedFamily

/-!
The linear-size private two-/three-cycle padding from the circulation draft,
rather than the larger ZMod4-vector padding used in the initial EPPA proof.
-/
namespace GluingEPPA
universe u v w
namespace BaseFamily
variable {L : Nat → Type u} {A : Type v} {I : Type w}
variable {S : RelStructure L A} (F : BaseFamily S I) [LinearOrder I]

abbrev PrivatePaddedCarrier (A : Type v) (I : Type w) :=
  A ⊕ InverseLabels.PrivateSlots I

noncomputable def privateSigma (i : I) :
    PrivatePaddedCarrier A I ≃ PrivatePaddedCarrier A I :=
  Equiv.sumCongr (F.base i) (F.labels.privatePerm i)

theorem privateSigma_injective : Function.Injective F.privateSigma := by
  intro i j h
  apply F.labels.privatePerm_injective
  apply Equiv.ext
  intro v
  have hh : F.privateSigma i (Sum.inr v) = F.privateSigma j (Sum.inr v) :=
    congrArg (fun p => p (Sum.inr v)) h
  exact Sum.inr.inj hh

theorem privateSigma_inverse (i : I) :
    F.privateSigma (F.labels.inv i) = (F.privateSigma i).symm := by
  apply Equiv.ext
  intro v
  cases v with
  | inl x =>
    change Sum.inl (F.base (F.labels.inv i) x) = Sum.inl ((F.base i).symm x)
    rw [F.base_inverse i]
  | inr x =>
    change Sum.inr (F.labels.privatePerm (F.labels.inv i) x) =
      Sum.inr ((F.labels.privatePerm i).symm x)
    rw [F.labels.privatePerm_inverse i]

noncomputable def privateData :
    PermutationDiagramData S (PrivatePaddedCarrier A I) I where
  incl := ⟨Sum.inl, Sum.inl_injective⟩
  sigma := F.privateSigma
  sigma_injective := F.privateSigma_injective
  inverse := F.labels.inv
  sigma_inverse := F.privateSigma_inverse
  transport := F.transport
  transport_inverse := F.transport_inverse
  transport_sigma := by
    intro i x y h
    change Sum.inl (F.base i x) = Sum.inl y
    rw [F.transport_base i x y h]
  transport_rel := F.transport_rel

theorem privateSigma_ne_refl (i : I) : F.privateSigma i ≠ Equiv.refl _ := by
  intro h
  apply F.labels.privatePerm_ne_refl i
  apply Equiv.ext
  intro v
  have hh : F.privateSigma i (Sum.inr v) =
      (Equiv.refl (PrivatePaddedCarrier A I)) (Sum.inr v) :=
    congrArg (fun p => p (Sum.inr v)) h
  exact Sum.inr.inj hh

theorem privateCarrier_card [Fintype A] [Fintype I] :
    Fintype.card (PrivatePaddedCarrier A I) =
        Fintype.card A + 2 * Fintype.card I := by
  simp only [PrivatePaddedCarrier, Fintype.card_sum]
  rw [F.labels.privateSlots_card]

end BaseFamily
end GluingEPPA
