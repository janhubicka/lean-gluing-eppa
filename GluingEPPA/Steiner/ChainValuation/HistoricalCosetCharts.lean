import GluingEPPA.Steiner.ChainValuation.OldComponentPersistence

/-!
# Coset charts for historical blocks of an actual separated chain

The current last-block invariant alone does not describe intersections of
M-components with *earlier* blocks. We record an embedded historical block
together with the two-way equivalence saying its M-components are exactly
cosets of a specified subgroup. A further separated attachment transports
this chart through the exact old-block embedding, provided the attachment
has the (already isolated) restricted-component pullback property.

This module proves preservation of one arbitrary historical chart; it does
not claim the whole finite family of historical blocks has been constructed.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {H K : Type v} [Group H] [Group K]

/-- An actual historical block embeds in a chain, and the pullback of the
M-component equivalence is precisely the left-coset equivalence of P. -/
structure HistoricalCosetChart
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (P : Subgroup H) where
  embed : H → C.Space
  injective : Function.Injective embed
  reach_iff : ∀ x y : H,
    LabelReach (fun e => (C.matching e).Rel) M (embed x) (embed y) ↔
      y ∈ leftCoset P x

/-- The last block is itself a historical chart, and the last-block
invariant is exactly the component statement needed for that chart. -/
def historicalLastChart
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (P : Subgroup A.Carrier)
    (h : LastBlockCosetInvariant A C M P) :
    HistoricalCosetChart A C M P where
  embed := C.lastEmbed
  injective := C.lastInjective
  reach_iff := h

/-- The intersection of any M-component with one historical block is
one entire restricted coset; no proper subset or union of two cosets
can appear in the preimage of the chart. -/
theorem HistoricalCosetChart.component_preimage
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (P : Subgroup H)
    (T : HistoricalCosetChart A C M P) (x : H) :
    {y : H | LabelReach (fun e => (C.matching e).Rel) M
      (T.embed x) (T.embed y)} = leftCoset P x := by
  ext y
  exact T.reach_iff x y

/-- Every additional true chain attachment preserves the full
historical-component coset classification of the entire old block.
This is stronger than simple injectivity of its vertices. -/
def HistoricalCosetChart.extend
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (P : Subgroup H) (T : HistoricalCosetChart A C M P) :
    HistoricalCosetChart B
      (GluingEPPA.Steiner.ChainValuation.extend A B C h left right hleft hright hsep hshared)
      M P where
  embed := fun x => oldEmbed A B C h left right hleft hright (T.embed x)
  injective := by
    intro x y hxy
    exact T.injective
      ((oldEmbed_injective A B C h left right hleft hright) hxy)
  reach_iff := by
    intro x y
    exact (extended_old_reach_iff_original
      A B C h left right hleft hright hsep hshared
      M hpull (T.embed x) (T.embed y)).trans (T.reach_iff x y)

end GluingEPPA.Steiner.ChainValuation
