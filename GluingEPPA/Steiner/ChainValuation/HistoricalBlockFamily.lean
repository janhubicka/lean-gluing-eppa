import GluingEPPA.Steiner.ChainValuation.HistoricalCosetCharts

/-!
# Finite collections of historical coset charts

The groups of successive earlier Cayley blocks need not be identical.
Bundle each historical group together with its actual subgroup and
injective chart into the current chain. Then transport the entire
finite list through each exact attachment and append the new final
block. This avoids an invented common ambient group and preserves
every historical component classification.

This is a generic finite-history construction. Instantiating the
construction with the literal LinkChain.buildNonempty recursor and
its previously checked pullback theorem is a separate step.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- A historical group block bundled with its own group,
restricted subgroup and labelled component chart in the current
chain state. The family may contain pairwise different groups. -/
structure HistoricalBlock
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) where
  Carrier : Type v
  [group : Group Carrier]
  subgroup : Subgroup Carrier
  chart : HistoricalCosetChart A C M subgroup

attribute [instance] HistoricalBlock.group

/-- The current last Cayley block supplies an additional historical
block with its genuine subgroup and last-embedding chart. -/
def historicalBlock_last
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (P : Subgroup A.Carrier)
    (h : LastBlockCosetInvariant A C M P) :
    HistoricalBlock A C M where
  Carrier := A.Carrier
  group := inferInstance
  subgroup := P
  chart := historicalLastChart A C M P h

/-- Transport an arbitrary historical block through one additional
separated attachment. Both the subgroup and its carrier remain
unchanged, while its chart composes with the literal old embedding. -/
def HistoricalBlock.transport
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (T : HistoricalBlock A C M) :
    HistoricalBlock B
      (GluingEPPA.Steiner.ChainValuation.extend
        A B C h left right hleft hright hsep hshared) M where
  Carrier := T.Carrier
  group := T.group
  subgroup := T.subgroup
  chart := T.chart.extend A B C h left right hleft hright hsep hshared
    M hpull T.subgroup

/-- An extension keeps *all* previous charts and appends exactly one
new historical block. This construction is independent of whether
different earlier groups have the same cardinality. -/
noncomputable def historicalBlocks_extend
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (Q : Subgroup B.Carrier)
    (hnew : LastBlockCosetInvariant B
      (GluingEPPA.Steiner.ChainValuation.extend
        A B C h left right hleft hright hsep hshared) M Q)
    (history : List (HistoricalBlock A C M)) :
    List (HistoricalBlock B
      (GluingEPPA.Steiner.ChainValuation.extend
        A B C h left right hleft hright hsep hshared) M) :=
  history.map (fun T =>
    T.transport A B C h left right hleft hright hsep hshared M hpull) ++
  [historicalBlock_last B
    (GluingEPPA.Steiner.ChainValuation.extend
      A B C h left right hleft hright hsep hshared) M Q hnew]

/-- One extension adds exactly one historical block to the list. -/
theorem historicalBlocks_extend_length
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (Q : Subgroup B.Carrier)
    (hnew : LastBlockCosetInvariant B
      (GluingEPPA.Steiner.ChainValuation.extend
        A B C h left right hleft hright hsep hshared) M Q)
    (history : List (HistoricalBlock A C M)) :
    (historicalBlocks_extend A B C h left right hleft hright
      hsep hshared M hpull Q hnew history).length =
        history.length + 1 := by
  simp [historicalBlocks_extend]

end GluingEPPA.Steiner.ChainValuation
