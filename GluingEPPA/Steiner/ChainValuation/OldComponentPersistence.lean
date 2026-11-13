import GluingEPPA.Steiner.ChainValuation.LastCosetStep

/-!
# Persistence of all old M-components under a true chain extension

The last-block coset induction describes the new final Cayley block.
To classify components in *all* historical blocks we also need that
a later separated attachment neither merges nor splits any old
M-component. This theorem proves the two-way correspondence of genuine
M-coloured reachability on the old chain and its image in the
literal extended chain.

It assumes only the explicit attachment-component pullback condition.
That condition is derived from the true earlier Links and
last-block coset invariant in the separate induction modules.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]
variable (A B : GroupBlock E) (C : ChainState E A)
variable (h : A.Carrier)
variable (left : K →* A.Carrier) (right : K →* B.Carrier)
variable (hleft : Function.Injective left) (hright : Function.Injective right)
variable (hsep : Disjoint C.entry (exitSet A h left))
variable (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
  ∃ k : K, left k = A.edge e ∧ right k = B.edge e)

/-- In an actual chain extension, restriction to the embedded old
chain reflects and preserves the entire M-component equivalence.
It is not merely injectivity of vertices. -/
theorem extended_old_reach_iff_original
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (x y : C.Space) :
    LabelReach
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel) M
      (oldEmbed A B C h left right hleft hright x)
      (oldEmbed A B C h left right hleft hright y) ↔
    LabelReach (fun e => (C.matching e).Rel) M x y := by
  constructor
  · exact chainExtend_old_components_reflect
      A B C h left right hleft hright hsep hshared M hpull x y
  · intro hxy
    apply LabelReach.map
      (fun e => (C.matching e).Rel)
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel)
      M (oldEmbed A B C h left right hleft hright)
    · intro e a b hab
      exact Or.inl ⟨a, b, hab, rfl, rfl⟩
    · exact hxy

end GluingEPPA.Steiner.ChainValuation
