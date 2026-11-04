import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutEdges

/-!
# M-saturation of a matched union of restricted pushout pieces

The previous module proves that the exact restricted pushout has
precisely the induced genuine edges from the full pushout.
To conclude that its completed letter actions are the *same*
as those of the ambient chain component, the selected union must
also be closed under every outgoing edge of a retained colour.

This is automatic if both selected block pieces are closed under
their genuine M-edges and the restrictions agree on the attachment
parameters. The result rules out an ambient M-edge escaping the
selected union, including at a point represented by both blocks.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w e
variable {X : Type u} {Y : Type v} {Z : Type w} {E : Type e}
variable {f : Z → X} {g : Z → Y}

namespace MatchedRestriction
variable (R : MatchedRestriction f g)

/-- The selected union has no outgoing genuine M-coloured edge
when each selected piece is closed under such edges locally. -/
theorem covered_closed_under_mask
    (hf : Function.Injective f) (hg : Function.Injective g)
    (M : Finset E)
    (leftEdges : E → X → X → Prop)
    (rightEdges : E → Y → Y → Prop)
    (hleft : ∀ (letter : E), letter ∈ M →
      ∀ x y : X, leftEdges letter x y → x ∈ R.left → y ∈ R.left)
    (hright : ∀ (letter : E), letter ∈ M →
      ∀ x y : Y, rightEdges letter x y → x ∈ R.right → y ∈ R.right)
    (letter : E) (he : letter ∈ M)
    (p q : SetPushout f g hf hg)
    (hp : p ∈ R.Covered hf hg)
    (hEdge : quotientEdges leftEdges rightEdges f g hf hg
      letter p q) :
    q ∈ R.Covered hf hg := by
  rcases hEdge with ⟨x, y, hxy, hpx, hqy⟩ |
    ⟨x, y, hxy, hpx, hqy⟩
  · have hx : x ∈ R.left :=
      (R.inl_mem_covered_iff hf hg x).mp (by
        rw [hpx]
        exact hp)
    have hy : y ∈ R.left :=
      hleft letter he x y hxy hx
    rw [← hqy]
    exact (R.inl_mem_covered_iff hf hg y).mpr hy
  · have hx : x ∈ R.right :=
      (R.inr_mem_covered_iff hf hg x).mp (by
        rw [hpx]
        exact hp)
    have hy : y ∈ R.right :=
      hright letter he x y hxy hx
    rw [← hqy]
    exact (R.inr_mem_covered_iff hf hg y).mpr hy

/-- Every genuine M-edge from a selected vertex remains within
the image of the exact restricted pushout, so the converse
edge-lifting theorem from RestrictedPushoutEdges can be used
for the *full* M-edge action of this component. -/
theorem mask_edge_lifts_from_image
    (hf : Function.Injective f) (hg : Function.Injective g)
    (M : Finset E)
    (leftEdges : E → X → X → Prop)
    (rightEdges : E → Y → Y → Prop)
    (hleft : ∀ (letter : E), letter ∈ M →
      ∀ x y : X, leftEdges letter x y → x ∈ R.left → y ∈ R.left)
    (hright : ∀ (letter : E), letter ∈ M →
      ∀ x y : Y, rightEdges letter x y → x ∈ R.right → y ∈ R.right)
    (letter : E) (he : letter ∈ M)
    (p : R.Space hf hg)
    (q : SetPushout f g hf hg)
    (hEdge : quotientEdges leftEdges rightEdges f g hf hg
      letter (R.intoFull hf hg p) q) :
    ∃ p' : R.Space hf hg,
      R.intoFull hf hg p' = q ∧
      quotientEdges
        (fun e (x y : R.Left) => leftEdges e x.val y.val)
        (fun e (x y : R.Right) => rightEdges e x.val y.val)
        R.leftAttach R.rightAttach
        (R.leftAttach_injective hf) (R.rightAttach_injective hg)
        letter p p' := by
  have hq : q ∈ R.Covered hf hg :=
    R.covered_closed_under_mask hf hg M leftEdges rightEdges
      hleft hright letter he (R.intoFull hf hg p) q
      (R.intoFull_mem_covered hf hg p) hEdge
  obtain ⟨p', hp'⟩ :=
    R.intoFull_surjective_covered hf hg (⟨q, hq⟩)
  refine ⟨p', hp', ?_⟩
  exact (R.include_edges_iff hf hg leftEdges rightEdges
    letter p p').mpr (by
      rw [hp']
      exact hEdge)

end MatchedRestriction
end GluingEPPA.Steiner.ChainValuation
