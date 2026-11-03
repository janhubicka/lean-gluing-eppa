import GluingEPPA.Steiner.ChainValuation.ChainEndpoint

/-!
# Persistent first-endpoint separation across arbitrarily many chain blocks

Once an initial vertex leaves the last block, exact injective pushout
attachments cannot identify it with a point of any later block. This
packages the induction needed for the final unrolled-cycle endpoint
argument, without assuming any group-theoretic acyclicity theorem.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- The initial distinguished point has no representative in the last block. -/
structure TailAnchor (A : GroupBlock E) (C : ChainState E A) where
  point : C.Space
  outside_last : ∀ a : A.Carrier, C.lastEmbed a ≠ point

/-- After the first attachment, a starting point outside its exit coset is
not represented in the newly attached block. -/
noncomputable def TailAnchor.start
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier)
    (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (x : A.Carrier) (hx : x ∉ exitSet A h left) :
    TailAnchor B (extend A B C h left right hleft hright hsep hshared) where
  point := oldEmbed A B C h left right hleft hright (C.lastEmbed x)
  outside_last := by
    intro y
    change newEmbed A B C h left right hleft hright y ≠
      oldEmbed A B C h left right hleft hright (C.lastEmbed x)
    exact (outside_exit_not_new A B C h left right hleft hright x hx y).symm

/-- The distinguished point remains excluded from the last block after
every further exact attachment. -/
noncomputable def TailAnchor.extend
    (A B : GroupBlock E) (C : ChainState E A)
    (Z : TailAnchor A C)
    (h : A.Carrier)
    (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e) :
    TailAnchor B (ChainValuation.extend A B C h left right hleft hright hsep hshared) where
  point := oldEmbed A B C h left right hleft hright Z.point
  outside_last := by
    intro y
    change newEmbed A B C h left right hleft hright y ≠
      oldEmbed A B C h left right hleft hright Z.point
    exact (outside_last_not_new A B C h left right hleft hright
      Z.point Z.outside_last y).symm

end GluingEPPA.Steiner.ChainValuation
