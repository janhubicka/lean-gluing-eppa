import GluingEPPA.Steiner.ChainValuation.StateRelabel
import GluingEPPA.Steiner.ChainValuation.ChainAttach
import GluingEPPA.Steiner.ChainValuation.PushoutEquiv

/-!
# Equivariance of the literal separated-chain attachment step

The old chain, new Cayley block and attaching interface are transported by
equivalences commuting with both attachment maps. The resulting equivalence
of the actual injective pushouts reflects all genuine labelled edges.
The completed letter permutations are therefore conjugate automatically.

The separation assumptions are used only to define the two matching
structures. They are not new naturality hypotheses.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E E' : Type u} {K K' : Type v}
variable [Group K] [Group K']

namespace StateRelabel

/-- Exact geometric naturality of one separated-chain attachment.
Both directions of every genuine edge relation are preserved. -/
noncomputable def extension
    (p : E ≃ E')
    (A B : GroupBlock.{u,v} E)
    (A' B' : GroupBlock.{u,v} E')
    (C : ChainState E A) (C' : ChainState E' A')
    (FA : A.Carrier ≃* A'.Carrier)
    (FB : B.Carrier ≃* B'.Carrier)
    (R : StateRelabel p FA C C')
    (FK : K ≃* K')
    (h : A.Carrier) (h' : A'.Carrier)
    (hH : FA h = h')
    (left : K →* A.Carrier) (right : K →* B.Carrier)
    (left' : K' →* A'.Carrier) (right' : K' →* B'.Carrier)
    (hL : ∀ k, FA (left k) = left' (FK k))
    (hR : ∀ k, FB (right k) = right' (FK k))
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hleft' : Function.Injective left') (hright' : Function.Injective right')
    (hsep : Disjoint C.entry (exitSet A h left))
    (hsep' : Disjoint C'.entry (exitSet A' h' left'))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (hshared' : ∀ e, e ∈ A'.active → e ∈ B'.active →
      ∃ k : K', left' k = A'.edge e ∧ right' k = B'.edge e)
    (hActiveB : ∀ e, e ∈ B.active ↔ p e ∈ B'.active)
    (hEdgeB : ∀ e ∈ B.active, FB (B.edge e) = B'.edge (p e)) :
    StateRelabel p FB
      (ChainValuation.extend A B C h left right
        hleft hright hsep hshared)
      (ChainValuation.extend A' B' C' h' left' right'
        hleft' hright' hsep' hshared') := by
  let f : K → C.Space := attachInto C.lastEmbed h left
  let f' : K' → C'.Space := attachInto C'.lastEmbed h' left'
  have hf : Function.Injective f :=
    attachInto_injective C.lastEmbed C.lastInjective h left hleft
  have hf' : Function.Injective f' :=
    attachInto_injective C'.lastEmbed C'.lastInjective h' left' hleft'
  have hFL : ∀ k, R.space (f k) = f' (FK k) := by
    intro k
    change R.space (C.lastEmbed (h * left k)) =
      C'.lastEmbed (h' * left' (FK k))
    rw [R.lastEmbed, map_mul, hH, hL]
  let P : SetPushout f right hf hright ≃
      SetPushout f' right' hf' hright' :=
    pushoutEquivOfEquivs f right hf hright f' right' hf' hright'
      R.space FB.toEquiv FK.toEquiv hFL hR
  have hOld : ∀ x : C.Space,
      P (oldEmbed A B C h left right hleft hright x) =
      oldEmbed A' B' C' h' left' right' hleft' hright' (R.space x) := by
    intro x
    rfl
  have hNew : ∀ g : B.Carrier,
      P (newEmbed A B C h left right hleft hright g) =
      newEmbed A' B' C' h' left' right' hleft' hright' (FB g) := by
    intro g
    rfl
  have hentry : ∀ g : B.Carrier,
      g ∈ (ChainValuation.extend A B C h left right
        hleft hright hsep hshared).entry ↔
      FB g ∈ (ChainValuation.extend A' B' C' h' left' right'
        hleft' hright' hsep' hshared').entry := by
    intro g
    change (∃ k : K, right k = g) ↔ (∃ k' : K', right' k' = FB g)
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨FK k, (hR k).symm⟩
    · rintro ⟨k', hk'⟩
      obtain ⟨k, rfl⟩ := FK.surjective k'
      refine ⟨k, FB.injective ?_⟩
      exact (hR k).trans hk'
  refine
    { space := P
      lastEmbed := hNew
      entry := hentry
      matching := ?_ }
  intro e x y
  change extendedEdgeRel A B C h left right hleft hright e x y ↔
    extendedEdgeRel A' B' C' h' left' right' hleft' hright'
      (p e) (P x) (P y)
  constructor
  · intro hxy
    rcases hxy with ⟨a, b, hab, hax, hby⟩ | ⟨g, he, hgx, hgy⟩
    · apply Or.inl
      refine ⟨R.space a, R.space b, (R.matching e a b).mp hab, ?_, ?_⟩
      · exact (hOld a).symm.trans (congrArg P hax)
      · exact (hOld b).symm.trans (congrArg P hby)
    · apply Or.inr
      refine ⟨FB g, (hActiveB e).mp he, ?_, ?_⟩
      · exact (hNew g).symm.trans (congrArg P hgx)
      · calc
          newEmbed A' B' C' h' left' right' hleft' hright'
              (FB g * B'.edge (p e)) =
            newEmbed A' B' C' h' left' right' hleft' hright'
              (FB (g * B.edge e)) := by
              simp only [map_mul, hEdgeB e he]
          _ = P (newEmbed A B C h left right hleft hright
              (g * B.edge e)) := (hNew _).symm
          _ = P y := congrArg P hgy
  · intro hxy
    rcases hxy with ⟨a', b', hab, hax, hby⟩ | ⟨g', he, hgx, hgy⟩
    · obtain ⟨a, rfl⟩ := R.space.surjective a'
      obtain ⟨b, rfl⟩ := R.space.surjective b'
      apply Or.inl
      refine ⟨a, b, (R.matching e a b).mpr hab, ?_, ?_⟩
      · apply P.injective
        exact (hOld a).trans hax
      · apply P.injective
        exact (hOld b).trans hby
    · obtain ⟨g, rfl⟩ := FB.surjective g'
      have heB : e ∈ B.active := (hActiveB e).mpr he
      apply Or.inr
      refine ⟨g, heB, ?_, ?_⟩
      · apply P.injective
        exact (hNew g).trans hgx
      · apply P.injective
        calc
          P (newEmbed A B C h left right hleft hright
              (g * B.edge e)) =
            newEmbed A' B' C' h' left' right' hleft' hright'
              (FB (g * B.edge e)) := hNew _
          _ = newEmbed A' B' C' h' left' right' hleft' hright'
              (FB g * B'.edge (p e)) := by
              simp only [map_mul, hEdgeB e heB]
          _ = P y := hgy

end StateRelabel
end GluingEPPA.Steiner.ChainValuation
