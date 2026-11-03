import GluingEPPA.Steiner.ChainValuation.Pushout

/-!
# Functoriality of exact chain attachments

When the old and new pieces of a smaller-chain test map to the corresponding
pieces of a larger chain and the maps agree on the common attachment, they
induce a map of the exact injective pushouts.

Crucially, the maps on the two blocks do NOT have to be injective. If both
are surjective, the induced map on pushouts is surjective. This is the
geometric API needed for constructing equivariant covers by smaller tests
without the stronger requirement of an isomorphism.

This file does not assert letter equivariance of arbitrary pushout maps.
That remains to be checked from the labelled matching relations of the
particular chain construction.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w u' v' w'
variable {X : Type u} {Y : Type v} {Z : Type w}
variable {X' : Type u'} {Y' : Type v'} {Z' : Type w'}

def pushoutSumMap (a : X → X') (b : Y → Y') :
    Sum X Y → Sum X' Y'
  | .inl x => .inl (a x)
  | .inr y => .inr (b y)

/-- The induced map on exact injective set pushouts; the block maps themselves
may identify points, as long as they commute with the attaching maps. -/
def pushoutMap
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X → X') (b : Y → Y') (c : Z → Z')
    (hleft : ∀ z, a (f z) = f' (c z))
    (hright : ∀ z, b (g z) = g' (c z)) :
    SetPushout f g hf hg → SetPushout f' g' hf' hg' := by
  refine Quotient.lift
    (fun t : Sum X Y =>
      Quotient.mk (pushoutSetoid f' g' hf' hg')
        (pushoutSumMap a b t)) ?_
  intro t s h
  cases t with
  | inl x =>
    cases s with
    | inl y =>
      change x = y at h
      cases h
      rfl
    | inr y =>
      obtain ⟨z, hzX, hzY⟩ := h
      apply Quotient.sound
      exact ⟨c z,
        (hleft z).symm.trans (congrArg a hzX),
        (hright z).symm.trans (congrArg b hzY)⟩
  | inr x =>
    cases s with
    | inl y =>
      obtain ⟨z, hzX, hzY⟩ := h
      apply Quotient.sound
      exact ⟨c z,
        (hright z).symm.trans (congrArg b hzX),
        (hleft z).symm.trans (congrArg a hzY)⟩
    | inr y =>
      change x = y at h
      cases h
      rfl

@[simp] theorem pushoutMap_inl
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X → X') (b : Y → Y') (c : Z → Z')
    (hleft : ∀ z, a (f z) = f' (c z))
    (hright : ∀ z, b (g z) = g' (c z))
    (x : X) :
    pushoutMap f g hf hg f' g' hf' hg'
      a b c hleft hright (pushoutInl f g hf hg x) =
        pushoutInl f' g' hf' hg' (a x) := rfl

@[simp] theorem pushoutMap_inr
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X → X') (b : Y → Y') (c : Z → Z')
    (hleft : ∀ z, a (f z) = f' (c z))
    (hright : ∀ z, b (g z) = g' (c z))
    (y : Y) :
    pushoutMap f g hf hg f' g' hf' hg'
      a b c hleft hright (pushoutInr f g hf hg y) =
        pushoutInr f' g' hf' hg' (b y) := rfl

/-- Surjective covers of both block spaces induce a surjective cover of
their pushout, with no injectivity hypothesis on either block cover. -/
theorem pushoutMap_surjective
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X → X') (b : Y → Y') (c : Z → Z')
    (hleft : ∀ z, a (f z) = f' (c z))
    (hright : ∀ z, b (g z) = g' (c z))
    (ha : Function.Surjective a) (hb : Function.Surjective b) :
    Function.Surjective
      (pushoutMap f g hf hg f' g' hf' hg'
        a b c hleft hright) := by
  intro t
  refine Quotient.inductionOn t ?_
  intro z
  cases z with
  | inl x =>
    obtain ⟨x0, hx⟩ := ha x
    refine ⟨pushoutInl f g hf hg x0, ?_⟩
    simpa [pushoutMap_inl, pushoutInl, hx]
  | inr y =>
    obtain ⟨y0, hy⟩ := hb y
    refine ⟨pushoutInr f g hf hg y0, ?_⟩
    simpa [pushoutMap_inr, pushoutInr, hy]

end GluingEPPA.Steiner.ChainValuation
