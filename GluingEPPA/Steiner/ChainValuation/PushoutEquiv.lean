import GluingEPPA.Steiner.ChainValuation.PushoutFunctor

/-!
# Exact pushouts respect equivalences of attaching diagrams

Given bijections of the two pieces and their common attaching
parameter space, commuting with both attachment maps, the induced
map of the literal injective pushouts is a bijection.

The previous functoriality theorem proved only surjectivity when
the two piece maps were surjective. The missing injectivity uses
the exact quotient relation, plus surjectivity of the interface
bijection; no additional geometric hypothesis is allowed.

This is the abstract glueing step for assembling normalized
smaller-mask Cayley charts into a full restricted-chain chart.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w u' v' w'
variable {X : Type u} {Y : Type v} {Z : Type w}
variable {X' : Type u'} {Y' : Type v'} {Z' : Type w'}

/-- Bijections of both pieces and of the interface reflect equality
in the exact literal pushout as long as the attaching squares commute. -/
theorem pushoutMap_injective_of_equivs
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X ≃ X') (b : Y ≃ Y') (c : Z ≃ Z')
    (hleft : ∀ z : Z, a (f z) = f' (c z))
    (hright : ∀ z : Z, b (g z) = g' (c z)) :
    Function.Injective
      (pushoutMap f g hf hg f' g' hf' hg'
        a b c hleft hright) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro s t h
  have hFull :
      pushoutRel f' g'
        (pushoutSumMap a b s) (pushoutSumMap a b t) :=
    Quotient.exact h
  apply Quotient.sound
  cases s with
  | inl x =>
      cases t with
      | inl y =>
          change a x = a y at hFull
          change x = y
          exact a.injective hFull
      | inr y =>
          change ∃ z' : Z', f' z' = a x ∧ g' z' = b y at hFull
          obtain ⟨z', hzX, hzY⟩ := hFull
          obtain ⟨z, rfl⟩ := c.surjective z'
          change ∃ z : Z, f z = x ∧ g z = y
          refine ⟨z, ?_, ?_⟩
          · exact a.injective ((hleft z).trans hzX)
          · exact b.injective ((hright z).trans hzY)
  | inr y =>
      cases t with
      | inl x =>
          change ∃ z' : Z', g' z' = b y ∧ f' z' = a x at hFull
          obtain ⟨z', hzY, hzX⟩ := hFull
          obtain ⟨z, rfl⟩ := c.surjective z'
          change ∃ z : Z, g z = y ∧ f z = x
          refine ⟨z, ?_, ?_⟩
          · exact b.injective ((hright z).trans hzY)
          · exact a.injective ((hleft z).trans hzX)
      | inr y' =>
          change b y = b y' at hFull
          change y = y'
          exact b.injective hFull

/-- The exact set-pushout of an attachment diagram is invariant
under bijective commuting changes of coordinates on both blocks
and the full attaching interface. -/
noncomputable def pushoutEquivOfEquivs
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X ≃ X') (b : Y ≃ Y') (c : Z ≃ Z')
    (hleft : ∀ z : Z, a (f z) = f' (c z))
    (hright : ∀ z : Z, b (g z) = g' (c z)) :
    SetPushout f g hf hg ≃ SetPushout f' g' hf' hg' :=
  Equiv.ofBijective
    (pushoutMap f g hf hg f' g' hf' hg'
      a b c hleft hright)
    ⟨pushoutMap_injective_of_equivs
        f g hf hg f' g' hf' hg' a b c hleft hright,
      pushoutMap_surjective
        f g hf hg f' g' hf' hg'
        a b c hleft hright a.surjective b.surjective⟩

end GluingEPPA.Steiner.ChainValuation
