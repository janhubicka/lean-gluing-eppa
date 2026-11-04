import GluingEPPA.Steiner.ChainValuation.PushoutFunctor

/-!
# Bijective chart transport through exact injective pushouts

Normalized proper-alphabet chain components are built by translating
individual restricted Cayley cosets and gluing on their exact interface
cosets. Each local translation is a bijection. This lemma lifts a
commuting triple of such bijections to an equivalence of the literal
set pushouts, not merely a surjection.

This is the general set-level ingredient for the pending normalized
smaller-chain chart theorem. It does not assert letter equivariance:
that requires the genuine-edge reflection calculation of the particular
Cayley blocks.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w u' v' w'
variable {X : Type u} {Y : Type v} {Z : Type w}
variable {X' : Type u'} {Y' : Type v'} {Z' : Type w'}

/-- Commuting bijective charts of both blocks and their attaching
interface induce a genuine equivalence of the exact pushouts. -/
noncomputable def pushoutEquiv
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X ≃ X') (b : Y ≃ Y') (c : Z ≃ Z')
    (hleft : ∀ z, a (f z) = f' (c z))
    (hright : ∀ z, b (g z) = g' (c z)) :
    SetPushout f g hf hg ≃ SetPushout f' g' hf' hg' := by
  have hleft_inv : ∀ z', a.symm (f' z') = f (c.symm z') := by
    intro z'
    apply a.injective
    simpa using (hleft (c.symm z')).symm
  have hright_inv : ∀ z', b.symm (g' z') = g (c.symm z') := by
    intro z'
    apply b.injective
    simpa using (hright (c.symm z')).symm
  exact
    { toFun := pushoutMap f g hf hg f' g' hf' hg'
        a b c hleft hright
      invFun := pushoutMap f' g' hf' hg' f g hf hg
        a.symm b.symm c.symm hleft_inv hright_inv
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro t
        cases t with
        | inl x =>
            change pushoutInl f g hf hg (a.symm (a x)) =
              pushoutInl f g hf hg x
            simp
        | inr y =>
            change pushoutInr f g hf hg (b.symm (b y)) =
              pushoutInr f g hf hg y
            simp
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro t
        cases t with
        | inl x =>
            change pushoutInl f' g' hf' hg' (a (a.symm x)) =
              pushoutInl f' g' hf' hg' x
            simp
        | inr y =>
            change pushoutInr f' g' hf' hg' (b (b.symm y)) =
              pushoutInr f' g' hf' hg' y
            simp }

/-- The associated literal pushout map is bijective, so none of the
normalized chart identifications are lost in the quotient. -/
theorem pushoutMap_bijective_of_equiv
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X ≃ X') (b : Y ≃ Y') (c : Z ≃ Z')
    (hleft : ∀ z, a (f z) = f' (c z))
    (hright : ∀ z, b (g z) = g' (c z)) :
    Function.Bijective (pushoutMap f g hf hg f' g' hf' hg'
      a b c hleft hright) :=
  (pushoutEquiv f g hf hg f' g' hf' hg' a b c hleft hright).bijective

end GluingEPPA.Steiner.ChainValuation
