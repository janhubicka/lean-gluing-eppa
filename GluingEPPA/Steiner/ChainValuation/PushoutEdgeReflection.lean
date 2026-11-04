import GluingEPPA.Steiner.ChainValuation.PushoutEquiv
import GluingEPPA.Steiner.ChainValuation.MatchingEquiv

/-!
# Labelled-edge reflection of an exact normalized pushout chart

Compatible bijections of old/new blocks and their attaching interface
already induce an equivalence of literal injective pushouts. We show
that, provided the component block charts preserve AND reflect their
genuine named edges, this pushout equivalence does the same.

This is not merely edge preservation or surjectivity, which fail to
transport fixed points in completed matching actions. The remaining
global normalized-chain problem is to instantiate these hypotheses
with the actual successive restricted Cayley coset charts.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w u' v' w' e
variable {X : Type u} {Y : Type v} {Z : Type w}
variable {X' : Type u'} {Y' : Type v'} {Z' : Type w'}
variable {E : Type e}

/-- The actual quotient edge is the image of a genuine edge of
one of the two pieces, with no spurious quotient edges. -/
def pushoutUnionEdges
    (R : E → X → X → Prop) (S : E → Y → Y → Prop)
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (letter : E) :
    SetPushout f g hf hg → SetPushout f g hf hg → Prop :=
  fun p q =>
    (∃ x y : X, R letter x y ∧
        pushoutInl f g hf hg x = p ∧
        pushoutInl f g hf hg y = q) ∨
    (∃ x y : Y, S letter x y ∧
        pushoutInr f g hf hg x = p ∧
        pushoutInr f g hf hg y = q)

/-- An exact pushout equivalence reflects *every* genuine
labelled edge when the two local charts reflect their edges.
No global N-acyclicity assumption is used. -/
theorem pushoutEquiv_edges_iff
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X ≃ X') (b : Y ≃ Y') (c : Z ≃ Z')
    (hleft : ∀ z, a (f z) = f' (c z))
    (hright : ∀ z, b (g z) = g' (c z))
    (R : E → X → X → Prop) (S : E → Y → Y → Prop)
    (R' : E → X' → X' → Prop) (S' : E → Y' → Y' → Prop)
    (hR : ∀ letter x y, R letter x y ↔ R' letter (a x) (a y))
    (hS : ∀ letter x y, S letter x y ↔ S' letter (b x) (b y))
    (letter : E)
    (p q : SetPushout f g hf hg) :
    pushoutUnionEdges R S f g hf hg letter p q ↔
    pushoutUnionEdges R' S' f' g' hf' hg' letter
      (pushoutEquiv f g hf hg f' g' hf' hg'
        a b c hleft hright p)
      (pushoutEquiv f g hf hg f' g' hf' hg'
        a b c hleft hright q) := by
  let F := pushoutEquiv f g hf hg f' g' hf' hg'
    a b c hleft hright
  have hInl (x : X) : F (pushoutInl f g hf hg x) =
      pushoutInl f' g' hf' hg' (a x) := by
    rfl
  have hInr (y : Y) : F (pushoutInr f g hf hg y) =
      pushoutInr f' g' hf' hg' (b y) := by
    rfl
  change pushoutUnionEdges R S f g hf hg letter p q ↔
    pushoutUnionEdges R' S' f' g' hf' hg' letter (F p) (F q)
  constructor
  · intro h
    rcases h with ⟨x, y, hxy, hp, hq⟩ | ⟨x, y, hxy, hp, hq⟩
    · refine Or.inl ⟨a x, a y, (hR letter x y).mp hxy, ?_, ?_⟩
      · exact (hInl x).symm.trans (congrArg F hp)
      · exact (hInl y).symm.trans (congrArg F hq)
    · refine Or.inr ⟨b x, b y, (hS letter x y).mp hxy, ?_, ?_⟩
      · exact (hInr x).symm.trans (congrArg F hp)
      · exact (hInr y).symm.trans (congrArg F hq)
  · intro h
    rcases h with ⟨x, y, hxy, hp, hq⟩ | ⟨x, y, hxy, hp, hq⟩
    · have hp' : pushoutInl f g hf hg (a.symm x) = p := by
        apply F.injective
        calc
          F (pushoutInl f g hf hg (a.symm x)) =
              pushoutInl f' g' hf' hg' x := by
                simpa using hInl (a.symm x)
          _ = F p := hp
      have hq' : pushoutInl f g hf hg (a.symm y) = q := by
        apply F.injective
        calc
          F (pushoutInl f g hf hg (a.symm y)) =
              pushoutInl f' g' hf' hg' y := by
                simpa using hInl (a.symm y)
          _ = F q := hq
      refine Or.inl ⟨a.symm x, a.symm y, ?_, hp', hq'⟩
      apply (hR letter (a.symm x) (a.symm y)).mpr
      simpa using hxy
    · have hp' : pushoutInr f g hf hg (b.symm x) = p := by
        apply F.injective
        calc
          F (pushoutInr f g hf hg (b.symm x)) =
              pushoutInr f' g' hf' hg' x := by
                simpa using hInr (b.symm x)
          _ = F p := hp
      have hq' : pushoutInr f g hf hg (b.symm y) = q := by
        apply F.injective
        calc
          F (pushoutInr f g hf hg (b.symm y)) =
              pushoutInr f' g' hf' hg' y := by
                simpa using hInr (b.symm y)
          _ = F q := hq
      refine Or.inr ⟨b.symm x, b.symm y, ?_, hp', hq'⟩
      apply (hS letter (b.symm x) (b.symm y)).mpr
      simpa using hxy

end GluingEPPA.Steiner.ChainValuation
