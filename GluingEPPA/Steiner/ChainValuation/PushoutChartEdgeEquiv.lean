import GluingEPPA.Steiner.ChainValuation.PushoutEquiv
import GluingEPPA.Steiner.ChainValuation.PushoutReachBridge

/-!
# Genuine edge reflection under an exact pushout chart equivalence

If two attaching diagrams are related by commuting equivalences of
their two sides and their whole interface, the induced equivalence
of literal set pushouts reflects as well as preserves every labelled
edge, provided each side chart reflects/preserves that label.

This isolates the edge-theoretic part of normalized smaller-mask
chain charts from their group and coset geometry. The statement
is about the *actual union-of-images relation* on the quotient;
no extra precompactness, commutativity, acyclicity or ambient group.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w u' v' w' e
variable {X : Type u} {Y : Type v} {Z : Type w}
variable {X' : Type u'} {Y' : Type v'} {Z' : Type w'}
variable {E : Type e}

/-- A commuting equivalence of full injective attachment diagrams
both preserves and reflects genuine edges of a selected colour.
In particular, the reflected edge may have its witness on the
other side of the glued interface. -/
theorem pushoutEquivOfEquivs_edge_iff
    (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (f' : Z' → X') (g' : Z' → Y')
    (hf' : Function.Injective f') (hg' : Function.Injective g')
    (a : X ≃ X') (b : Y ≃ Y') (c : Z ≃ Z')
    (hleft : ∀ z : Z, a (f z) = f' (c z))
    (hright : ∀ z : Z, b (g z) = g' (c z))
    (R : E → X → X → Prop) (S : E → Y → Y → Prop)
    (R' : E → X' → X' → Prop) (S' : E → Y' → Y' → Prop)
    (letter : E)
    (hR : ∀ x y, R letter x y ↔ R' letter (a x) (a y))
    (hS : ∀ x y, S letter x y ↔ S' letter (b x) (b y))
    (p q : SetPushout f g hf hg) :
    let F := pushoutEquivOfEquivs
      f g hf hg f' g' hf' hg' a b c hleft hright
    pushoutLabelRel R S f g hf hg letter p q ↔
      pushoutLabelRel R' S' f' g' hf' hg' letter (F p) (F q) := by
  let F := pushoutEquivOfEquivs
    f g hf hg f' g' hf' hg' a b c hleft hright
  change pushoutLabelRel R S f g hf hg letter p q ↔
    pushoutLabelRel R' S' f' g' hf' hg' letter (F p) (F q)
  constructor
  · intro h
    rcases h with ⟨x, y, hxy, hx, hy⟩ | ⟨x, y, hxy, hx, hy⟩
    · refine Or.inl ⟨a x, a y, (hR x y).mp hxy, ?_, ?_⟩
      · rw [← hx]
        rfl
      · rw [← hy]
        rfl
    · refine Or.inr ⟨b x, b y, (hS x y).mp hxy, ?_, ?_⟩
      · rw [← hx]
        rfl
      · rw [← hy]
        rfl
  · intro h
    rcases h with ⟨x', y', hxy, hx, hy⟩ | ⟨x', y', hxy, hx, hy⟩
    · obtain ⟨x, rfl⟩ := a.surjective x'
      obtain ⟨y, rfl⟩ := a.surjective y'
      have hpx : pushoutInl f g hf hg x = p := F.injective (by
        change pushoutInl f' g' hf' hg' (a x) = F p
        exact hx)
      have hqy : pushoutInl f g hf hg y = q := F.injective (by
        change pushoutInl f' g' hf' hg' (a y) = F q
        exact hy)
      exact Or.inl ⟨x, y, (hR x y).mpr hxy, hpx, hqy⟩
    · obtain ⟨x, rfl⟩ := b.surjective x'
      obtain ⟨y, rfl⟩ := b.surjective y'
      have hpx : pushoutInr f g hf hg x = p := F.injective (by
        change pushoutInr f' g' hf' hg' (b x) = F p
        exact hx)
      have hqy : pushoutInr f g hf hg y = q := F.injective (by
        change pushoutInr f' g' hf' hg' (b y) = F q
        exact hy)
      exact Or.inr ⟨x, y, (hS x y).mpr hxy, hpx, hqy⟩

end GluingEPPA.Steiner.ChainValuation
