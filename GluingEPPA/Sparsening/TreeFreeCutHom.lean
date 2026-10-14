import GluingEPPA.Sparsening.TreeFreeCutMaps

/-!
# Homomorphisms assembled across a genuine unary free decomposition

The universal side map from the checked AllThoseEPPA carrier interface is
now proved to preserve ALL relation tuples and set-valued unary outputs,
provided the two side maps agree over their exact overlap. No injectivity
is silently assumed; genuine homomorphism-embeddings require an additional
irreducibility-side argument in the local-tree induction.
-/
namespace GluingEPPA.Sparsening.Tree
universe u v w z
variable {L : Nat → Type u} {P : Type v} {F : Type w} {W : Type z}
variable {R : RelStructure L P} {out : F → P → Set P}

/-- Gluing relation-preserving side maps preserves every relation tuple,
including nullary symbols and tuples with repeated coordinates. -/
theorem glueFreeCutMap_rel
    (d : UnaryFreeDecomposition R out)
    (S : RelStructure L W)
    (l : d.left → W) (r : d.right → W)
    (hAgree : ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    (hLeft : ∀ {n} (t : L n) (xs : Fin n → d.left),
      R.rel t (fun i => (xs i).val) → S.rel t (fun i => l (xs i)))
    (hRight : ∀ {n} (t : L n) (xs : Fin n → d.right),
      R.rel t (fun i => (xs i).val) → S.rel t (fun i => r (xs i)))
    {n : Nat} (t : L n) (xs : Fin n → P) (ht : R.rel t xs) :
    S.rel t (fun i => glueFreeCutMap d l r (xs i)) := by
  rcases d.rel_local t xs ht with hxsL | hxsR
  · let ys : Fin n → d.left := fun i => ⟨xs i, hxsL i⟩
    have hsrc : R.rel t (fun i => (ys i).val) := by
      simpa only [ys] using ht
    have hmap : (fun i => glueFreeCutMap d l r (xs i)) =
        (fun i => l (ys i)) := by
      funext i
      exact glueFreeCutMap_left d l r (xs i) (hxsL i)
    rw [hmap]
    exact hLeft t ys hsrc
  · let ys : Fin n → d.right := fun i => ⟨xs i, hxsR i⟩
    have hsrc : R.rel t (fun i => (ys i).val) := by
      simpa only [ys] using ht
    have hmap : (fun i => glueFreeCutMap d l r (xs i)) =
        (fun i => r (ys i)) := by
      funext i
      exact glueFreeCutMap_right d l r hAgree (xs i) (hxsR i)
    rw [hmap]
    exact hRight t ys hsrc

/-- Preservation of unary functions means ALL output elements, not merely
a selected output edge, map into the corresponding target fibre. -/
theorem glueFreeCutMap_unary_mem
    (d : UnaryFreeDecomposition R out)
    (target : F → W → Set W)
    (l : d.left → W) (r : d.right → W)
    (hAgree : ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    (hLeft : ∀ f (x y : d.left),
      y.val ∈ out f x.val → l y ∈ target f (l x))
    (hRight : ∀ f (x y : d.right),
      y.val ∈ out f x.val → r y ∈ target f (r x))
    (f : F) (x y : P) (hy : y ∈ out f x) :
    glueFreeCutMap d l r y ∈ target f (glueFreeCutMap d l r x) := by
  classical
  by_cases hx : x ∈ d.left
  · have hz : y ∈ d.left := d.left_closed f x y hx hy
    have hh := hLeft f ⟨x, hx⟩ ⟨y, hz⟩ hy
    simpa only [glueFreeCutMap_left d l r x hx,
      glueFreeCutMap_left d l r y hz] using hh
  · have hxR : x ∈ d.right := freeCut_right_of_not_left d hx
    have hzR : y ∈ d.right := d.right_closed f x y hxR hy
    have hh := hRight f ⟨x, hxR⟩ ⟨y, hzR⟩ hy
    simpa only [glueFreeCutMap_right d l r hAgree x hxR,
      glueFreeCutMap_right d l r hAgree y hzR] using hh

/-- The complete image of every unary fibre maps into the target fibre.
This is exactly the function clause of the AllThoseEPPA Homomorphism API. -/
theorem glueFreeCutMap_unary_image
    (d : UnaryFreeDecomposition R out)
    (target : F → W → Set W)
    (l : d.left → W) (r : d.right → W)
    (hAgree : ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    (hLeft : ∀ f (x y : d.left),
      y.val ∈ out f x.val → l y ∈ target f (l x))
    (hRight : ∀ f (x y : d.right),
      y.val ∈ out f x.val → r y ∈ target f (r x))
    (f : F) (x : P) :
    glueFreeCutMap d l r '' out f x ⊆
      target f (glueFreeCutMap d l r x) := by
  rintro y ⟨z, hz, rfl⟩
  exact glueFreeCutMap_unary_mem d target l r
    hAgree hLeft hRight f x z hz

end GluingEPPA.Sparsening.Tree
