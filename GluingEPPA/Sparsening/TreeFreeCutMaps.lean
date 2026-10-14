import GluingEPPA.Sparsening.TreePushoutCarrier

/-!
# Gluing side maps across an actual closed free cut

This is the minimal unary-language port of the verified universal carrier
map in shulda/lean_all_those_eppa_classes,
AllThoseEPPA/TreeLikeFreeCutGlueMap.lean.

The two proper sides are induced closed substructures of the actual test,
not hypothetical abstract decompositions. The glued map is defined on all
points, and agreements and injectivity are proved with exact overlap.
The relation/full-function-fibre homomorphism properties remain separate.
-/
namespace GluingEPPA.Sparsening.Tree
universe u v w z
variable {L : Nat → Type u} {P : Type v} {F : Type w} {W : Type z}
variable {R : RelStructure L P} {out : F → P → Set P}

/-- A point outside the left side of a free decomposition is in the right. -/
theorem freeCut_right_of_not_left (d : UnaryFreeDecomposition R out)
    {x : P} (hx : x ∉ d.left) : x ∈ d.right := by
  have hCover : x ∈ d.left ∪ d.right := by
    rw [d.cover]
    exact Set.mem_univ x
  exact hCover.resolve_left hx

/-- Prefer the left map on the overlap. No agreement is needed to define it. -/
noncomputable def glueFreeCutMap
    (d : UnaryFreeDecomposition R out)
    (l : d.left → W) (r : d.right → W) : P → W := by
  classical
  intro x
  exact if hx : x ∈ d.left then l ⟨x, hx⟩
    else r ⟨x, freeCut_right_of_not_left d hx⟩

theorem glueFreeCutMap_left
    (d : UnaryFreeDecomposition R out)
    (l : d.left → W) (r : d.right → W)
    (x : P) (hx : x ∈ d.left) :
    glueFreeCutMap d l r x = l ⟨x, hx⟩ := by
  classical
  simp [glueFreeCutMap, hx]

theorem glueFreeCutMap_right
    (d : UnaryFreeDecomposition R out)
    (l : d.left → W) (r : d.right → W)
    (hAgree :
      ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    (x : P) (hx : x ∈ d.right) :
    glueFreeCutMap d l r x = r ⟨x, hx⟩ := by
  classical
  by_cases hxL : x ∈ d.left
  · rw [glueFreeCutMap_left d l r x hxL]
    exact hAgree x hxL hx
  · simp [glueFreeCutMap, hxL]

theorem glueFreeCutMap_unique
    (d : UnaryFreeDecomposition R out)
    (l : d.left → W) (r : d.right → W)
    (hAgree :
      ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    (f : P → W)
    (hfL : ∀ (x : P) (hx : x ∈ d.left), f x = l ⟨x, hx⟩)
    (hfR : ∀ (x : P) (hx : x ∈ d.right), f x = r ⟨x, hx⟩) :
    f = glueFreeCutMap d l r := by
  funext x
  by_cases hx : x ∈ d.left
  · rw [hfL x hx, glueFreeCutMap_left d l r x hx]
  · have hR : x ∈ d.right := freeCut_right_of_not_left d hx
    rw [hfR x hR, glueFreeCutMap_right d l r hAgree x hR]

/-- Exact criterion for global injection after gluing: maps injective on
each side, with no unintended cross-side coincidences. -/
theorem glueFreeCutMap_injective
    (d : UnaryFreeDecomposition R out)
    (l : d.left → W) (r : d.right → W)
    (hLeft : Function.Injective l)
    (hRight : Function.Injective r)
    (hCross : ∀ (x : d.left) (y : d.right),
      l x = r y → x.1 = y.1) :
    Function.Injective (glueFreeCutMap d l r) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ d.left
  · by_cases hy : y ∈ d.left
    · have h : l ⟨x, hx⟩ = l ⟨y, hy⟩ := by
        simpa only [glueFreeCutMap_left d l r x hx,
          glueFreeCutMap_left d l r y hy] using hxy
      exact congrArg Subtype.val (hLeft h)
    · have hyR : y ∈ d.right := freeCut_right_of_not_left d hy
      have h : l ⟨x, hx⟩ = r ⟨y, hyR⟩ := by
        simpa [glueFreeCutMap, hx, hy] using hxy
      exact hCross ⟨x, hx⟩ ⟨y, hyR⟩ h
  · have hxR : x ∈ d.right := freeCut_right_of_not_left d hx
    by_cases hy : y ∈ d.left
    · have h : r ⟨x, hxR⟩ = l ⟨y, hy⟩ := by
        simpa [glueFreeCutMap, hx, hy] using hxy
      exact (hCross ⟨y, hy⟩ ⟨x, hxR⟩ h.symm).symm
    · have hyR : y ∈ d.right := freeCut_right_of_not_left d hy
      have h : r ⟨x, hxR⟩ = r ⟨y, hyR⟩ := by
        simpa only [glueFreeCutMap, dif_neg hx, dif_neg hy] using hxy
      exact congrArg Subtype.val (hRight h)

end GluingEPPA.Sparsening.Tree
