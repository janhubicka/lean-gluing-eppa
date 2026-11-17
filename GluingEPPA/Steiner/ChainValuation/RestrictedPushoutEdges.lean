import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutExact

/-!
# Genuine labelled edges in the exact pushout of restricted pieces

The matched restriction API proves that the selected pieces glue
injectively into the full pushout. We now show that the genuine
labelled-edge relation on the selected quotient is precisely the
induced genuine-edge relation of the entire quotient.

No letter can acquire a spurious neighbour merely because the
selected pieces were attached, and no real edge *between two
selected vertices* is lost. This is edge reflection, not just
forward preservation. To restrict completed matching actions one
must additionally show that the union is closed under all M-edges.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w e
variable {X : Type u} {Y : Type v} {Z : Type w} {E : Type e}
variable {f : Z → X} {g : Z → Y}

namespace MatchedRestriction

variable (R : MatchedRestriction f g)

/-- The genuine union-of-images edge relation in a literal
injective set pushout. This is the same edge relation used by the
chain-state matching construction. -/
def quotientEdges
    {X' : Type u} {Y' : Type v} {Z' : Type w}
    (R1 : E → X' → X' → Prop) (S1 : E → Y' → Y' → Prop)
    (f1 : Z' → X') (g1 : Z' → Y')
    (hf1 : Function.Injective f1) (hg1 : Function.Injective g1)
    (letter : E) :
    SetPushout f1 g1 hf1 hg1 → SetPushout f1 g1 hf1 hg1 → Prop :=
  fun p q =>
    (∃ x y : X', R1 letter x y ∧
      pushoutInl f1 g1 hf1 hg1 x = p ∧
      pushoutInl f1 g1 hf1 hg1 y = q) ∨
    (∃ x y : Y', S1 letter x y ∧
      pushoutInr f1 g1 hf1 hg1 x = p ∧
      pushoutInr f1 g1 hf1 hg1 y = q)

/-- A full-side left vertex belongs to the selected quotient image
if and only if it itself lies in the selected left subset. This
uses agreement of the interface preimages, not merely the fact
that the inclusion is injective. -/
theorem inl_mem_covered_iff
    (hf : Function.Injective f) (hg : Function.Injective g)
    (x : X) :
    pushoutInl f g hf hg x ∈ R.Covered hf hg ↔ x ∈ R.left := by
  constructor
  · intro h
    change (∃ x' : R.Left, pushoutInl f g hf hg x'.val =
        pushoutInl f g hf hg x) ∨
      (∃ y' : R.Right, pushoutInr f g hf hg y'.val =
        pushoutInl f g hf hg x) at h
    rcases h with ⟨x', hx⟩ | ⟨y', hy⟩
    · have hx' := (pushoutInl_injective f g hf hg) hx
      simpa only [hx'] using x'.property
    · obtain ⟨z, hzX, hzY⟩ :=
        (pushoutInl_eq_inr_iff f g hf hg x y'.val).mp hy.symm
      have hy' : g z ∈ R.right := by
        rw [hzY]
        exact y'.property
      rw [← hzX]
      exact (R.agree z).mpr hy'
  · intro hx
    exact Or.inl ⟨⟨x, hx⟩, rfl⟩

/-- Symmetric membership test for the other side of the gluing. -/
theorem inr_mem_covered_iff
    (hf : Function.Injective f) (hg : Function.Injective g)
    (y : Y) :
    pushoutInr f g hf hg y ∈ R.Covered hf hg ↔ y ∈ R.right := by
  constructor
  · intro h
    change (∃ x' : R.Left, pushoutInl f g hf hg x'.val =
        pushoutInr f g hf hg y) ∨
      (∃ y' : R.Right, pushoutInr f g hf hg y'.val =
        pushoutInr f g hf hg y) at h
    rcases h with ⟨x', hx⟩ | ⟨y', hy⟩
    · obtain ⟨z, hzX, hzY⟩ :=
        (pushoutInl_eq_inr_iff f g hf hg x'.val y).mp hx
      have hx' : f z ∈ R.left := by
        rw [hzX]
        exact x'.property
      rw [← hzY]
      exact (R.agree z).mp hx'
    · have hy' := (pushoutInr_injective f g hf hg) hy
      simpa only [hy'] using y'.property
  · intro hy
    exact Or.inr ⟨⟨y, hy⟩, rfl⟩

/-- The genuine edges in the restricted quotient are **exactly**
the genuine full-quotient edges whose two endpoints belong to
the selected image. The reverse direction relies crucially on
the injectivity of the exact restriction map. -/
theorem include_edges_iff
    (hf : Function.Injective f) (hg : Function.Injective g)
    (leftEdges : E → X → X → Prop)
    (rightEdges : E → Y → Y → Prop)
    (letter : E)
    (p q : R.Space hf hg) :
    quotientEdges
      (fun e (x y : R.Left) => leftEdges e x.val y.val)
      (fun e (x y : R.Right) => rightEdges e x.val y.val)
      R.leftAttach R.rightAttach
      (R.leftAttach_injective hf) (R.rightAttach_injective hg)
      letter p q ↔
    quotientEdges leftEdges rightEdges f g hf hg letter
      (R.intoFull hf hg p) (R.intoFull hf hg q) := by
  constructor
  · intro h
    rcases h with ⟨x, y, hxy, hp, hq⟩ | ⟨x, y, hxy, hp, hq⟩
    · refine Or.inl ⟨x.val, y.val, hxy, ?_, ?_⟩
      · exact (congrArg (R.intoFull hf hg) hp)
      · exact (congrArg (R.intoFull hf hg) hq)
    · refine Or.inr ⟨x.val, y.val, hxy, ?_, ?_⟩
      · exact (congrArg (R.intoFull hf hg) hp)
      · exact (congrArg (R.intoFull hf hg) hq)
  · intro h
    rcases h with ⟨x, y, hxy, hp, hq⟩ | ⟨x, y, hxy, hp, hq⟩
    · have hx : x ∈ R.left :=
        (R.inl_mem_covered_iff hf hg x).mp (by
          rw [hp]
          exact R.intoFull_mem_covered hf hg p)
      have hy : y ∈ R.left :=
        (R.inl_mem_covered_iff hf hg y).mp (by
          rw [hq]
          exact R.intoFull_mem_covered hf hg q)
      let x0 : R.Left := ⟨x, hx⟩
      let y0 : R.Left := ⟨y, hy⟩
      have hp0 : pushoutInl R.leftAttach R.rightAttach
          (R.leftAttach_injective hf) (R.rightAttach_injective hg) x0 =
          p := by
        apply R.intoFull_injective hf hg
        change pushoutInl f g hf hg x = R.intoFull hf hg p
        exact hp
      have hq0 : pushoutInl R.leftAttach R.rightAttach
          (R.leftAttach_injective hf) (R.rightAttach_injective hg) y0 =
          q := by
        apply R.intoFull_injective hf hg
        change pushoutInl f g hf hg y = R.intoFull hf hg q
        exact hq
      exact Or.inl ⟨x0, y0, hxy, hp0, hq0⟩
    · have hx : x ∈ R.right :=
        (R.inr_mem_covered_iff hf hg x).mp (by
          rw [hp]
          exact R.intoFull_mem_covered hf hg p)
      have hy : y ∈ R.right :=
        (R.inr_mem_covered_iff hf hg y).mp (by
          rw [hq]
          exact R.intoFull_mem_covered hf hg q)
      let x0 : R.Right := ⟨x, hx⟩
      let y0 : R.Right := ⟨y, hy⟩
      have hp0 : pushoutInr R.leftAttach R.rightAttach
          (R.leftAttach_injective hf) (R.rightAttach_injective hg) x0 =
          p := by
        apply R.intoFull_injective hf hg
        change pushoutInr f g hf hg x = R.intoFull hf hg p
        exact hp
      have hq0 : pushoutInr R.leftAttach R.rightAttach
          (R.leftAttach_injective hf) (R.rightAttach_injective hg) y0 =
          q := by
        apply R.intoFull_injective hf hg
        change pushoutInr f g hf hg y = R.intoFull hf hg q
        exact hq
      exact Or.inr ⟨x0, y0, hxy, hp0, hq0⟩

end MatchedRestriction
end GluingEPPA.Steiner.ChainValuation
