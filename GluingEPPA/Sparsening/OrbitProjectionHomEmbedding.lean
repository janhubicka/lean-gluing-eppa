import GluingEPPA.Sparsening.TreeHomEmbedding
import GluingEPPA.Sparsening.OrbitIrreducible

/-!
# The actual canonical orbit-atlas projection is a homomorphism-embedding

This bridges the atlas-specific projection-on-irreducibles theorem to the
reusable unary relational homomorphism-embedding interface. It does not
postulate a globally injective projection. The empty closed test needs
special care: the canonical atlas always contains the empty chart, so
nullary relations are reflected even on an empty test.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v w
variable {L : Nat → Type u} {A : Type v} {F : Type w}
variable (R : RelStructure L A) (out : F → A → Set A)
    (root : Set A)
variable [Finite A]
open scoped Classical
noncomputable section
attribute [local instance] chartsFintype edgesFintype

theorem projection_rel_map
    {n : Nat} (r : L n) (xs : Fin n → Vertex R out root)
    (h : (relations R out root).rel r xs) :
    R.rel r
      (fun i => ChartAtlas.project (graph R out root)
        (support R out root) (xs i)) := by
  change (ChartAtlas.quotientStructure (graph R out root)
    (support R out root) R).rel r xs at h
  obtain ⟨s, chi, ys, hy, hys⟩ := h
  have heq : (fun i => (ys i).val) =
      (fun i => ChartAtlas.project (graph R out root)
        (support R out root) (xs i)) := by
    funext i
    exact congrArg
      (ChartAtlas.project (graph R out root) (support R out root))
      (hys i)
  rw [← heq]
  exact hy

/-- The empty chart witnesses every true old nullary relation in the
quotient, even when the distinguished root itself is empty. -/
theorem projection_nullary_iff
    (r : L 0) (xs : Fin 0 → Vertex R out root) :
    R.rel r (fun i => ChartAtlas.project (graph R out root)
      (support R out root) (xs i)) ↔
    (relations R out root).rel r xs := by
  constructor
  · intro hr
    change (ChartAtlas.quotientStructure (graph R out root)
      (support R out root) R).rel r xs
    refine ⟨emptyChart R out root, 0,
      (fun i : Fin 0 => Fin.elim0 i), ?_, ?_⟩
    · convert hr using 1
    · intro i
      exact Fin.elim0 i
  · exact projection_rel_map R out root r xs

/-- Actual orbit projection as a strong homomorphism-embedding. It
embeds every closed irreducible test with full unary-fibre equality,
including the empty test with nullary predicates. -/
def projectionHomEmbedding :
    Tree.UnaryHomEmbedding (relations R out root) (outputs R out root)
      R out where
  toFun := ChartAtlas.project (graph R out root) (support R out root)
  rel_map := by
    intro n r xs h
    exact projection_rel_map R out root r xs h
  unary_map := by
    intro f q z hz
    have hi : ChartAtlas.project (graph R out root)
        (support R out root) z ∈
      ChartAtlas.project (graph R out root) (support R out root) ''
        outputs R out root f q := ⟨z, hz, rfl⟩
    change ChartAtlas.project (graph R out root)
      (support R out root) z ∈
      ChartAtlas.project (graph R out root) (support R out root) ''
        ChartAtlas.liftOutput (graph R out root) (support R out root)
          out (closed R out root) f q at hi
    rw [ChartAtlas.liftOutput_projection
      (graph R out root) (support R out root)
      out (closed R out root) f q] at hi
    exact hi
  exact_on_irred := by
    intro S hclosed hirr
    by_cases hNonempty : Nonempty S
    · letI : Nonempty S := hNonempty
      have hEmb : ChartAtlas.ProjectionIsEmbeddingOn
          (graph R out root) (support R out root)
          R out (closed R out root) S :=
        projection_on_irreducible R out root S hclosed hirr
      refine ⟨{
        toFun := fun q => ChartAtlas.project (graph R out root)
          (support R out root) q.val
        injective := ?_
        rel_iff := ?_
        out_eq := ?_ }, ?_⟩
      · intro a b hab
        apply Subtype.ext
        exact hEmb.1 a.property b.property hab
      · intro n r xs
        change R.rel r (fun i => ChartAtlas.project
          (graph R out root) (support R out root) (xs i).val) ↔
          (relations R out root).rel r (fun i => (xs i).val)
        exact (hEmb.2.1 r (fun i => (xs i).val)
          (fun i => (xs i).property)).symm
      · intro f q
        apply Set.ext
        intro y
        constructor
        · rintro ⟨z, hz, rfl⟩
          have hi : ChartAtlas.project (graph R out root)
              (support R out root) z.val ∈
              ChartAtlas.project (graph R out root)
                (support R out root) '' outputs R out root f q.val :=
            ⟨z.val, hz, rfl⟩
          change ChartAtlas.project (graph R out root)
              (support R out root) z.val ∈
            ChartAtlas.project (graph R out root) (support R out root) ''
              ChartAtlas.liftOutput (graph R out root) (support R out root)
                out (closed R out root) f q.val at hi
          rw [ChartAtlas.liftOutput_projection
            (graph R out root) (support R out root)
            out (closed R out root) f q.val] at hi
          exact hi
        · intro hy
          have hi : y ∈ ChartAtlas.project (graph R out root)
              (support R out root) '' outputs R out root f q.val := by
            change y ∈ ChartAtlas.project (graph R out root)
              (support R out root) ''
              ChartAtlas.liftOutput (graph R out root) (support R out root)
                out (closed R out root) f q.val
            rw [ChartAtlas.liftOutput_projection
              (graph R out root) (support R out root)
              out (closed R out root) f q.val]
            exact hy
          obtain ⟨z, hz, heq⟩ := hi
          have hzS : z ∈ S := hclosed f q.val z q.property hz
          exact ⟨⟨z, hzS⟩, hz, heq⟩
      · intro z
        rfl
    · refine ⟨{
        toFun := fun q => ChartAtlas.project (graph R out root)
          (support R out root) q.val
        injective := ?_
        rel_iff := ?_
        out_eq := ?_ }, ?_⟩
      · intro a b _
        exact (hNonempty ⟨a⟩).elim
      · intro n r xs
        by_cases hz : n = 0
        · subst n
          change R.rel r (fun i : Fin 0 =>
            ChartAtlas.project (graph R out root)
              (support R out root) (xs i).val) ↔
            (relations R out root).rel r (fun i => (xs i).val)
          exact projection_nullary_iff R out root r
            (fun i => (xs i).val)
        · have hi : Fin n := ⟨0, Nat.pos_of_ne_zero hz⟩
          exact (hNonempty ⟨xs hi⟩).elim
      · intro f a
        exact (hNonempty ⟨a⟩).elim
      · intro z
        exact (hNonempty ⟨z⟩).elim

end
end GluingEPPA.Sparsening.OrbitAtlas
