import GluingEPPA.Sparsening.OrbitRootedDichotomy

/-!
# The canonical atlas chart case embeds exactly into the old root

On a single lifted chart the projection reflects every old relation,
including nullary relations. On a CLOSED test it also preserves equality
of entire unary fibres. An old automorphism witnessing that the chart is
contained in an image of the distinguished root then yields the explicit
exact embedding q ↦ h⁻¹(project q) into the root.

This is the one-block target branch of the proposed sparsening induction.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v w
variable {L : Nat → Type u} {F : Type w} {B : Type v}
open scoped Classical
noncomputable section
variable [Finite B]
attribute [local instance] chartsFintype edgesFintype

/-- Exact projection on ANY closed subtest contained in one lifted chart,
not merely on irreducible tests. -/
noncomputable def chartTestExact
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (s : Chart R out root) (chi : Edges R out root → ZMod 2)
    (S : Set (Vertex R out root))
    (hS : UnaryClosed (outputs R out root) (fun q => q ∈ S))
    (hchart : ∀ q : S, ∃ hx : support R out root
      (testProjection R out root S q) s,
      ChartAtlas.copy (graph R out root) (support R out root)
        s chi (testProjection R out root S q) hx = q.val) :
    Tree.ExactUnaryEmbedding
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S)
      R out where
  toFun := testProjection R out root S
  injective := by
    intro p q hpq
    obtain ⟨hps, hpe⟩ := hchart p
    obtain ⟨hqs, hqe⟩ := hchart q
    have heq : (⟨testProjection R out root S p, hps⟩ :
        {x : B // support R out root x s}) =
        ⟨testProjection R out root S q, hqs⟩ := Subtype.ext hpq
    have hcopy := congrArg
      (fun z : {x : B // support R out root x s} =>
        ChartAtlas.copy (graph R out root) (support R out root)
          s chi z.val z.property) heq
    exact Subtype.ext (hpe.symm.trans (hcopy.trans hqe))
  rel_iff := by
    intro n r xs
    constructor
    · intro hOld
      change (ChartAtlas.quotientStructure (graph R out root)
        (support R out root) R).rel r (fun i => (xs i).val)
      refine ⟨s, chi, (fun i => ⟨testProjection R out root S (xs i),
          (hchart (xs i)).1⟩), hOld, ?_⟩
      intro i
      exact (hchart (xs i)).2
    · intro hNew
      exact projection_rel_map R out root r (fun i => (xs i).val) hNew
  out_eq := by
    intro f q
    exact testProjection_fibres R out root S hS f q

/-- The old automorphism allows a chart-subtest to land in the distinguished
root, rather than merely in the entire previous-stage structure. -/
noncomputable def chartTestRootExact
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (s : Chart R out root) (chi : Edges R out root → ZMod 2)
    (S : Set (Vertex R out root))
    (hS : UnaryClosed (outputs R out root) (fun q => q ∈ S))
    (hchart : ∀ q : S, ∃ hx : support R out root
      (testProjection R out root S q) s,
      ChartAtlas.copy (graph R out root) (support R out root)
        s chi (testProjection R out root S q) hx = q.val)
    (h : Aut R out) (hs : s.val ⊆ h.perm '' root) :
    Tree.ExactUnaryEmbedding
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S)
      (inducedRelations R root) (inducedUnary out root) := by
  let e := chartTestExact R out root s chi S hS hchart
  have hmem : ∀ q : S,
      h.perm.symm (testProjection R out root S q) ∈ root := by
    intro q
    obtain ⟨a, ha, heq⟩ :=
      hs ((hchart q).1 : testProjection R out root S q ∈ s.val)
    change h.perm.symm (testProjection R out root S q) ∈ root
    rw [← heq, Equiv.symm_apply_apply]
    exact ha
  refine {
    toFun := fun q => ⟨h.perm.symm (testProjection R out root S q), hmem q⟩
    injective := ?_
    rel_iff := ?_
    out_eq := ?_ }
  · intro p q hpq
    apply e.injective
    exact h.perm.symm.injective (congrArg Subtype.val hpq)
  · intro n r xs
    change R.rel r (fun i => h.perm.symm
      (testProjection R out root S (xs i))) ↔
        (ChartAtlas.inducedAtlas (graph R out root)
          (support R out root) R S).rel r xs
    exact (h.symm.rel_iff r
      (fun i => testProjection R out root S (xs i))).trans
      (e.rel_iff r xs)
  · intro f p
    ext z
    constructor
    · rintro ⟨q, hq, hqz⟩
      change z.val ∈ out f (h.perm.symm (testProjection R out root S p))
      have hImg : testProjection R out root S q ∈
          e.toFun ''
            (ChartAtlas.inducedOutput (graph R out root)
              (support R out root) out (closed R out root) S f p) :=
        ⟨q, hq, rfl⟩
      rw [e.out_eq f p] at hImg
      have hNew : h.perm.symm (testProjection R out root S q) ∈
          out f (h.perm.symm (testProjection R out root S p)) :=
        (h.symm.unary_iff f
          (testProjection R out root S p)
          (testProjection R out root S q)).mpr hImg
      have hv := congrArg Subtype.val hqz
      rw [← hv]
      exact hNew
    · intro hz
      change z.val ∈ out f (h.perm.symm
        (testProjection R out root S p)) at hz
      have hOld : h.perm z.val ∈ out f
          (testProjection R out root S p) := by
        apply (h.symm.unary_iff f
          (testProjection R out root S p) (h.perm z.val)).mp
        simpa only [Equiv.symm_apply_apply] using hz
      have hImg : h.perm z.val ∈ e.toFun ''
          (ChartAtlas.inducedOutput (graph R out root)
            (support R out root) out (closed R out root) S f p) := by
        rw [e.out_eq f p]
        exact hOld
      obtain ⟨q, hq, hEq⟩ := hImg
      refine ⟨q, hq, Subtype.ext ?_⟩
      change h.perm.symm (testProjection R out root S q) = z.val
      rw [hEq, Equiv.symm_apply_apply]

/-- No extra chart automorphism has to be chosen: every canonical chart
already carries a witness in its definition. -/
theorem exists_chartTestRootExact
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (s : Chart R out root) (chi : Edges R out root → ZMod 2)
    (S : Set (Vertex R out root))
    (hS : UnaryClosed (outputs R out root) (fun q => q ∈ S))
    (hchart : ∀ q : S, ∃ hx : support R out root
      (testProjection R out root S q) s,
      ChartAtlas.copy (graph R out root) (support R out root)
        s chi (testProjection R out root S q) hx = q.val) :
    Nonempty (Tree.ExactUnaryEmbedding
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S)
      (inducedRelations R root) (inducedUnary out root)) := by
  obtain ⟨h, hs⟩ := s.property.2
  exact ⟨chartTestRootExact R out root s chi S hS hchart h hs⟩

end
end GluingEPPA.Sparsening.OrbitAtlas
