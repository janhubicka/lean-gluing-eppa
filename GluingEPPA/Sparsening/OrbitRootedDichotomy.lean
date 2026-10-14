import GluingEPPA.Sparsening.OrbitProjectedLocalGlue

/-!
# The canonical orbit atlas has a J-complete projected free-cut root

Unlike the generic chart atlas, the chart indices here are actual closed
subsets of automorphic images of the distinguished old root. Hence if the
old root has complete J, every such chart does as well. This discharges
the last old-chart completeness hypothesis in the atlas geometric lemma.

The resulting alternatives are (1) a common lifted chart or (2) an
actual upstairs unary free decomposition whose OLD projected overlap is
a typed complete J-clique. No freeness is asserted downstairs.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v w
variable {L : Nat → Type u} {F : Type w} {B : Type v}
open scoped Classical
noncomputable section

/-- The actual old auxiliary binary symbol, not a metatheoretic
chart-incidence predicate. -/
def oldJ (R : RelStructure (WithJ L) B) (x y : B) : Prop :=
  R.rel (Sum.inr (⟨(), rfl⟩ : JSymbol 2)) (Tree.JPair x y)

/-- J-completeness of the distinguished old root transfers to all
canonical subcharts by the OLD automorphism supplied in the chart
definition. -/
theorem allCharts_J_complete
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hroot : ∀ x y, x ∈ root → y ∈ root → oldJ R x y)
    (s : Chart R out root) (x y : B)
    (hx : support R out root x s)
    (hy : support R out root y s) :
    oldJ R x y := by
  obtain ⟨h, hs⟩ := s.property.2
  obtain ⟨a, ha, hax⟩ := hs hx
  obtain ⟨b, hb, hby⟩ := hs hy
  have hh := (h.rel_iff
    (Sum.inr (⟨(), rfl⟩ : JSymbol 2))
    (Tree.JPair a b)).mpr (hroot a b ha hb)
  have htuple : (fun i : Fin 2 => h.perm (Tree.JPair a b i)) =
      Tree.JPair x y := by
    funext i
    fin_cases i
    · simpa [Tree.JPair] using hax
    · simpa [Tree.JPair] using hby
  change R.rel (Sum.inr (⟨(), rfl⟩ : JSymbol 2))
    (fun i : Fin 2 => h.perm (Tree.JPair a b i)) at hh
  rw [htuple] at hh
  exact hh

section Finite
variable [Finite B]
attribute [local instance] chartsFintype edgesFintype

/-- The concrete, fully quantified canonical chart-or-J-rooted-free-cut
dichotomy, now without a separate hypothesis about arbitrary chart
indices. The free cut is in the INDUCED UPSTAIRS test structure. -/
theorem chart_or_projected_Jroot
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hroot : ∀ x y, x ∈ root → y ∈ root → oldJ R x y)
    (S : Set (Vertex R out root)) [Nonempty S] :
    (∃ (s : Chart R out root)
      (chi : Edges R out root → ZMod 2),
      ∀ q : S, ∃ hx : support R out root
        (testProjection R out root S q) s,
        ChartAtlas.copy (graph R out root) (support R out root)
          s chi (testProjection R out root S q) hx = q.val) ∨
    (∃ d : UnaryFreeDecomposition
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S),
      ∀ (p q : S), p ∈ d.left → p ∈ d.right →
        q ∈ d.left → q ∈ d.right →
        oldJ R (testProjection R out root S p)
          (testProjection R out root S q)) := by
  exact ChartAtlas.atlas_chart_or_JRoot_freeCut
    (graph R out root) (support R out root)
    R out (closed R out root)
    CompleteChartGraph.complete
    (oldJ R)
    (allCharts_J_complete R out root hroot) S

/-- A form ready for recursive strict-tree gluing: in the cut case the
induced old projected overlap is a complete auxiliary J-clique. -/
theorem chart_or_projected_Jclique
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hroot : ∀ x y, x ∈ root → y ∈ root → oldJ R x y)
    (S : Set (Vertex R out root)) [Nonempty S] :
    (∃ (s : Chart R out root)
      (chi : Edges R out root → ZMod 2),
      ∀ q : S, ∃ hx : support R out root
        (testProjection R out root S q) s,
        ChartAtlas.copy (graph R out root) (support R out root)
          s chi (testProjection R out root S q) hx = q.val) ∨
    (∃ d : UnaryFreeDecomposition
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S),
      Tree.IsJClique
        (inducedRelations R
          (testProjection R out root S '' (d.left ∩ d.right)))
        Set.univ) := by
  rcases chart_or_projected_Jroot R out root hroot S with hchart | hcut
  · exact Or.inl hchart
  · obtain ⟨d, hJ⟩ := hcut
    exact Or.inr ⟨d, testProjection_overlap_J R out root S d hJ⟩

end Finite
end
end GluingEPPA.Sparsening.OrbitAtlas
