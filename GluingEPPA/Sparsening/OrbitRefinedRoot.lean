import GluingEPPA.Sparsening.OrbitProjectedLocalGlue

/-!
# The distinguished full chart remains closed and J-complete after refinement

The finite tower needs not only the local-tree inequality but also a
well-defined distinguished root at every stage. Both properties below
follow directly from the actual canonical quotient: complete unary
fibres keep a lifted full chart closed, and its internal J-tuples are
contributed from the old J-complete root.

No appeal to freeness of the old quotient image is made.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v w
variable {L : Nat → Type u} {F : Type w} {B : Type v}
open scoped Classical
noncomputable section
variable [Finite B]
attribute [local instance] chartsFintype edgesFintype

/-- The distinguished old root has its literal zero-valuation lifted
full chart as the root for the next stage. -/
def refinedRoot (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hr : UnaryClosed out (fun b => b ∈ root)) :
    Set (Vertex R out root) :=
  liftedChart R out root (rootChart R out root hr) 0

/-- The new distinguished root is closed under EVERY unary output. -/
theorem refinedRoot_closed
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hr : UnaryClosed out (fun b => b ∈ root)) :
    UnaryClosed (outputs R out root)
      (fun q => q ∈ refinedRoot R out root hr) := by
  exact ChartAtlas.lifted_chart_closed
    (graph R out root) (support R out root)
    out (closed R out root) (rootChart R out root hr) 0

/-- If the auxiliary J is complete on the old root, it is again complete
on the new distinguished lifted copy. This is a *real* J-relation of the
quotient, not an auxiliary graph of chart incidences. -/
theorem refinedRoot_J_complete
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hr : UnaryClosed out (fun b => b ∈ root))
    (hJ : Tree.IsJClique R root) :
    Tree.IsJClique (relations R out root)
      (refinedRoot R out root hr) := by
  intro p hp q hq
  obtain ⟨x, hx, hxp⟩ := hp
  obtain ⟨y, hy, hyq⟩ := hq
  let s := rootChart R out root hr
  let xs : Fin 2 → {a // support R out root a s} :=
    fun i => if i.val = 0 then ⟨x, hx⟩ else ⟨y, hy⟩
  have htuple : (fun i => (xs i).val) = Tree.JPair x y := by
    funext i
    fin_cases i <;> rfl
  change (ChartAtlas.quotientStructure (graph R out root)
    (support R out root) R).rel
    (Sum.inr (⟨(), rfl⟩ : JSymbol 2)) (Tree.JPair p q)
  refine ⟨s, 0, xs, ?_, ?_⟩
  · rw [htuple]
    exact hJ x hx y hy
  · intro i
    fin_cases i
    · simpa only [xs, Tree.JPair, dif_pos, ↓reduceIte] using hxp
    · simpa only [xs, Tree.JPair, dif_neg, Nat.reduceNe, ↓reduceIte] using hyq

end
end GluingEPPA.Sparsening.OrbitAtlas
