import GluingEPPA.Steiner.RecursiveTransport

/-!
# Isomorphisms of actual Cayley lifts and components

Graph isomorphisms preserve incidence, not chosen orientations. Given a
smaller-stage group isomorphism, we construct the equivalence of actual
component sets and conjugate all component edge and word permutations.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
attribute [local instance] Classical.propDecidable
universe u
variable {V E V' E' V'' E'' G H : Type u}

/-- Named-edge isomorphisms may reverse endpoints independently. -/
structure Iso (D : EdgeGraph V E) (D' : EdgeGraph V' E') where
  vertex : V ≃ V'
  edge : E ≃ E'
  joins : ∀ e u v, D'.Joins (edge e) (vertex u) (vertex v) ↔ D.Joins e u v

namespace Iso
variable {D : EdgeGraph V E} {D' : EdgeGraph V' E'} {D'' : EdgeGraph V'' E''}

def refl (D : EdgeGraph V E) : Iso D D where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  joins _ _ _ := Iff.rfl

def symm (f : Iso D D') : Iso D' D where
  vertex := f.vertex.symm
  edge := f.edge.symm
  joins e u v := by
    simpa using (f.joins (f.edge.symm e) (f.vertex.symm u) (f.vertex.symm v)).symm

def trans (f : Iso D D') (g : Iso D' D'') : Iso D D'' where
  vertex := f.vertex.trans g.vertex
  edge := f.edge.trans g.edge
  joins e u v := (g.joins (f.edge e) (f.vertex u) (f.vertex v)).trans (f.joins e u v)

variable (f : Iso D D') [Group G] [Group H]
variable (M : Set E) (N : Set E') (a : E → G) (b : E' → H)
variable (F : G ≃* H)
variable (hMN : ∀ e, f.edge e ∈ N ↔ e ∈ M)
variable (hF : ∀ e ∈ M, F (a e) = b (f.edge e))

include hMN hF in
/-- The map sends actual lifted walks to actual lifted walks. -/
theorem map_cayleyWalk {u v : V} {g h : G}
    (p : D.CayleyWalk M a u g v h) :
    D'.CayleyWalk N b (f.vertex u) (F g) (f.vertex v) (F h) := by
  induction p with
  | nil u g => exact CayleyWalk.nil _ _
  | @cons u v w g h e he hj p ih =>
      have ih' : D'.CayleyWalk N b (f.vertex v) (F g * b (f.edge e))
          (f.vertex w) (F h) := by
        simpa only [map_mul, hF e he] using ih
      exact CayleyWalk.cons ((hMN e).2 he) ((f.joins e u v).2 hj) ih'

include hMN in
theorem inverse_membership (e : E') : f.edge.symm e ∈ M ↔ e ∈ N := by
  simpa using (hMN (f.edge.symm e)).symm

include hMN hF in
theorem inverse_generator (e : E') (he : e ∈ N) :
    F.symm (b e) = a (f.edge.symm e) := by
  apply F.injective
  have h := hF (f.edge.symm e) ((inverse_membership f M N hMN e).2 he)
  simpa using h.symm

include hMN hF in
/-- Both original lifted endpoints are retained. -/
theorem cayleyWalk_iff (u v : V) (g h : G) :
    D'.CayleyWalk N b (f.vertex u) (F g) (f.vertex v) (F h) ↔
      D.CayleyWalk M a u g v h := by
  constructor
  · intro p
    have q := map_cayleyWalk f.symm N M b a F.symm
      (inverse_membership f M N hMN)
      (inverse_generator f M N a b F hMN hF) p
    simpa [symm] using q
  · exact map_cayleyWalk f M N a b F hMN hF

variable (ha : ∀ e ∈ M, a e * a e = 1) (hb : ∀ e ∈ N, b e * b e = 1)

/-- The quotient is by actual lifted connectivity. -/
def mapComponent : D.Component M a ha → D'.Component N b hb :=
  Quotient.map (fun z : V × G => (f.vertex z.1, F z.2)) (by
    intro z z' p
    exact map_cayleyWalk f M N a b F hMN hF p)

@[simp] theorem mapComponent_apply (u : V) (g : G) :
    mapComponent f M N a b F hMN hF ha hb (D.component M a ha u g) =
      D'.component N b hb (f.vertex u) (F g) := rfl

def componentEquiv : D.Component M a ha ≃ D'.Component N b hb where
  toFun := mapComponent f M N a b F hMN hF ha hb
  invFun := mapComponent f.symm N M b a F.symm
    (inverse_membership f M N hMN)
    (inverse_generator f M N a b F hMN hF) hb ha
  left_inv c := by
    refine Quotient.inductionOn c ?_
    rintro ⟨u,g⟩
    change D.component M a ha (f.vertex.symm (f.vertex u)) (F.symm (F g)) =
      D.component M a ha u g
    simp
  right_inv c := by
    refine Quotient.inductionOn c ?_
    rintro ⟨u,g⟩
    change D'.component N b hb (f.vertex (f.vertex.symm u)) (F (F.symm g)) =
      D'.component N b hb u g
    simp

@[simp] theorem componentEquiv_apply (u : V) (g : G) :
    componentEquiv f M N a b F hMN hF ha hb (D.component M a ha u g) =
      D'.component N b hb (f.vertex u) (F g) := rfl

theorem componentEquiv_translation (k : G) (c : D.Component M a ha) :
    componentEquiv f M N a b F hMN hF ha hb
        (D.componentTranslation M a ha k c) =
      D'.componentTranslation N b hb (F k)
        (componentEquiv f M N a b F hMN hF ha hb c) := by
  refine Quotient.inductionOn c ?_
  rintro ⟨u,g⟩
  change D'.component N b hb (f.vertex u) (F (k * g)) =
    D'.component N b hb (f.vertex u) (F k * F g)
  rw [map_mul]

theorem componentEquiv_rightAction (k : G) (c : D.Component M a ha) :
    componentEquiv f M N a b F hMN hF ha hb (D.componentRightAction M a ha c k) =
      D'.componentRightAction N b hb
        (componentEquiv f M N a b F hMN hF ha hb c) (F k) := by
  unfold componentRightAction
  rw [componentEquiv_translation, map_inv]

end Iso

/-- Conjugacy of swaps does not require the marked points to differ. -/
theorem equiv_swap_apply {X Y : Type u} (f : X ≃ Y) (x y z : X) :
    f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) := by
  classical
  by_cases hx : z = x
  · subst z
    simp
  · by_cases hy : z = y
    · subst z
      simp
    · have hx' : f z ≠ f x := fun h => hx (f.injective h)
      have hy' : f z ≠ f y := fun h => hy (f.injective h)
      simp [Equiv.swap_apply_def, hx, hy, hx', hy']

namespace Iso
variable {D : EdgeGraph V E} {D' : EdgeGraph V' E'} (f : Iso D D')
variable [Group G] [Group H]
variable (M : Set E) (N : Set E') (a : E → G) (b : E' → H)
variable (F : G ≃* H) (hMN : ∀ e, f.edge e ∈ N ↔ e ∈ M)
variable (hF : ∀ e ∈ M, F (a e) = b (f.edge e))
variable (ha : ∀ e ∈ M, a e * a e = 1) (hb : ∀ e ∈ N, b e * b e = 1)

/-- Internal translations and external swaps both commute with relabelling. -/
theorem componentEquiv_edgePerm (e : E) (c : D.Component M a ha) :
    componentEquiv f M N a b F hMN hF ha hb (D.componentEdgePerm M a ha e c) =
      D'.componentEdgePerm N b hb (f.edge e)
        (componentEquiv f M N a b F hMN hF ha hb c) := by
  classical
  by_cases he : e ∈ M
  · rw [D.componentEdgePerm_of_mem M a ha he,
      D'.componentEdgePerm_of_mem N b hb ((hMN e).2 he)]
    change componentEquiv f M N a b F hMN hF ha hb
        (D.componentTranslation M a ha (a e) c) =
      D'.componentTranslation N b hb (b (f.edge e))
        (componentEquiv f M N a b F hMN hF ha hb c)
    rw [componentEquiv_translation, hF e he]
  · have he' : f.edge e ∉ N := fun h => he ((hMN e).1 h)
    rw [D.componentEdgePerm_of_not_mem M a ha he,
      D'.componentEdgePerm_of_not_mem N b hb he']
    rw [equiv_swap_apply]
    simp only [componentEquiv_apply, map_one]
    have hj := (f.joins e (D.source e) (D.target e)).2 (D.joins_endpoints e)
    rcases hj with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [← hs, ← ht]
    · rw [← ht, ← hs, Equiv.swap_comm]

/-- Arbitrary words, not merely walks, satisfy the conjugacy identity. -/
theorem componentEquiv_wordPerm (w : List E) (c : D.Component M a ha) :
    componentEquiv f M N a b F hMN hF ha hb (D.componentWordPerm M a ha w c) =
      D'.componentWordPerm N b hb (w.map f.edge)
        (componentEquiv f M N a b F hMN hF ha hb c) := by
  induction w generalizing c with
  | nil => rfl
  | cons e w ih =>
      simp only [List.map_cons, componentWordPerm_cons]
      rw [ih, componentEquiv_edgePerm]

end Iso
end EdgeGraph
end GluingEPPA.Steiner
