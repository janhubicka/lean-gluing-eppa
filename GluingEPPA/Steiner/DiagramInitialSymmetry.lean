import GluingEPPA.Steiner.DiagramInitialRepresentative

/-!
# Every label permutation acts on the actual Steiner EPPA gluing diagram

The vertices are labelled systems, not occurrences (σ,U). Relabelling
acts on their point sets and triple relations. An edge (F,S) is sent to
the edge between the relabelled full system and relabelled closed
subsystem. This gives a graph isomorphism and a compatible relabelling
of all local Steiner systems and their gluing domains.

Naturality of the recursively constructed valuation group was proved
earlier. This module supplies the missing *concrete graph action*.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord

universe u
variable {A : Type u} (R : A → A → A → Prop)

/-- Full systems stay full under relabelling. -/
theorem full_relabel (σ : Equiv.Perm A) (s : Site R)
    (h : Full R s) : Full R (Site.relabel R σ s) := by
  apply Set.ext
  intro x
  change (σ.symm x ∈ s.val.points) ↔ x ∈ Set.univ
  rw [h]
  simp

/-- Closed induced subsystems remain closed and induced after
relabeling every point and triple. -/
theorem closedSubsite_relabel (σ : Equiv.Perm A)
    (s f : Site R) (h : ClosedSubsite R s f) :
    ClosedSubsite R (Site.relabel R σ s) (Site.relabel R σ f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change σ.symm x ∈ s.val.points at hx
    change σ.symm x ∈ f.val.points
    exact h.subset_points hx
  · intro x y z hx hy hz
    change σ.symm x ∈ s.val.points at hx
    change σ.symm y ∈ s.val.points at hy
    change σ.symm z ∈ s.val.points at hz
    change s.val.triple (σ.symm x) (σ.symm y) (σ.symm z) ↔
      f.val.triple (σ.symm x) (σ.symm y) (σ.symm z)
    exact h.induced _ _ _ hx hy hz
  · intro x y z ht hx hy
    change f.val.triple (σ.symm x) (σ.symm y) (σ.symm z) at ht
    change σ.symm x ∈ s.val.points at hx
    change σ.symm y ∈ s.val.points at hy
    change σ.symm z ∈ s.val.points
    exact h.closure _ _ _ ht hx hy

/-- Relabelling cannot make two different point sets equal. -/
theorem relabel_points_ne (σ : Equiv.Perm A) (s f : Site R)
    (h : s.val.points ≠ f.val.points) :
    (Site.relabel R σ s).val.points ≠
      (Site.relabel R σ f).val.points := by
  intro heq
  apply h
  apply Set.ext
  intro x
  have hh : (σ x ∈ (Site.relabel R σ s).val.points) ↔
      (σ x ∈ (Site.relabel R σ f).val.points) := by
    rw [heq]
  change (σ.symm (σ x) ∈ s.val.points) ↔
    (σ.symm (σ x) ∈ f.val.points) at hh
  simpa using hh

/-- Relabel the two endpoints of an actual gluing edge. -/
def edgeRelabel (σ : Equiv.Perm A) (e : Edge R) : Edge R := by
  refine ⟨⟨Site.relabel R σ e.val.1,
    Site.relabel R σ e.val.2⟩, ?_⟩
  exact ⟨full_relabel R σ e.val.1 e.property.1,
    closedSubsite_relabel R σ e.val.2 e.val.1 e.property.2.1,
    relabel_points_ne R σ e.val.2 e.val.1 e.property.2.2⟩

@[simp] theorem edgeRelabel_refl (e : Edge R) :
    edgeRelabel R (Equiv.refl A) e = e := by
  apply Subtype.ext
  apply Prod.ext
  · exact Site.relabel_refl R e.val.1
  · exact Site.relabel_refl R e.val.2

theorem edgeRelabel_trans (σ τ : Equiv.Perm A) (e : Edge R) :
    edgeRelabel R τ (edgeRelabel R σ e) =
      edgeRelabel R (σ.trans τ) e := by
  apply Subtype.ext
  apply Prod.ext
  · exact Site.relabel_trans R σ τ e.val.1
  · exact Site.relabel_trans R σ τ e.val.2

/-- The action on named edges is a permutation. -/
def edgeRelabelEquiv (σ : Equiv.Perm A) : Equiv.Perm (Edge R) where
  toFun := edgeRelabel R σ
  invFun := edgeRelabel R σ.symm
  left_inv e := by
    rw [edgeRelabel_trans]
    simpa using edgeRelabel_refl R e
  right_inv e := by
    rw [edgeRelabel_trans]
    simpa using edgeRelabel_refl R e

/-- The induced automorphism of the undirected base edge graph. -/
def graphRelabel (σ : Equiv.Perm A) : Iso (graph R) (graph R) where
  vertex := Site.relabelEquiv R σ
  edge := edgeRelabelEquiv R σ
  joins := by
    intro e u v
    change ((Site.relabel R σ e.val.1 = Site.relabel R σ u ∧
      Site.relabel R σ e.val.2 = Site.relabel R σ v) ∨
      (Site.relabel R σ e.val.1 = Site.relabel R σ v ∧
        Site.relabel R σ e.val.2 = Site.relabel R σ u)) ↔
      ((e.val.1 = u ∧ e.val.2 = v) ∨
        (e.val.1 = v ∧ e.val.2 = u))
    constructor
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · exact Or.inl ⟨(Site.relabelEquiv R σ).injective ha,
          (Site.relabelEquiv R σ).injective hb⟩
      · exact Or.inr ⟨(Site.relabelEquiv R σ).injective ha,
          (Site.relabelEquiv R σ).injective hb⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

variable [Finite A]

/-- Ambient permutations preserve the actual local Steiner relations
and the closed gluing overlaps; graph incidence alone would not suffice. -/
noncomputable def inputSymmetry (P : Input A)
    (σ : Equiv.Perm A) :
    LabelledSymmetry (graph P.triple) (localDiagram P) where
  graph := graphRelabel P.triple σ
  labels := σ
  present := by
    intro s x
    change σ.symm (σ x) ∈ s.val.points ↔ x ∈ s.val.points
    simp
  triple := by
    intro s x y z
    change s.val.triple (σ.symm (σ x))
      (σ.symm (σ y)) (σ.symm (σ z)) ↔
      s.val.triple x y z
    simp
  overlap := by
    intro e x
    change σ.symm (σ x) ∈ e.val.2.val.points ↔
      x ∈ e.val.2.val.points
    simp

end GluingEPPA.Steiner.InitialSites
