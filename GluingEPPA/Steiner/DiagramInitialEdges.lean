import GluingEPPA.Steiner.DiagramInitialSites

/-!
# Edges of the concrete Steiner EPPA gluing diagram

The vertices are actual labelled closed subsystems (not pairs of
permutations and subsets). An edge joins a full labelled system F to
a *proper closed induced subsystem* S of F. Its gluing domain is the
point set of S. Thus a labelled relation tuple is present at most once;
no additional notion of edge type or multiplicity is introduced.

This is the undirected-edge object used in Section 6 of the manuscript.
-/

namespace GluingEPPA.Steiner.InitialSites

universe u
variable {A : Type u} (R : A → A → A → Prop)

/-- A local system is full when all ambient labels occur as points. -/
def Full (s : Site R) : Prop := s.val.points = Set.univ

/-- The smaller system is induced and closed in the larger system. -/
structure ClosedSubsite (s f : Site R) : Prop where
  subset_points : s.val.points ⊆ f.val.points
  induced : ∀ x y z, x ∈ s.val.points → y ∈ s.val.points →
    z ∈ s.val.points → (s.val.triple x y z ↔ f.val.triple x y z)
  closure : ∀ x y z, f.val.triple x y z →
    x ∈ s.val.points → y ∈ s.val.points → z ∈ s.val.points

/-- One undirected named edge for each actual full-to-proper-closed
subsystem pair. There are no indexed duplicates of an edge. -/
def Edge :=
  {p : Site R × Site R //
    Full R p.1 ∧ ClosedSubsite R p.2 p.1 ∧
      p.2.val.points ≠ p.1.val.points}

/-- The directed notation stores the full end first. A walk in the
underlying undirected graph may of course traverse it either way. -/
def graph : EdgeGraph (Site R) (Edge R) where
  source e := e.val.1
  target e := e.val.2
  loopless e := by
    intro h
    apply e.property.2.2
    exact (congrArg (fun s : Site R => s.val.points) h).symm

instance edge_finite [Finite A] : Finite (Edge R) := by
  classical
  infer_instance

/-- Gluing is the identity on the smaller system's point set. -/
def overlap (e : Edge R) : Set A := e.val.2.val.points

/-- Every point in a gluing domain occurs in both local systems. -/
theorem overlap_at_ends (e : Edge R) (x : A)
    (hx : x ∈ overlap R e) :
    x ∈ ((graph R).source e).val.points ∧
    x ∈ ((graph R).target e).val.points := by
  exact ⟨e.property.2.1.subset_points hx, hx⟩

/-- Closure and inducedness transport triples across an edge when it
is traversed from its full system to its smaller system. -/
theorem edge_triple_down (e : Edge R) (x y z : A)
    (ht : e.val.1.val.triple x y z)
    (hx : x ∈ overlap R e) (hy : y ∈ overlap R e) :
    z ∈ overlap R e ∧ e.val.2.val.triple x y z := by
  have hz := e.property.2.1.closure x y z ht hx hy
  exact ⟨hz, (e.property.2.1.induced x y z hx hy hz).2 ht⟩

/-- The original full labelled copy is present as a vertex. -/
def root : Site R :=
  siteOf R Set.univ (by intro x y z _ _ _; trivial)
    (Equiv.refl A)

theorem root_full : Full R (root R) := by
  rfl

theorem root_triple (x y z : A) :
    (root R).val.triple x y z ↔ R x y z := by
  simp [root, siteOf, SiteData.relabel, induced]

end GluingEPPA.Steiner.InitialSites
