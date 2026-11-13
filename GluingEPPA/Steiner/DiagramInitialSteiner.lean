import GluingEPPA.Steiner.DiagramInitialRootEdge

/-!
# The actual local partial Steiner systems of the initial EPPA diagram

Every labelled site inherits its triples from a closed induced subsystem
of the input. Each gluing edge is an inclusion of a proper closed
subsystem of a full copy. In either direction, carrying the first two
points of a triple also carries its third point.

Thus the concrete initial diagram supplies the hypotheses of the
already verified Steiner free-realization lemma, not a substitute
assumed EPPA witness.
-/

namespace GluingEPPA.Steiner.InitialSites

universe u
variable {A : Type u}

/-- A finite partial Steiner triple system, in ordered-triple notation. -/
structure Input (A : Type u) where
  triple : A → A → A → Prop
  unique : ∀ x y z z', triple x y z → triple x y z' → z = z'
  swap : ∀ x y z, triple x y z → triple y x z
  rotate : ∀ x y z, triple x y z → triple y z x
  distinct : ∀ x y z, triple x y z → x ≠ y ∧ x ≠ z ∧ y ≠ z

/-- A local triple has all its labels in that local system. -/
theorem site_triple_present (R : A → A → A → Prop)
    (s : Site R) (x y z : A) (ht : s.val.triple x y z) :
    x ∈ s.val.points ∧ y ∈ s.val.points ∧ z ∈ s.val.points := by
  obtain ⟨σ, U, hU, hs⟩ := s.property
  rw [hs] at ht ⊢
  exact ht.2

theorem site_triple_unique (P : Input A) (s : Site P.triple)
    (x y z z' : A) (ht : s.val.triple x y z)
    (ht' : s.val.triple x y z') : z = z' := by
  obtain ⟨σ, U, hU, hs⟩ := s.property
  rw [hs] at ht ht'
  apply σ.symm.injective
  exact P.unique (σ.symm x) (σ.symm y) (σ.symm z) (σ.symm z')
    ht.1 ht'.1

theorem site_triple_swap (P : Input A) (s : Site P.triple)
    (x y z : A) (ht : s.val.triple x y z) :
    s.val.triple y x z := by
  obtain ⟨σ, U, hU, hs⟩ := s.property
  rw [hs] at ht ⊢
  exact ⟨P.swap _ _ _ ht.1, ht.2.2.1, ht.2.1, ht.2.2.2⟩

theorem site_triple_rotate (P : Input A) (s : Site P.triple)
    (x y z : A) (ht : s.val.triple x y z) :
    s.val.triple y z x := by
  obtain ⟨σ, U, hU, hs⟩ := s.property
  rw [hs] at ht ⊢
  exact ⟨P.rotate _ _ _ ht.1, ht.2.2.1, ht.2.2.2, ht.2.1⟩

theorem site_triple_distinct (P : Input A) (s : Site P.triple)
    (x y z : A) (ht : s.val.triple x y z) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨σ, U, hU, hs⟩ := s.property
  rw [hs] at ht
  obtain ⟨hxy, hxz, hyz⟩ :=
    P.distinct (σ.symm x) (σ.symm y) (σ.symm z) ht.1
  exact ⟨fun h => hxy (congrArg σ.symm h),
    fun h => hxz (congrArg σ.symm h),
    fun h => hyz (congrArg σ.symm h)⟩

/-- Every edge is a closed gluing inclusion in either direction.
This is the concrete structure consumed by DiagramFreeQuotient. -/
def localDiagram (P : Input A) :
    EdgeGraph.RecursiveRecord.LabelledSteiner (graph P.triple) A where
  present := fun s x => x ∈ s.val.points
  triple := fun s x y z => s.val.triple x y z
  triple_present := by
    intro s x y z ht
    exact site_triple_present P.triple s x y z ht
  triple_unique := by
    intro s x y z z' ht ht'
    exact site_triple_unique P s x y z z' ht ht'
  triple_swap := by
    intro s x y z ht
    exact site_triple_swap P s x y z ht
  triple_rotate := by
    intro s x y z ht
    exact site_triple_rotate P s x y z ht
  triple_distinct := by
    intro s x y z ht
    exact site_triple_distinct P s x y z ht
  overlap := overlap P.triple
  overlap_present := by
    intro e x hx
    exact overlap_at_ends P.triple e x hx
  overlap_closed := by
    intro e u v x y z hj ht hx hy
    rcases hj with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · subst u
      subst v
      exact edge_triple_down P.triple e x y z ht hx hy
    · subst v
      subst u
      have hz : z ∈ overlap P.triple e :=
        (site_triple_present P.triple e.val.2 x y z ht).2.2
      exact ⟨hz, (e.property.2.1.induced x y z hx hy hz).1 ht⟩

end GluingEPPA.Steiner.InitialSites
