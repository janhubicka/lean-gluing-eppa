import GluingEPPA.Steiner.LiftedTriples

/-!
# Genuine chart occurrences in the Steiner realization

Not every label is present in every chart. The quotient of all labelled
formal occurrences from `LiftedTriples` is convenient for proving
transport, but the actual realization retains only classes with a
representative present in some local chart. This file proves that the
finite exact-transport construction yields unique completion and
closed chart images on that genuine realization.
-/

namespace GluingEPPA.Steiner

universe u v
variable {V E : Type u} {A : Type v}
variable [Fintype E] [DecidableEq E] [Finite V]
attribute [local instance] Classical.propDecidable

/-- The labels present in each local structure, together with compatibility
of the given closed-domain edge identifications. -/
structure PresentLabels (D : LabelledGraph V E A) where
  present : V → A → Prop
  triple_present : ∀ {s x y z}, D.triple s x y z →
    present s x ∧ present s y ∧ present s z
  edge_present : ∀ {e s t x}, D.graph.Joins e s t → D.carries e x →
    present s x ∧ present t x

namespace PresentLabels
variable {D : LabelledGraph V E A} (P : PresentLabels D)

/-- True point occurrences, rather than a copy of every label at every site. -/
def Actual : Type (max u v) :=
  { q : (D.lifted).Realization //
    ∃ (s : D.Sheet) (x : A), P.present s.1 x ∧ (D.lifted).copy s x = q }

/-- A point of a labelled chart gives a point in the true realization. -/
def copy (s : D.Sheet) (x : A) (hx : P.present s.1 x) : P.Actual :=
  ⟨(D.lifted).copy s x, ⟨s, x, hx, rfl⟩⟩

/-- A point relation in the genuine realization is contributed locally. -/
def triple (x y z : P.Actual) : Prop :=
  (D.lifted).tripleOnRealization x.val y.val z.val

theorem copy_injective (s : D.Sheet)
    {x y : A} (hx : P.present s.1 x) (hy : P.present s.1 y)
    (h : P.copy s x hx = P.copy s y hy) : x = y := by
  have heq := congrArg Subtype.val h
  exact (D.lifted).copy_injective s heq

/-- Two present occurrences are identified exactly when a carrying walk
joins their original lifted sites with the original label. -/
theorem copy_eq_iff (s t : D.Sheet) (x y : A)
    (hx : P.present s.1 x) (hy : P.present t.1 y) :
    P.copy s x hx = P.copy t y hy ↔ x = y ∧ D.liftRel x s t := by
  constructor
  · intro h
    have heq := congrArg Subtype.val h
    obtain ⟨hxy, hc⟩ := ((D.lifted).copy_eq_iff s t x y).mp heq
    exact ⟨hxy, D.carries_as_walk x hc⟩
  · rintro ⟨hxy, hc⟩
    apply Subtype.ext
    apply ((D.lifted).copy_eq_iff s t x y).mpr
    exact ⟨hxy, Relation.ReflTransGen.single hc⟩

/-- Every local triple gives a contributed triple in the true realization. -/
theorem triple_of_chart {s : D.Sheet} {x y z : A}
    (ht : D.triple s.1 x y z) :
    P.triple (P.copy s x (P.triple_present ht).1)
      (P.copy s y (P.triple_present ht).2.1)
      (P.copy s z (P.triple_present ht).2.2) := by
  exact ⟨s, x, y, z, ht, rfl, rfl, rfl⟩

/-- Uniqueness of the completed point in the true Steiner realization. -/
theorem triple_unique {b c d e : P.Actual}
    (h : P.triple b c d) (k : P.triple b c e) : d = e := by
  apply Subtype.ext
  exact D.lifted_triple_unique h k

/-- Any contributed triple meeting the actual chart in two vertices
is the image of a local triple. -/
theorem chart_closed {s : D.Sheet} {x y : A}
    (hx : P.present s.1 x) (hy : P.present s.1 y) {d : P.Actual}
    (h : P.triple (P.copy s x hx) (P.copy s y hy) d) :
    ∃ z (hz : P.present s.1 z), D.triple s.1 x y z ∧ P.copy s z hz = d := by
  obtain ⟨z, ht, heq⟩ := D.lifted_chart_closed h
  have hz : P.present s.1 z := (P.triple_present ht).2.2
  refine ⟨z, hz, ht, ?_⟩
  apply Subtype.ext
  exact heq

end PresentLabels
end GluingEPPA.Steiner
