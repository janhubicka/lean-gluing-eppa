import GluingEPPA.Steiner.LiftedTriples

/-!
# Symmetries of the quotient of transported point occurrences

An isomorphism of the vertex set and the finite group preserving the
valued-walk relation induces an automorphism of its quotient space.
This is the elementary naturality step needed to lift base graph
automorphisms through the recursive group construction.
-/

namespace GluingEPPA.Steiner.Transport

universe u v
variable {V : Type u} {G : Type v} [Group G]
/-- Compatible symmetries of vertices and group values. -/
structure Symmetry (T : Transport V G) where
  vertices : V ≃ V
  values : G ≃* G
  preserves : ∀ u v g,
    T.Rel u v g ↔ T.Rel (vertices u) (vertices v) (values g)

namespace Symmetry
variable {T : Transport V G} (s : T.Symmetry)

def pair (p : V × G) : V × G :=
  (s.vertices p.1, s.values p.2)

theorem pair_respects (p q : V × G) (h : T.setoid.r p q) :
    T.setoid.r (s.pair p) (s.pair q) := by
  change T.Rel (s.vertices p.1) (s.vertices q.1)
    (s.values p.2 * (s.values q.2)⁻¹)
  have hp := (s.preserves p.1 q.1 (p.2 * q.2⁻¹)).mp h
  simpa only [map_mul, map_inv] using hp

def map : T.Space → T.Space :=
  Quotient.map s.pair (fun p q h => s.pair_respects p q h)

@[simp] theorem map_point (u : V) (g : G) :
    s.map (T.point u g) = T.point (s.vertices u) (s.values g) := rfl

@[simp] theorem map_marked (u : V) :
    s.map (T.marked u) = T.marked (s.vertices u) := by
  simp [marked]

def symm : T.Symmetry where
  vertices := s.vertices.symm
  values := s.values.symm
  preserves := by
    intro u v g
    have h := s.preserves (s.vertices.symm u) (s.vertices.symm v)
      (s.values.symm g)
    simpa using h.symm

@[simp] theorem symm_map_map (x : T.Space) :
    s.symm.map (s.map x) = x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨u, g⟩
  change T.point (s.vertices.symm (s.vertices u))
    (s.values.symm (s.values g)) = T.point u g
  simp

@[simp] theorem map_symm_map (x : T.Space) :
    s.map (s.symm.map x) = x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨u, g⟩
  change T.point (s.vertices (s.vertices.symm u))
    (s.values (s.values.symm g)) = T.point u g
  simp

def quotientEquiv : T.Space ≃ T.Space where
  toFun := s.map
  invFun := s.symm.map
  left_inv := s.symm_map_map
  right_inv := s.map_symm_map

theorem map_rightMul (x : T.Space) (g : G) :
    s.map (T.rightMul x g) =
      T.rightMul (s.map x) (s.values g) := by
  refine Quotient.inductionOn x ?_
  rintro ⟨u,h⟩
  change T.point (s.vertices u) (s.values (h * g)) =
    T.point (s.vertices u) (s.values h * s.values g)
  rw [map_mul]

end Symmetry
end GluingEPPA.Steiner.Transport
