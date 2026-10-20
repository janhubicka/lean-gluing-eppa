import GluingEPPA.Steiner.QuotientSymmetry

/-!
# Transport quotient isomorphisms between different finite groups

The recursive Steiner construction builds different groups on different
edge subsets. A compatible equivalence of graph vertices and group values
therefore relates two different transport relations. It induces an
equivalence of their quotient sets, intertwining right multiplication.
This is the ingredient used when an automorphism permutes the coordinates
of the recursive finite product.
-/

namespace GluingEPPA.Steiner.Transport

universe u v w z
variable {V : Type u} {W : Type v}
variable {G : Type w} {H : Type z} [Group G] [Group H]

structure Iso (T : Transport V G) (U : Transport W H) where
  vertices : V ≃ W
  values : G ≃* H
  rel_iff : ∀ u v g,
    T.Rel u v g ↔ U.Rel (vertices u) (vertices v) (values g)

namespace Iso
variable {T : Transport V G} {U : Transport W H} (f : T.Iso U)

def symm : U.Iso T where
  vertices := f.vertices.symm
  values := f.values.symm
  rel_iff := by
    intro u v g
    have h := f.rel_iff (f.vertices.symm u) (f.vertices.symm v)
      (f.values.symm g)
    simpa using h.symm

/-- Map quotient points represented by a vertex and a group element. -/
def map : T.Space → U.Space :=
  Quotient.map (fun p => (f.vertices p.1, f.values p.2)) (by
    intro p q h
    apply Quotient.sound
    change U.Rel (f.vertices p.1) (f.vertices q.1)
      (f.values p.2 * (f.values q.2)⁻¹)
    have hp := (f.rel_iff p.1 q.1 (p.2 * q.2⁻¹)).mp h
    simpa only [map_mul, map_inv] using hp)

@[simp] theorem map_point (u : V) (g : G) :
    f.map (T.point u g) = U.point (f.vertices u) (f.values g) := rfl

@[simp] theorem map_marked (u : V) :
    f.map (T.marked u) = U.marked (f.vertices u) := by
  simp [marked]

@[simp] theorem symm_map_map (x : T.Space) :
    f.symm.map (f.map x) = x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨u, g⟩
  change T.point (f.vertices.symm (f.vertices u))
    (f.values.symm (f.values g)) = T.point u g
  simp

@[simp] theorem map_symm_map (x : U.Space) :
    f.map (f.symm.map x) = x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨u, g⟩
  change U.point (f.vertices (f.vertices.symm u))
    (f.values (f.values.symm g)) = U.point u g
  simp

def spaceEquiv : T.Space ≃ U.Space where
  toFun := f.map
  invFun := f.symm.map
  left_inv := f.symm_map_map
  right_inv := f.map_symm_map

theorem map_rightMul (x : T.Space) (g : G) :
    f.map (T.rightMul x g) =
      U.rightMul (f.map x) (f.values g) := by
  refine Quotient.inductionOn x ?_
  rintro ⟨u, h⟩
  change U.point (f.vertices u) (f.values (h * g)) =
    U.point (f.vertices u) (f.values h * f.values g)
  rw [map_mul]

end Iso
end GluingEPPA.Steiner.Transport
