import GluingEPPA.Steiner.DiagramFreeQuotient

/-!
# Uniqueness of Steiner completions in the free quotient

Separate walks may identify the first two points of a triple at two
different lifted vertices. Exact intersections supply one common walk;
closedness then transports their third point. The local Steiner axiom
forces the same completion at the other endpoint.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- Free-realization points for the actual final recursive valuation. -/
noncomputable abbrev realizedPoint (L : LabelledSteiner D Ω) : Type _ :=
  FreePoint D L (family D Finset.univ).edge
    (fun e => family_square D Finset.univ e)

/-- The canonical image of a local point in the free realization. -/
noncomputable def canonicalPoint (L : LabelledSteiner D Ω)
    (u : V) (g : (family D Finset.univ).Carrier)
    (x : Ω) (hx : L.present u x) : realizedPoint D L :=
  pointAt D L (family D Finset.univ).edge
    (fun e => family_square D Finset.univ e) u g x hx

/-- Equality of quotient points is exactly equality of labels plus
    a walk between their actual lifted endpoints. -/
theorem canonicalPoint_eq_iff (L : LabelledSteiner D Ω)
    (u v : V) (g h : (family D Finset.univ).Carrier)
    (x y : Ω) (hx : L.present u x) (hy : L.present v y) :
    canonicalPoint D L u g x hx = canonicalPoint D L v h y hy ↔
    x = y ∧ D.CayleyWalk (edgesCarrying L.overlap x)
      (family D Finset.univ).edge u g v h := by
  exact pointAt_eq_iff D L (family D Finset.univ).edge
    (fun e => family_square D Finset.univ e) u v g h x y hx hy

/-- Given the same two quotient points, local triples at the two
    lifted vertices have the same third label and third quotient point. -/
theorem completion_agrees_across_copies (L : LabelledSteiner D Ω)
    (u v : V) (g h : (family D Finset.univ).Carrier)
    (x y z z' : Ω)
    (ht : L.triple u x y z) (ht' : L.triple v x y z')
    (hx : canonicalPoint D L u g x ((L.triple_present u x y z ht).1) =
      canonicalPoint D L v h x ((L.triple_present v x y z' ht').1))
    (hy : canonicalPoint D L u g y ((L.triple_present u x y z ht).2.1) =
      canonicalPoint D L v h y ((L.triple_present v x y z' ht').2.1)) :
    z = z' ∧
    canonicalPoint D L u g z ((L.triple_present u x y z ht).2.2) =
      canonicalPoint D L v h z' ((L.triple_present v x y z' ht').2.2) := by
  have wx := ((canonicalPoint_eq_iff D L u v g h x x
    ((L.triple_present u x y z ht).1)
    ((L.triple_present v x y z' ht').1)).mp hx).2
  have wy := ((canonicalPoint_eq_iff D L u v g h y y
    ((L.triple_present u x y z ht).2.1)
    ((L.triple_present v x y z' ht').2.1)).mp hy).2
  obtain ⟨hz, wz⟩ := two_walks_carry_triple D
    L.overlap L.triple L.overlap_closed x y z u v g h wx wy ht
  have eqz : z = z' := L.triple_unique v x y z z' hz ht'
  refine ⟨eqz, ?_⟩
  subst z'
  apply (canonicalPoint_eq_iff D L u v g h z z
    ((L.triple_present u x y z ht).2.2)
    ((L.triple_present v x y z ht').2.2)).mpr
  exact ⟨rfl, wz⟩

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
