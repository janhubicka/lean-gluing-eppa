import GluingEPPA.Steiner.DiagramIntersections

/-!
# Transport of Steiner triples in the lifted gluing diagram

Each edge e of the base diagram has a set of point labels which its
gluing map identifies. Transporting a pair x,y along an edge requires
both labels to belong to this set. Closedness of the local Steiner
systems says that if x,y,z is a triple at the source, then the gluing
also carries z and preserves the triple.

The exact intersection theorem turns two possibly different walks
transporting x and y between the SAME lifted vertices into one walk
transporting both. The following lemmas prove that this walk carries
their third point too. This is the central step in Lemma 5.1 of the
current manuscript, independent of the group-versus-diagram notation.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- The edges whose gluing maps identify a specified point label. -/
def edgesCarrying (overlap : E → Set Ω) (x : Ω) : Set E :=
  {e | x ∈ overlap e}

/-- A legal walk which carries two points also carries their completion.
The second conclusion retains both endpoints in the same ambient lift. -/
theorem pair_walk_carries_third
    (overlap : E → Set Ω) (triple : V → Ω → Ω → Ω → Prop)
    (closed : ∀ e u v x y z, D.Joins e u v →
       triple u x y z → x ∈ overlap e → y ∈ overlap e →
       z ∈ overlap e ∧ triple v x y z)
    (x y z : Ω) (u v : V)
    (g h : (family D Finset.univ).Carrier)
    (p : D.CayleyWalk
      (edgesCarrying overlap x ∩ edgesCarrying overlap y)
      (family D Finset.univ).edge u g v h)
    (ht : triple u x y z) :
    triple v x y z ∧
      D.CayleyWalk (edgesCarrying overlap z)
        (family D Finset.univ).edge u g v h := by
  revert ht
  induction p with
  | nil u g =>
      intro ht
      exact ⟨ht, CayleyWalk.nil u g⟩
  | @cons u v w g h e he hj p ih =>
      intro ht
      obtain ⟨hz, hv⟩ := closed e u v x y z hj ht he.1 he.2
      obtain ⟨hw, q⟩ := ih hv
      exact ⟨hw, CayleyWalk.cons hz hj q⟩

/-- The intersection property synchronizes separate transports of the
two labels; closedness then transports their third point. -/
theorem two_walks_carry_triple
    (overlap : E → Set Ω) (triple : V → Ω → Ω → Ω → Prop)
    (closed : ∀ e u v x y z, D.Joins e u v →
       triple u x y z → x ∈ overlap e → y ∈ overlap e →
       z ∈ overlap e ∧ triple v x y z)
    (x y z : Ω) (u v : V)
    (g h : (family D Finset.univ).Carrier)
    (px : D.CayleyWalk (edgesCarrying overlap x)
      (family D Finset.univ).edge u g v h)
    (py : D.CayleyWalk (edgesCarrying overlap y)
      (family D Finset.univ).edge u g v h)
    (ht : triple u x y z) :
    triple v x y z ∧
      D.CayleyWalk (edgesCarrying overlap z)
        (family D Finset.univ).edge u g v h := by
  exact pair_walk_carries_third D overlap triple closed x y z u v g h
    (set_exact_intersection_walk D
      (edgesCarrying overlap x) (edgesCarrying overlap y) u v g h px py) ht

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
