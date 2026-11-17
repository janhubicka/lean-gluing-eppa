import GluingEPPA.Steiner.ChainValuation.MatchingActionEquiv
import GluingEPPA.Steiner.ChainValuation.ChainState

/-!
# Natural equivalence of single Cayley blocks and their completed matchings

A group isomorphism carrying the active named generators to the relabelled
ones preserves and reflects all genuine edges. Therefore it also conjugates
the completed involutions, including fixed points of inactive letters.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {E' : Type v}
variable (A : GroupBlock E) (B : GroupBlock E')
variable (p : E ≃ E') (F : A.Carrier ≃* B.Carrier)
variable (hActive : ∀ e, e ∈ A.active ↔ p e ∈ B.active)
variable (hEdge : ∀ e ∈ A.active, F (A.edge e) = B.edge (p e))

/-- Genuine Cayley edges are preserved and reflected under relabelling. -/
theorem groupBlock_edgeRel_relabel_iff (e : E) (x y : A.Carrier) :
    A.edgeRel e x y ↔ B.edgeRel (p e) (F x) (F y) := by
  constructor
  · rintro ⟨he, rfl⟩
    refine ⟨(hActive e).mp he, ?_⟩
    simp only [map_mul, hEdge e he]
  · rintro ⟨he, hy⟩
    have heA : e ∈ A.active := (hActive e).mpr he
    refine ⟨heA, ?_⟩
    apply F.injective
    calc
      F y = F x * B.edge (p e) := hy
      _ = F (x * A.edge e) := by rw [map_mul, hEdge e heA]

/-- The same block isomorphism conjugates the completed involutions. -/
theorem groupBlock_matching_relabel (e : E) (x : A.Carrier) :
    F ((A.matching e).perm x) = (B.matching (p e)).perm (F x) :=
  matching_perm_conjugate_of_rel_iff F.toEquiv
    (A.matching e) (B.matching (p e))
    (groupBlock_edgeRel_relabel_iff A B p F hActive hEdge e) x

end GluingEPPA.Steiner.ChainValuation
