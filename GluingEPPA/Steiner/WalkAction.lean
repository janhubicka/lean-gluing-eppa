import GluingEPPA.Steiner.Restriction

/-!
# The walk-replacement step from a quotient coordinate

Mathlib permutations use ordinary left composition. The paper uses right
composition. Accordingly an actual forward walk of value `g` acts on marked
vertices through `ρ g⁻¹`. The quotient action is inverse right multiplication,
so these inversions cancel exactly in `replacement_of_coordinate`.
-/

namespace GluingEPPA.Steiner

universe u v w z t

namespace EdgeGraph

variable {V : Type u} {E : Type v} {G : Type w} [Group G]
variable {D : EdgeGraph V E} {S : Set E} {a : E → G}

/-- Actual walks transport their marked endpoints. The inverse accounts for
Mathlib's left permutation convention. -/
theorem WalkValue.action_endpoint {X : Type z}
    (ρ : G →* Equiv.Perm X) (mark : V → X)
    (ha : ∀ e ∈ S, a e * a e = 1)
    (hedge : ∀ e ∈ S, ∀ u v, D.Joins e u v → ρ (a e) (mark u) = mark v)
    {u v : V} {g : G} (p : D.WalkValue S a u v g) :
    ρ g⁻¹ (mark u) = mark v := by
  induction p with
  | nil => simp
  | @cons u v w e g he hj p ih =>
      calc
        ρ (a e * g)⁻¹ (mark u) = ρ g⁻¹ (ρ (a e) (mark u)) := by
          simp only [mul_inv_rev, map_mul, Equiv.Perm.mul_apply,
            involutive_inv_eq (ha e he)]
        _ = ρ g⁻¹ (mark v) := by rw [hedge e he u v hj]
        _ = mark w := ih

end EdgeGraph

namespace Transport

variable {V : Type u} {G : Type v} [Group G]
variable (T : Transport V G)

/-- The action on a quotient recognizes an actual walk value. -/
theorem action_inv_marked_iff (u v : V) (g : G) :
    T.action g⁻¹ (T.marked u) = T.marked v ↔ T.Rel u v g := by
  simpa only [action_apply, inv_inv, rightMul_marked] using
    T.point_eq_marked_iff u v g

variable {E : Type w} {K : Type z} [Group K]

/-- Property (ii) of Lemma 2.2, once the embedding and its quotient coordinate
have been constructed. The conclusion is the original relation of actual
smaller walks, not membership in a generated subgroup. -/
theorem replacement_of_coordinate
    (D : EdgeGraph V E) (S : Set E) (a : E → K)
    (ha : ∀ e ∈ S, a e * a e = 1)
    (i : G →* K) (ρ : K →* Equiv.Perm T.Space)
    (hcoordinate : ∀ g, ρ (i g) = T.action g)
    (hedge : ∀ e ∈ S, ∀ u v, D.Joins e u v →
      ρ (a e) (T.marked u) = T.marked v)
    {u v : V} {k : K} {g : G}
    (p : D.WalkValue S a u v k) (hk : k = i g) : T.Rel u v g := by
  have hend := p.action_endpoint ρ T.marked ha hedge
  apply (T.action_inv_marked_iff u v g).mp
  calc
    T.action g⁻¹ (T.marked u) = ρ (i g⁻¹) (T.marked u) := by
      rw [hcoordinate]
    _ = ρ (i g)⁻¹ (T.marked u) := by rw [map_inv]
    _ = T.marked v := by simpa only [hk] using hend

/-- Lemma 2.1 with the induction's literal old membership hypothesis and
ordinary subgroup generation, rather than assuming reflection or word surjectivity. -/
theorem restriction_factors_of_membership
    {H : Type t} [Group H] (L : Transport V H) (i : H →* G)
    (pres : ∀ u v g, L.Rel u v g → T.Rel u v (i g))
    (hi : Function.Injective i)
    (hm : ∀ u v g, T.Rel u v (i g) →
      ∃ h, L.Rel u v h ∧ i h = i g)
    (a : E → K) (b : E → H) (inside : E → Prop) (source target : E → V)
    (ρ : K →* Equiv.Perm L.Space) (del : K →* H)
    (hon : ∀ e, inside e → ρ (a e) = L.action (b e))
    (hout : ∀ e, ¬ inside e → ρ (a e) = L.swapPoints (source e) (target e))
    (hdel : ∀ e, inside e → del (a e) = b e)
    (hdelout : ∀ e, ¬ inside e → del (a e) = 1)
    (ha : ∀ e, a e * a e = 1)
    (hgen : Subgroup.closure (Set.range a) = ⊤) :
    ∃ φ : K →* Equiv.Perm T.Space,
      ∀ e, φ (a e) = T.restrictedEdge i inside b source target e := by
  exact T.restriction_factors L i pres
    (T.reflects_of_membership L i hi hm) a b inside source target ρ del
    hon hout hdel hdelout ha (exists_word_of_closure a ha hgen)

end Transport
end GluingEPPA.Steiner
