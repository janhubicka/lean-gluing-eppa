import GluingEPPA.Steiner.WalkValues

/-!
# Actual walks in the Cayley lift

This is the lift in Section 4 of `steiner_recursive_gluing_valuations.tex`
(v7), not the transport quotient used by an earlier manuscript. A step
from `(u,g)` to `(v,g*a e)` retains its named base edge `e`. Restricting
edges to `M` never changes the group containing the second coordinate.

Only the elementary lemmas about values of actual base walks are reused.
No recursive-group existence or EPPA theorem is imported.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

universe u v w
variable {V : Type u} {E : Type v} {G : Type w} [Group G]
variable (D : EdgeGraph V E)

/-- An actual finite walk in the lift, with its group coordinate at each step. -/
inductive CayleyWalk (M : Set E) (a : E → G) : V → G → V → G → Prop
  | nil (u : V) (g : G) : CayleyWalk M a u g u g
  | cons {u v w : V} {g h : G} {e : E} :
      e ∈ M → D.Joins e u v → CayleyWalk M a v (g * a e) w h →
      CayleyWalk M a u g w h

namespace CayleyWalk
variable {D} {M : Set E} {a : E → G}

/-- Forgetting the lifted coordinates gives exactly the value `g⁻¹*h`. -/
theorem value {u v : V} {g h : G}
    (p : D.CayleyWalk M a u g v h) :
    D.WalkValue M a u v (g⁻¹ * h) := by
  induction p with
  | nil u g =>
      simpa using (WalkValue.nil (D := D) (S := M) (a := a) u)
  | @cons u v w g h e he hj p ih =>
      have q := WalkValue.cons he hj ih
      convert q using 1 <;> group

end CayleyWalk

namespace WalkValue
variable {D} {M : Set E} {a : E → G}

/-- Lift a base walk from any prescribed group coordinate. -/
theorem lift {u v : V} {k : G}
    (p : D.WalkValue M a u v k) (g : G) :
    D.CayleyWalk M a u g v (g * k) := by
  induction p generalizing g with
  | nil u =>
      simpa using (CayleyWalk.nil (D := D) (M := M) (a := a) u g)
  | @cons u v w e k he hj p ih =>
      simpa only [mul_assoc] using
        (CayleyWalk.cons he hj (ih (g * a e)))

end WalkValue

/-- Reachability in the literal lift, with both endpoints fixed. -/
theorem cayleyWalk_iff_value (M : Set E) (a : E → G)
    (u v : V) (g h : G) :
    D.CayleyWalk M a u g v h ↔ D.WalkValue M a u v (g⁻¹ * h) := by
  constructor
  · exact CayleyWalk.value
  · intro p
    simpa using p.lift g

namespace CayleyWalk
variable {D} {M : Set E} {a : E → G}

/-- Concatenation stays in the same lift. -/
theorem trans {u v w : V} {g h k : G}
    (p : D.CayleyWalk M a u g v h)
    (q : D.CayleyWalk M a v h w k) :
    D.CayleyWalk M a u g w k := by
  apply (D.cayleyWalk_iff_value M a u w g k).2
  have r := p.value.trans q.value
  convert r using 1 <;> group

/-- Reversal uses the same named edge; its value must be an involution. -/
theorem symm (ha : ∀ e ∈ M, a e * a e = 1)
    {u v : V} {g h : G} (p : D.CayleyWalk M a u g v h) :
    D.CayleyWalk M a v h u g := by
  apply (D.cayleyWalk_iff_value M a v u h g).2
  simpa only [mul_inv_rev, inv_inv] using p.value.symm ha

/-- Restricting the allowed edges does not replace `G` by another group. -/
theorem mono {N : Set E} (hMN : M ⊆ N)
    {u v : V} {g h : G} (p : D.CayleyWalk M a u g v h) :
    D.CayleyWalk N a u g v h := by
  exact (D.cayleyWalk_iff_value N a u v g h).2 (p.value.mono hMN)

end CayleyWalk

/-- Left multiplication preserves and reflects lifted walks. -/
theorem cayleyWalk_left_mul (M : Set E) (a : E → G)
    (k : G) (u v : V) (g h : G) :
    D.CayleyWalk M a u (k * g) v (k * h) ↔
      D.CayleyWalk M a u g v h := by
  rw [D.cayleyWalk_iff_value, D.cayleyWalk_iff_value]
  have hcoord : (k * g)⁻¹ * (k * h) = g⁻¹ * h := by group
  rw [hcoord]

/-- The set of vertices in the component of `z`, using allowed edges `M`. -/
def componentSet (M : Set E) (a : E → G) (z : V × G) : Set (V × G) :=
  {z' | D.CayleyWalk M a z.1 z.2 z'.1 z'.2}

theorem mem_componentSet_iff (M : Set E) (a : E → G)
    (u v : V) (g h : G) :
    (v,h) ∈ D.componentSet M a (u,g) ↔
      D.WalkValue M a u v (g⁻¹ * h) :=
  D.cayleyWalk_iff_value M a u v g h

end EdgeGraph
end GluingEPPA.Steiner
