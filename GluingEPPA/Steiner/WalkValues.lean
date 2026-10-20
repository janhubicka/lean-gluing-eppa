import Mathlib

/-!
# Values of walks for the Steiner EPPA construction

Edges are named, so parallel edges remain distinct. `WalkValue` is an inductive
relation on actual graph walks, not an algebraic word-membership predicate.
-/

namespace GluingEPPA.Steiner

universe u v w z

structure EdgeGraph (V : Type u) (E : Type v) where
  source : E → V
  target : E → V
  loopless : ∀ e, source e ≠ target e

namespace EdgeGraph

variable {V : Type u} {E : Type v} (D : EdgeGraph V E)

def Joins (e : E) (u v : V) : Prop :=
  (D.source e = u ∧ D.target e = v) ∨
  (D.source e = v ∧ D.target e = u)

theorem joins_symm {e : E} {u v : V} (h : D.Joins e u v) :
    D.Joins e v u := Or.symm h

theorem joins_endpoints (e : E) : D.Joins e (D.source e) (D.target e) :=
  Or.inl ⟨rfl, rfl⟩

variable {G : Type w} [Group G]

inductive WalkValue (S : Set E) (a : E → G) : V → V → G → Prop
  | nil (v : V) : WalkValue S a v v 1
  | cons {u v w : V} {e : E} {g : G} :
      e ∈ S → D.Joins e u v → WalkValue S a v w g →
      WalkValue S a u w (a e * g)

namespace WalkValue

variable {D} {S : Set E} {a : E → G}

theorem single {u v : V} {e : E} (he : e ∈ S) (hj : D.Joins e u v) :
    D.WalkValue S a u v (a e) := by
  simpa using WalkValue.cons he hj (WalkValue.nil v)

theorem trans {u v w : V} {g h : G}
    (p : D.WalkValue S a u v g) (q : D.WalkValue S a v w h) :
    D.WalkValue S a u w (g * h) := by
  induction p with
  | nil => simpa using q
  | cons he hj p ih =>
      simpa only [mul_assoc] using WalkValue.cons he hj (ih q)

theorem symm (hinv : ∀ e ∈ S, a e * a e = 1)
    {u v : V} {g : G} (p : D.WalkValue S a u v g) :
    D.WalkValue S a v u g⁻¹ := by
  induction p with
  | nil => simpa using WalkValue.nil (D := D) (S := S) (a := a) _
  | @cons u v w e g he hj p ih =>
      have hae : (a e)⁻¹ = a e := by
        calc
          (a e)⁻¹ = (a e)⁻¹ * 1 := (mul_one _).symm
          _ = (a e)⁻¹ * (a e * a e) := by rw [hinv e he]
          _ = a e := by group
      simpa only [mul_inv_rev, hae] using
        ih.trans (WalkValue.single he (D.joins_symm hj))

theorem mono {S T : Set E} (hST : S ⊆ T)
    {u v : V} {g : G} (p : D.WalkValue S a u v g) :
    D.WalkValue T a u v g := by
  induction p with
  | nil => exact WalkValue.nil _
  | cons he hj _ ih => exact WalkValue.cons (hST he) hj ih

theorem map {H : Type z} [Group H] (f : G →* H)
    {u v : V} {g : G} (p : D.WalkValue S a u v g) :
    D.WalkValue S (fun e => f (a e)) u v (f g) := by
  induction p with
  | nil => simpa only [map_one] using
      WalkValue.nil (D := D) (S := S) (a := fun e => f (a e)) _
  | cons he hj _ ih =>
      simpa only [map_mul] using WalkValue.cons he hj ih

end WalkValue
end EdgeGraph

/-- The elementary closure properties of values of actual walks. This interface
is instantiated by `EdgeGraph.transport` below; it assumes no membership theorem. -/
structure Transport (V : Type u) (G : Type w) [Group G] where
  Rel : V → V → G → Prop
  refl : ∀ v, Rel v v 1
  symm : ∀ {u v g}, Rel u v g → Rel v u g⁻¹
  trans : ∀ {u v w g h}, Rel u v g → Rel v w h → Rel u w (g * h)

namespace EdgeGraph

variable {V : Type u} {E : Type v} {G : Type w} [Group G]

def transport (D : EdgeGraph V E) (S : Set E) (a : E → G)
    (hinv : ∀ e ∈ S, a e * a e = 1) : Transport V G where
  Rel := D.WalkValue S a
  refl := WalkValue.nil
  symm := WalkValue.symm hinv
  trans := WalkValue.trans

end EdgeGraph
end GluingEPPA.Steiner
