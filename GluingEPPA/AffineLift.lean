import GluingEPPA.Cover
import GluingEPPA.Symmetry

namespace GluingEPPA
universe u v w
namespace EdgeGraph
variable {V : Type u} {E : Type v} {A : Type w}
variable [DecidableEq E]

/-- Permute edge coordinates and translate by one fixed Boolean vector. -/
def affine (sigma : E ≃ E) (delta chi : Valuation (E := E)) : Valuation (E := E) :=
  fun e => chi (sigma.symm e) + delta e

def affineEquiv (sigma : E ≃ E) (delta : Valuation (E := E)) :
    Valuation (E := E) ≃ Valuation (E := E) where
  toFun := affine sigma delta
  invFun chi e := chi (sigma e) - delta (sigma e)
  left_inv chi := by
    funext e
    simp [affine]
  right_inv chi := by
    funext e
    simp [affine]

theorem affine_flip (sigma : E ≃ E) (delta chi : Valuation (E := E)) (e : E) :
    affine sigma delta (flip chi e) = flip (affine sigma delta chi) (sigma e) := by
  funext d
  have he : sigma.symm d = e ↔ d = sigma e := by
    constructor
    · intro h
      simpa using congrArg sigma h
    · intro h
      rw [h, sigma.symm_apply_apply]
  simp only [affine, flip, he]
  ring

variable (G : EdgeGraph V E) (D : System V A)

/-- An affine lift of a base symmetry. Incidence equivariance is the explicit
edge-index formulation of the induced permutation of the manuscript's M. -/
def liftSymmetry (t : D.Symmetry) (sigma : E ≃ E)
    (incidence : ∀ e a b, G.Inc (sigma e) (t.perm a) (t.perm b) ↔ G.Inc e a b)
    (delta : Valuation (E := E)) : (G.cover D).Symmetry where
  perm := Equiv.prodCongr t.perm (affineEquiv sigma delta)
  step_iff := by
    intro p q x y
    change
      (G.LiftEdge (t.perm p.1, affine sigma delta p.2)
        (t.perm q.1, affine sigma delta q.2) ∧
        D.step (t.perm p.1, x) (t.perm q.1, y)) ↔
      (G.LiftEdge p q ∧ D.step (p.1, x) (q.1, y))
    constructor
    · rintro ⟨⟨e, hi, hv⟩, ht⟩
      refine ⟨⟨sigma.symm e, ?_, ?_⟩, t.step_iff.mp ht⟩
      · apply (incidence (sigma.symm e) p.1 q.1).mp
        simpa using hi
      · apply (affineEquiv sigma delta).injective
        change affine sigma delta q.2 = affine sigma delta (flip p.2 (sigma.symm e))
        rw [affine_flip, sigma.apply_symm_apply]
        exact hv
    · rintro ⟨⟨e, hi, hv⟩, ht⟩
      refine ⟨⟨sigma e, (incidence e p.1 q.1).mpr hi, ?_⟩, t.step_iff.mpr ht⟩
      change affine sigma delta q.2 = flip (affine sigma delta p.2) (sigma e)
      rw [hv, affine_flip]

@[simp] theorem lift_root (t : D.Symmetry) (sigma : E ≃ E)
    (incidence : ∀ e a b, G.Inc (sigma e) (t.perm a) (t.perm b) ↔ G.Inc e a b)
    (delta : Valuation (E := E)) (a : V) :
    (G.liftSymmetry D t sigma incidence delta).perm (a, 0) = (t.perm a, delta) := by
  apply Prod.ext
  · rfl
  · funext e
    simp [liftSymmetry, affineEquiv, affine]

/-- The unit translation supplies the incoming edge needed for extension. -/
theorem root_extension (t : D.Symmetry) (sigma : E ≃ E)
    (incidence : ∀ e a b, G.Inc (sigma e) (t.perm a) (t.perm b) ↔ G.Inc e a b)
    (a : V) (e : E) (edge : G.Inc e a (t.perm a))
    (x y : A) (point : D.step (t.perm a, x) (a, y)) :
    (G.liftSymmetry D t sigma incidence (flip 0 e)).map ((G.cover D).copy (a, 0) x) =
      (G.cover D).copy (a, 0) y := by
  apply System.Symmetry.extends_of_step
  rw [G.lift_root]
  refine ⟨⟨e, G.inc_symm edge, ?_⟩, point⟩
  exact (flip_flip 0 e).symm
end EdgeGraph
end GluingEPPA
