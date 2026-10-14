import GluingEPPA.Sparsening.OddBoundary

/-! The endpoint-cochain cancellation used in the coherent affine lift.
This is an algebraic identity, not an assumption of coherent EPPA. -/
namespace GluingEPPA.Sparsening
universe u
variable {E : Type u}

def coordinateMap (sigma : E ≃ E) (v : E → ZMod 2) : E → ZMod 2 :=
  fun e => v (sigma.symm e)

def chartTranslation (sigma : E ≃ E) (etaD etaR : E → ZMod 2) : E → ZMod 2 :=
  etaR + coordinateMap sigma etaD

/-- First sigma, then tau; the intermediate endpoint cochain cancels. -/
theorem chartTranslation_comp (sigma tau : E ≃ E)
    (etaD etaR etaT : E → ZMod 2) :
    chartTranslation tau etaR etaT +
        coordinateMap tau (chartTranslation sigma etaD etaR) =
      chartTranslation (sigma.trans tau) etaD etaT := by
  funext e
  change (etaT e + etaR (tau.symm e)) +
      (etaR (tau.symm e) + etaD (sigma.symm (tau.symm e))) =
    etaT e + etaD (sigma.symm (tau.symm e))
  calc
    (etaT e + etaR (tau.symm e)) +
        (etaR (tau.symm e) + etaD (sigma.symm (tau.symm e))) =
      etaT e + (etaR (tau.symm e) + etaR (tau.symm e)) +
        etaD (sigma.symm (tau.symm e)) := by abel
    _ = etaT e + etaD (sigma.symm (tau.symm e)) := by
      rw [bit_add_self, add_zero]

theorem chartTranslation_identity (eta : E → ZMod 2) :
    chartTranslation (Equiv.refl E) eta eta = 0 := by
  funext e
  change eta e + eta e = 0
  exact bit_add_self (eta e)

end GluingEPPA.Sparsening
