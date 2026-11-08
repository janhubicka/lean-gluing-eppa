import GluingEPPA.Steiner.DiagramRelabellingComposition

/-!
# The coherent EPPA extension formula on the Steiner free quotient

The concrete maps are the valuation-prefix automorphisms P_U and
the quotient relabellings F_sigma. The extension for a partial map
from U to W is P_W ∘ F_sigma ∘ P_U. The middle involutions cancel
for composable partial maps; no commutation assumption between P
and F is needed.

This checks the algebraic coherence of the final formula. Construction
of the specific finite closed-subsystem diagram and of the coherent
order-preserving-complement extensions sigma_f is separate.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- The extension formula, acting first by the source prefix,
then by relabelling, and finally by the target prefix. -/
noncomputable def extensionMap (L : LabelledSteiner D Ω)
    (kU kW : (family D Finset.univ).Carrier)
    (t : LabelledSymmetry D L) : Equiv.Perm (realizedPoint D L) :=
  ((realizedDeck D L kU).trans (relabelPointEquiv D L t)).trans
    (realizedDeck D L kW)

/-- The identity restriction extends to the identity whenever its
source and target use the same involutive prefix. -/
theorem extensionMap_id (L : LabelledSteiner D Ω)
    (kU : (family D Finset.univ).Carrier) (hk : kU * kU = 1) :
    extensionMap D L kU kU (LabelledSymmetry.id D L) =
      Equiv.refl (realizedPoint D L) := by
  apply Equiv.ext
  intro p
  change (realizedDeck D L kU)
    ((relabelPointEquiv D L (LabelledSymmetry.id D L))
      ((realizedDeck D L kU) p)) = p
  rw [relabelPointEquiv_id]
  exact realizedDeck_involutive D L kU hk p

/-- The central P_W maps cancel in the composition of extensions.
The remaining quotient relabellings compose by naturality. -/
theorem extensionMap_comp (L : LabelledSteiner D Ω)
    (kU kW kT : (family D Finset.univ).Carrier)
    (f g : LabelledSymmetry D L) (hkW : kW * kW = 1) :
    (extensionMap D L kU kW f).trans (extensionMap D L kW kT g) =
      extensionMap D L kU kT (LabelledSymmetry.trans D L f g) := by
  apply Equiv.ext
  intro p
  change (realizedDeck D L kT)
    ((relabelPointEquiv D L g)
      ((realizedDeck D L kW)
        ((realizedDeck D L kW)
          ((relabelPointEquiv D L f) ((realizedDeck D L kU) p))))) =
    (realizedDeck D L kT)
      ((relabelPointEquiv D L (LabelledSymmetry.trans D L f g))
        ((realizedDeck D L kU) p))
  rw [realizedDeck_involutive D L kW hkW]
  rw [relabelPointEquiv_trans]
  rfl

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
