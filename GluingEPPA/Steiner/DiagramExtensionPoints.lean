import GluingEPPA.Steiner.DiagramPartialSite

/-!
# What the coherent extension formula does to a represented point

The action of P_W ∘ F_sigma ∘ P_U on a local representative is a
one-line calculation: an involutive source prefix first returns the
valuation coordinate to 1, the relabelling changes its site and point
label, and the target prefix installs the target valuation coordinate.

This lemma separates the algebraic calculation from the later question
which particular sites represent a closed source and target subsystem.
No form of EPPA is assumed.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- The concrete three-factor extension formula, evaluated on the
source subsystem's representative with its prescribed prefix. -/
theorem extensionMap_on_local_point
    (L : LabelledSteiner D Ω)
    (kU kW : (family D Finset.univ).Carrier)
    (t : LabelledSymmetry D L) (hkU : kU * kU = 1)
    (sU sW : V) (hs : t.graph.vertex sU = sW)
    (x y : Ω) (hx : L.present sU x) (hy : L.present sW y)
    (hxy : t.labels x = y) :
    (extensionMap D L kU kW t)
      (canonicalPoint D L sU kU x hx) =
       canonicalPoint D L sW kW y hy := by
  change canonicalPoint D L (t.graph.vertex sU)
    (kW * relabelValuation D L t (kU * kU)) (t.labels x)
      ((t.present sU x).2 hx) =
    canonicalPoint D L sW kW y hy
  rw [hkU, map_one, mul_one]
  cases hs
  cases hxy
  rfl

/-- Equivalent formulation when the original embedding is represented
by a point in the source local system and a point in the target. -/
theorem extensionMap_of_representatives
    (L : LabelledSteiner D Ω)
    (kU kW : (family D Finset.univ).Carrier)
    (t : LabelledSymmetry D L) (hkU : kU * kU = 1)
    (sU sW : V) (hs : t.graph.vertex sU = sW)
    (x y : Ω) (hx : L.present sU x) (hy : L.present sW y)
    (hxy : t.labels x = y)
    (a b : realizedPoint D L)
    (ha : a = canonicalPoint D L sU kU x hx)
    (hb : b = canonicalPoint D L sW kW y hy) :
    (extensionMap D L kU kW t) a = b := by
  rw [ha, hb]
  exact extensionMap_on_local_point D L kU kW t hkU
    sU sW hs x y hx hy hxy

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
