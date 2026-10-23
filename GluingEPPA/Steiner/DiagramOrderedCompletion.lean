import GluingEPPA.Steiner.DiagramCoherentFormula

/-!
# Increasing bijections between complements of finite ordered subsets

The coherent extension of a partial bijection in the Steiner proof
uses the unique increasing bijection between the complements of its
domain and image. Any two composable increasing bijections between
finite linear orders compose to the unique increasing bijection between
their outer endpoints. This avoids an explicit permutation case split.

The following lemmas are unconditional mathematics, not assumptions
about EPPA witnesses or about the existence of coherent completions.
-/

namespace GluingEPPA.Steiner.OrderedCompletion

universe u v w

/-- The increasing bijection between equinumerous finite linear orders. -/
noncomputable def increasingIso (A : Type u) (B : Type v)
    [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    (h : Fintype.card A = Fintype.card B) : A ≃o B :=
  (monoEquivOfFin A rfl).symm.trans
    (monoEquivOfFin B h.symm)

/-- An increasing bijection of a finite linear order to itself is the identity. -/
theorem increasingIso_refl (A : Type u) [Fintype A] [LinearOrder A] :
    increasingIso A A rfl = OrderIso.refl A := by
  classical
  exact Subsingleton.elim _ _

/-- Increasing bijections compose exactly. -/
theorem increasingIso_trans (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [LinearOrder A]
    [Fintype B] [LinearOrder B]
    [Fintype C] [LinearOrder C]
    (hAB : Fintype.card A = Fintype.card B)
    (hBC : Fintype.card B = Fintype.card C) :
    (increasingIso A B hAB).trans (increasingIso B C hBC) =
      increasingIso A C (hAB.trans hBC) := by
  classical
  exact Subsingleton.elim _ _

variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]

/-- The unique increasing bijection between the complements of the
domain and image of a finite partial bijection. -/
noncomputable def complementIso (U W : Finset A)
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W}) :
    {x : A // x ∉ U} ≃o {x : A // x ∉ W} := by
  classical
  have hcard : Fintype.card {x : A // x ∉ U} =
      Fintype.card {x : A // x ∉ W} :=
    Fintype.card_compl_eq_card_compl
      (p := fun x : A => x ∈ U)
      (q := fun x : A => x ∈ W)
      (Fintype.card_congr f)
  exact increasingIso _ _ hcard

/-- The increasing complement map for an identity is the identity. -/
theorem complementIso_refl (U : Finset A) :
    complementIso U U (Equiv.refl {x : A // x ∈ U}) =
      OrderIso.refl {x : A // x ∉ U} := by
  classical
  exact Subsingleton.elim _ _

/-- The increasing maps on complements compose exactly for any
composable pair of finite partial bijections. -/
theorem complementIso_trans (U W T : Finset A)
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (g : {x : A // x ∈ W} ≃ {x : A // x ∈ T}) :
    (complementIso U W f).trans (complementIso W T g) =
      complementIso U T (f.trans g) := by
  classical
  exact Subsingleton.elim _ _

end GluingEPPA.Steiner.OrderedCompletion
