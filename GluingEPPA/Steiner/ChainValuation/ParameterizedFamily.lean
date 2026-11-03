import GluingEPPA.Steiner.ChainValuation.AugmentedStep

/-!
# A recursive valuation family parameterized by finite test packages

At every subset S, a test package may depend on the already constructed proper
stages. The generic recursion packages those tests into RecursiveRecord.Data.
No chain-specific compatibility or endpoint-repair theorem is assumed here.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}

/-- Extra finite involutive permutation coordinates for one recursive stage. -/
structure TestPackage (E : Type u) (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) where
  J : Type u
  [finiteJ : Finite J]
  X : J → Type u
  [finiteX : ∀ j, Finite (X j)]
  τ : ∀ j, E → Equiv.Perm (X j)
  square : ∀ j e, τ j e * τ j e = 1

attribute [instance] TestPackage.finiteJ TestPackage.finiteX

variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (tests : ∀ (S : Finset E) (old : ∀ i : Proper S, Data E i.val),
  TestPackage E S old)

/-- One stage using the supplied package after all proper stages are fixed. -/
noncomputable def parameterizedStep (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) : Data E S :=
  let P := tests S old
  AugmentedStep.data D S old P.X P.τ P.square

/-- The same well-founded subset recursion as the manuscript, with arbitrary
finite involutive tests appended at every stage. -/
noncomputable def parameterizedFamily (S : Finset E) : Data E S :=
  parameterizedStep D tests S (fun i => parameterizedFamily i.val)
termination_by S.card
decreasing_by exact Finset.card_lt_card i.property

theorem parameterizedFamily_step (S : Finset E) :
    parameterizedFamily D tests S =
      parameterizedStep D tests S (fun i => parameterizedFamily D tests i.val) := by
  rw [parameterizedFamily]

/-- Finiteness is part of the Data interface at every recursive stage. -/
theorem parameterizedFamily_finite (S : Finset E) :
    Finite (parameterizedFamily D tests S).Carrier :=
  inferInstance

/-- Every element of every parameterized stage is represented by an allowed
word in its named generators. -/
theorem parameterizedFamily_generated (S : Finset E)
    (g : (parameterizedFamily D tests S).Carrier) :
    ∃ w : List E, (∀ e ∈ w, e ∈ S) ∧
      (w.map (parameterizedFamily D tests S).edge).prod = g :=
  (parameterizedFamily D tests S).generated g

theorem parameterizedFamily_square (S : Finset E) (e : E) :
    (parameterizedFamily D tests S).edge e *
      (parameterizedFamily D tests S).edge e = 1 :=
  (parameterizedFamily D tests S).square e

end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
