import GluingEPPA.Steiner.ChainValuation.AugmentedRecord
import GluingEPPA.Steiner.ChainValuation.WordAction

/-!
# The recorded chain-test coordinate is the left-to-right word action

The actual recursive valuation stores permutation coordinates using the
opposite group. This identifies that convention with the literal matching
word action of the chain, so that a moved chain endpoint can be used by the
nontriviality lemma in CycleUnwindingCore.
-/

namespace GluingEPPA.Steiner.EdgeGraph.AugmentedRecord

universe u q
variable {E : Type u} {J : Type q}
variable (X : J → Type q) (τ : ∀ j, E → Equiv.Perm (X j))

/-- Opposite multiplication in the permutation coordinate implements the
same left-to-right word convention as the chain's matching actions. -/
theorem testValue_eq_testWordPerm (j : J) (w : List E) :
    MulOpposite.unop (testValue X τ w j) =
      GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (τ j) w := by
  induction w with
  | nil =>
      ext x
      rfl
  | cons e w ih =>
      ext x
      have h := congrArg (fun f : Equiv.Perm (X j) => f (τ j e x)) ih
      simpa only [testValue, List.map_cons, List.prod_cons,
        MulOpposite.unop_mul, MulOpposite.unop_op, Equiv.Perm.mul_apply,
        GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm_cons]
        using h

end GluingEPPA.Steiner.EdgeGraph.AugmentedRecord
