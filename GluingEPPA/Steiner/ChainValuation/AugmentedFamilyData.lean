import GluingEPPA.Steiner.ChainValuation.LinkUniqueness
import GluingEPPA.Steiner.ChainValuation.ChainTests
import GluingEPPA.Steiner.ChainValuation.AugmentedLinks

/-!
# The actual recursive family with bounded chain coordinates

The existing well-founded record recursion accepts test packages for
arbitrary predecessor data.  Use all bounded chain tests whenever those
predecessors admit Links, with an empty package otherwise.  Link uniqueness
makes the chosen package independent of the selected witnesses.

The subsequent link induction proves that every actual recursive stage
uses the chain package.  The empty branch only makes the package function
total on arbitrary inputs to the generic recursor.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace AugmentedFamily

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

def emptyTests (S : Finset E) (old : ∀ i : Proper S, Data E i.val) :
    TestPackage E S old where
  J := PEmpty
  finiteJ := inferInstance
  X := fun _ => PUnit
  finiteX := fun _ => inferInstance
  τ := fun _ _ => Equiv.refl _
  square := by intros; rfl

/-- The concrete package function used by the existing subset recursion. -/
noncomputable def tests (N : Nat) (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) : TestPackage E S old :=
  if h : Nonempty (EarlierLinks D S old) then
    LinkChain.testPackage D N S old (Classical.choice h)
  else emptyTests S old

theorem tests_eq (N : Nat) (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) (L : EarlierLinks D S old) :
    tests D N S old = LinkChain.testPackage D N S old L := by
  have h : Nonempty (EarlierLinks D S old) := ⟨L⟩
  rw [tests, dite_eq_left h]
  exact congrArg (LinkChain.testPackage D N S old) (Subsingleton.elim _ _)

/-- One family on actual edge subsets, with exactly the generic
well-founded recursion's carriers, generators, and finiteness proofs. -/
noncomputable def family (N : Nat) (S : Finset E) : Data E S :=
  parameterizedFamily D (tests D N) S

theorem family_step (N : Nat) (S : Finset E) :
    family D N S = parameterizedStep D (tests D N) S
      (fun i => family D N i.val) :=
  parameterizedFamily_step D (tests D N) S

/-- When the actual proper predecessors have Links, this is precisely
the stage recording every bounded separated chain built from them. -/
theorem family_eq_augmented (N : Nat) (S : Finset E)
    (L : EarlierLinks D S (fun i => family D N i.val)) :
    family D N S =
      AugmentedStep.data D S (fun i => family D N i.val)
        (LinkChain.chainSpace D N S (fun i => family D N i.val) L)
        (LinkChain.chainPerm D N S (fun i => family D N i.val) L)
        (LinkChain.chainPerm_square D N S (fun i => family D N i.val) L) := by
  rw [family_step]
  unfold parameterizedStep
  rw [tests_eq D N S (fun i => family D N i.val) L]
  rfl

/-- The original component coordinate survives every augmentation. -/
noncomputable def componentAction (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) (P : TestPackage E S old) (i : Proper S) :
    RightAction (AugmentedStep.data D S old P.X P.τ P.square).Carrier
      (Step.components D S old i) :=
  (Step.action D S old i).comap (AugmentedStep.forget D S old P.X P.τ P.square)

theorem componentAction_edge (S : Finset E)
    (old : ∀ i : Proper S, Data E i.val) (P : TestPackage E S old) (i : Proper S)
    (e : E) (he : e ∈ S) (c : Step.components D S old i) :
    (componentAction D S old P i).act c
      ((AugmentedStep.data D S old P.X P.τ P.square).edge e) =
      D.componentEdgePerm (Step.sets S i) (Step.edges S old i)
        (Step.involutions S old i) e c := by
  change (Step.action D S old i).act c
    (AugmentedStep.forget D S old P.X P.τ P.square
      ((AugmentedStep.data D S old P.X P.τ P.square).edge e)) = _
  rw [AugmentedStep.forget_edge, Step.action_edge D S old i e he c]

/-- Every earlier component action is supplied by its actual augmented
record, even before the new inclusion Links are constructed. -/
theorem family_component_action (N : Nat) (T S : Finset E) (hTS : T ⊂ S) :
    ∃ A : RightAction (family D N S).Carrier
      (D.Component (T : Set E) (family D N T).edge (fun e _ => (family D N T).square e)),
      ∀ e ∈ S, ∀ c, A.act c ((family D N S).edge e) =
        D.componentEdgePerm (T : Set E) (family D N T).edge
          (fun e _ => (family D N T).square e) e c := by
  rw [family_step]
  let old : ∀ i : Proper S, Data E i.val := fun i => family D N i.val
  let P := tests D N S old
  exact ⟨componentAction D S old P ⟨T, hTS⟩,
    componentAction_edge D S old P ⟨T, hTS⟩⟩

end AugmentedFamily
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
