import GluingEPPA.Steiner.ChainValuation.AugmentedFamilyData
import GluingEPPA.Steiner.ChainValuation.RecordedChainActions

/-!
# Actual earlier-stage actions on their recorded chain tests

The stage equation identifies the very same recursive group with the
augmented record containing these bounded tests.  Transport its literal
coordinate action along that equation.  No word-kernel compatibility is
assumed for the earlier group.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace AugmentedFamily

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (N : Nat) (S : Finset E)
variable (L : EarlierLinks D S (fun i => family D N i.val))

theorem recordedAction_exists
    (c : LinkChain.SeparatedChains D N S (fun i => family D N i.val) L) :
    ∃ B : RightAction (family D N S).Carrier
        (LinkChain.chainSpace D N S (fun i => family D N i.val) L c),
      ∀ e ∈ S, ∀ x, B.act x ((family D N S).edge e) =
        LinkChain.chainPerm D N S (fun i => family D N i.val) L c e x := by
  rw [family_eq_augmented D N S L]
  exact ⟨AugmentedStep.recordedTestAction D S (fun i => family D N i.val)
      (LinkChain.chainSpace D N S (fun i => family D N i.val) L)
      (LinkChain.chainPerm D N S (fun i => family D N i.val) L)
      (LinkChain.chainPerm_square D N S (fun i => family D N i.val) L) c,
    AugmentedStep.recordedTestAction_edge D S (fun i => family D N i.val)
      (LinkChain.chainSpace D N S (fun i => family D N i.val) L)
      (LinkChain.chainPerm D N S (fun i => family D N i.val) L)
      (LinkChain.chainPerm_square D N S (fun i => family D N i.val) L) c⟩

noncomputable def recordedAction
    (c : LinkChain.SeparatedChains D N S (fun i => family D N i.val) L) :
    RightAction (family D N S).Carrier
      (LinkChain.chainSpace D N S (fun i => family D N i.val) L c) :=
  Classical.choose (recordedAction_exists D N S L c)

theorem recordedAction_edge
    (c : LinkChain.SeparatedChains D N S (fun i => family D N i.val) L)
    (e : E) (he : e ∈ S)
    (x : LinkChain.chainSpace D N S (fun i => family D N i.val) L c) :
    (recordedAction D N S L c).act x ((family D N S).edge e) =
      LinkChain.chainPerm D N S (fun i => family D N i.val) L c e x :=
  Classical.choose_spec (recordedAction_exists D N S L c) e he x

end AugmentedFamily
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
