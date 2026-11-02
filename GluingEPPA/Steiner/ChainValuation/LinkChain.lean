import GluingEPPA.Steiner.RecursiveLinks
import GluingEPPA.Steiner.ChainValuation.ChainAttach
import GluingEPPA.Steiner.ChainValuation.ChainIndex
import GluingEPPA.Steiner.ChainValuation.ChainRestrictionCore

/-!
# Chain states from the actual recursive links

This file connects the generic chain-state construction to the verified Link
interface. Intersections use the already constructed proper stage at A ∩ B;
its two inclusion maps are the actual attachment maps.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open ChainValuation

def block (A : Proper S) : ChainValuation.GroupBlock E where
  Carrier := (old A).Carrier
  group := inferInstance
  finite := inferInstance
  active := (A.val : Set E)
  edge := (old A).edge
  square e _ := (old A).square e

def common (A B : Proper S) : Proper S :=
  Step.meet S A B

noncomputable def left (A B : Proper S) :
    (old (common S A B)).Carrier →* (old A).Carrier :=
  (L (common S A B) A Finset.inter_subset_left).incl

noncomputable def right (A B : Proper S) :
    (old (common S A B)).Carrier →* (old B).Carrier :=
  (L (common S A B) B Finset.inter_subset_right).incl

theorem left_injective (A B : Proper S) :
    Function.Injective (left D S old L A B) :=
  Link.injective D (old (common S A B)) (old A)
    Finset.inter_subset_left (L (common S A B) A Finset.inter_subset_left)

theorem right_injective (A B : Proper S) :
    Function.Injective (right D S old L A B) :=
  Link.injective D (old (common S A B)) (old B)
    Finset.inter_subset_right (L (common S A B) B Finset.inter_subset_right)

theorem shared_edge (A B : Proper S) (e : E)
    (heA : e ∈ A.val) (heB : e ∈ B.val) :
    ∃ k : (old (common S A B)).Carrier,
      left D S old L A B k = (old A).edge e ∧
      right D S old L A B k = (old B).edge e := by
  have he : e ∈ (common S A B).val := Finset.mem_inter.mpr ⟨heA, heB⟩
  refine ⟨(old (common S A B)).edge e, ?_, ?_⟩
  · exact (L (common S A B) A Finset.inter_subset_left).incl_edge e he
  · exact (L (common S A B) B Finset.inter_subset_right).incl_edge e he

abbrev Atom := ChainValuation.ChainAtom S old

/-- The paper's separation condition at one internal block. -/
def tripleSeparated (x y z : Atom S old) : Prop :=
  Disjoint
    (ChainValuation.leftCoset (right D S old L x.1 y.1).range 1)
    (ChainValuation.leftCoset (left D S old L y.1 z.1).range y.2)

/-- A partial construction, remembering enough information to check the next
internal separation condition. -/
structure BuildResult where
  previous : Option (Atom S old)
  current : Atom S old
  state : ChainValuation.ChainState E (block old current.1)
  entry_spec :
    match previous with
    | none => state.entry = ∅
    | some p => state.entry = Set.range (right D S old L p.1 current.1)

noncomputable def initial (x : Atom S old) : BuildResult D S old L where
  previous := none
  current := x
  state := ChainValuation.ChainState.first (block old x.1)
  entry_spec := rfl

/-- One left-to-right chain extension. For the first attachment there is no
separation condition; later steps use exactly the preceding triple. -/
noncomputable def step (R : BuildResult D S old L) (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y) :
    BuildResult D S old L := by
  let A := R.current.1
  let B := y.1
  let i := left D S old L A B
  let j := right D S old L A B
  have hi : Function.Injective i := left_injective D S old L A B
  have hj : Function.Injective j := right_injective D S old L A B
  have hdisj : Disjoint R.state.entry
      (ChainValuation.exitSet (block old A) R.current.2 i) := by
    cases hp : R.previous with
    | none =>
        have he : R.state.entry = ∅ := by
          simpa [hp] using R.entry_spec
        rw [he]
        exact Set.disjoint_empty_left
    | some p =>
        have he : R.state.entry =
            Set.range (right D S old L p.1 A) := by
          simpa [hp] using R.entry_spec
        have hs : tripleSeparated D S old L p R.current y := by
          simpa [hp] using hsep
        rw [he, ChainValuation.range_eq_leftCoset_one,
          ChainValuation.translated_range_eq_leftCoset]
        exact hs
  have hshared : ∀ e, e ∈ (block old A).active → e ∈ (block old B).active →
      ∃ k : (old (common S A B)).Carrier,
        i k = (block old A).edge e ∧ j k = (block old B).edge e := by
    intro e heA heB
    exact shared_edge D S old L A B e heA heB
  let Cnext := ChainValuation.extend (block old A) (block old B) R.state
    R.current.2 i j hi hj hdisj hshared
  exact
    { previous := some R.current
      current := y
      state := Cnext
      entry_spec := rfl }

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
