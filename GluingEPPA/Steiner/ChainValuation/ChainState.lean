import GluingEPPA.Steiner.ChainValuation.Matching

/-!
# Recursive state for an actual finite chain test

A state remembers the global labelled matchings together with the final Cayley
block. The entry subset of the last block records its overlap with the
previous block. Outside its own alphabet, a last-block point not in entry
has no global edge of that colour. This is the invariant needed to attach
the next block under the separation condition.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u}

/-- One finite Cayley block with individually named involutive generators. -/
structure GroupBlock (E : Type u) where
  Carrier : Type v
  [group : Group Carrier]
  [finite : Finite Carrier]
  active : Set E
  edge : E → Carrier
  square : ∀ e ∈ active, edge e * edge e = 1

attribute [instance] GroupBlock.group GroupBlock.finite

namespace GroupBlock

variable (B : GroupBlock E)

/-- The labelled Cayley edge relation of one block. -/
def edgeRel (e : E) (x y : B.Carrier) : Prop :=
  e ∈ B.active ∧ y = x * B.edge e

def matching (e : E) : Matching B.Carrier where
  Rel := B.edgeRel e
  symm := by
    rintro x y ⟨he, rfl⟩
    refine ⟨he, ?_⟩
    rw [mul_assoc, B.square e he, mul_one]
  unique := by
    rintro x y z ⟨_, hy⟩ ⟨_, hz⟩
    exact hy.symm.trans hz

theorem matching_rel {e : E} (he : e ∈ B.active) (x : B.Carrier) :
    (B.matching e).Rel x (x * B.edge e) :=
  ⟨he, rfl⟩

theorem matching_perm {e : E} (he : e ∈ B.active) (x : B.Carrier) :
    (B.matching e).perm x = x * B.edge e :=
  Matching.perm_eq_of_rel (B.matching_rel he x)

theorem matching_none {e : E} (he : e ∉ B.active) (x : B.Carrier) :
    ¬ ∃ y, (B.matching e).Rel x y := by
  rintro ⟨y, hy, _⟩
  exact he hy

end GroupBlock

/-- A partially built chain test with its global labelled matchings. -/
structure ChainState (E : Type u) where
  Space : Type v
  [finiteSpace : Finite Space]
  last : GroupBlock E
  lastEmbed : last.Carrier → Space
  lastInjective : Function.Injective lastEmbed
  entry : Set last.Carrier
  matching : E → Matching Space
  last_active : ∀ e ∈ last.active, ∀ g,
    (matching e).Rel (lastEmbed g) (lastEmbed (g * last.edge e))
  last_external : ∀ e ∉ last.active, ∀ g,
    g ∉ entry → ¬ ∃ y, (matching e).Rel (lastEmbed g) y

attribute [instance] ChainState.finiteSpace

namespace ChainState

/-- A one-block chain. -/
def first (B : GroupBlock E) : ChainState E where
  Space := B.Carrier
  finiteSpace := inferInstance
  last := B
  lastEmbed := id
  lastInjective := Function.injective_id
  entry := ∅
  matching := B.matching
  last_active e he g := by
    simpa using B.matching_rel he g
  last_external e he g _ := B.matching_none he g

@[simp] theorem first_lastEmbed (B : GroupBlock E) (g : B.Carrier) :
    (first B).lastEmbed g = g := rfl

theorem first_perm (B : GroupBlock E) {e : E} (he : e ∈ B.active)
    (g : B.Carrier) :
    ((first B).matching e).perm g = g * B.edge e :=
  B.matching_perm he g

end ChainState
end GluingEPPA.Steiner.ChainValuation
