import GluingEPPA.Steiner.ChainValuation.Matching

/-!
# Recursive state for an actual finite chain test

A state remembers the global labelled matchings together with a fixed final
Cayley block. The entry subset of that block records its overlap with the
previous block. Outside its own alphabet, a last-block point not in entry has
no global edge of that colour.
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
    exact hy.trans hz.symm

theorem matching_rel {e : E} (he : e ∈ B.active) (x : B.Carrier) :
    (B.matching e).Rel x (x * B.edge e) :=
  ⟨he, rfl⟩

theorem matching_perm {e : E} (he : e ∈ B.active) (x : B.Carrier) :
    (B.matching e).perm x = x * B.edge e :=
  (B.matching e).perm_eq_of_rel (B.matching_rel he x)

theorem matching_none {e : E} (he : e ∉ B.active) (x : B.Carrier) :
    ¬ ∃ y, (B.matching e).Rel x y := by
  rintro ⟨y, hy, _⟩
  exact he hy

end GroupBlock

/-- A partially built chain whose final block is B. -/
structure ChainState (E : Type u) (B : GroupBlock E) where
  Space : Type v
  [finiteSpace : Finite Space]
  lastEmbed : B.Carrier → Space
  lastInjective : Function.Injective lastEmbed
  entry : Set B.Carrier
  matching : E → Matching Space
  last_active : ∀ e ∈ B.active, ∀ g,
    (matching e).Rel (lastEmbed g) (lastEmbed (g * B.edge e))
  last_external : ∀ e ∉ B.active, ∀ g,
    g ∉ entry → ¬ ∃ y, (matching e).Rel (lastEmbed g) y

attribute [instance] ChainState.finiteSpace

namespace ChainState

def first (B : GroupBlock E) : ChainState E B where
  Space := B.Carrier
  finiteSpace := inferInstance
  lastEmbed := id
  lastInjective := Function.injective_id
  entry := ∅
  matching := B.matching
  last_active e he g := by simpa using B.matching_rel he g
  last_external e he g _ := B.matching_none he g

@[simp] theorem first_lastEmbed (B : GroupBlock E) (g : B.Carrier) :
    (first B).lastEmbed g = g := rfl

theorem first_perm (B : GroupBlock E) {e : E} (he : e ∈ B.active)
    (g : B.Carrier) :
    ((first B).matching e).perm g = g * B.edge e :=
  B.matching_perm he g

end ChainState
end GluingEPPA.Steiner.ChainValuation
