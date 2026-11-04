import GluingEPPA.Steiner.ChainValuation.LinkStepCoset

/-!
# Last-block coset induction through the actual finite chain builder

The generic one-step theorem is now applied recursively to the
`LinkChain.pair`, `LinkChain.next`, `LinkChain.buildTail`
and `LinkChain.buildNonempty` functions from the original
separated-chain test construction. The separation witnesses are
the ones already supplied by `separatedList`.

This proves the last-block M-component invariant for every
finite nonempty separated chain, not yet the normalized
proper-alphabet component chart.
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

open GluingEPPA.Steiner.ChainValuation

/-- The last-block invariant for a completed partial chain package. -/
def SomeStateLastCoset (M : Proper S) (R : SomeState S old) : Prop :=
  LastBlockCosetInvariant (block S old R.current.1) R.state M.val
    (restrictedSubgroup D S old L M R.current.1)

/-- The first actual two-block chain inherits the invariant. -/
theorem pair_lastCoset (M : Proper S) (x y : Atom S old) :
    LastBlockCosetInvariant (block S old y.1)
      (pair D S old L x y).state M.val
      (restrictedSubgroup D S old L M y.1) := by
  have hfirst := initial_lastMaskCoset D S old L M x
  have hstep := step_lastMaskCoset D S old L M
    (initial D S old L x) y trivial hfirst
  exact hstep

/-- One further actual attached block preserves the invariant,
using precisely the previous triple's separation witness. -/
theorem next_lastCoset (M : Proper S) {p c : Atom S old}
    (R : PairResult D S old L p c) (z : Atom S old)
    (hsep : tripleSeparated D S old L p c z)
    (hR : LastBlockCosetInvariant (block S old c.1)
      R.state M.val (restrictedSubgroup D S old L M c.1)) :
    LastBlockCosetInvariant (block S old z.1)
      (next D S old L R z hsep).state M.val
      (restrictedSubgroup D S old L M z.1) := by
  let BR : BuildResult D S old L :=
    { previous := some p
      current := c
      state := R.state
      entry_spec := R.entry_spec }
  have hb : LastMaskCoset D S old L M BR := hR
  have hn := step_lastMaskCoset D S old L M BR z
    (by simpa using hsep) hb
  exact hn

/-- Iterated preservation along the actual list-of-blocks recursor. -/
theorem buildTail_lastCoset (M : Proper S) :
    ∀ (rest : List (Atom S old)) (p c : Atom S old)
      (R : PairResult D S old L p c)
      (hsep : separatedList D S old L (p :: c :: rest)),
      LastBlockCosetInvariant (block S old c.1) R.state M.val
        (restrictedSubgroup D S old L M c.1) →
      SomeStateLastCoset D S old L M
        (buildTail D S old L p c R rest hsep) := by
  intro rest
  induction rest with
  | nil =>
      intro p c R hsep hR
      exact hR
  | cons z zs ih =>
      intro p c R hsep hR
      have ht : tripleSeparated D S old L p c z := hsep.1
      have htail : separatedList D S old L (c :: z :: zs) := hsep.2
      have hn := next_lastCoset D S old L M R z ht hR
      exact ih c z (next D S old L R z ht) htail hn

/-- Every nonempty separated chain in the actual earlier-stage
construction satisfies the last-block coset invariant. -/
theorem buildNonempty_lastCoset
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    SomeStateLastCoset D S old L M
      (buildNonempty D S old L atoms hne hsep) := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact initial_lastMaskCoset D S old L M x
      | cons y ys =>
          have hp := pair_lastCoset D S old L M x y
          exact buildTail_lastCoset D S old L M ys x y
            (pair D S old L x y) hsep hp

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
