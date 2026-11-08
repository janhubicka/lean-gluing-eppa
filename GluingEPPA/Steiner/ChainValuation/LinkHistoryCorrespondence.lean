import GluingEPPA.Steiner.ChainValuation.LinkHistoryList

/-!
# Historical coset construction agrees with literal LinkChain.buildNonempty

The heterogeneous component-history construction transports real
Cayley-block charts through a separate dependent record so that it
can remember their coset invariants. This module verifies that the
forgetful map recovers exactly the *original* finite-chain builder
of the manuscript, rather than a merely similar construction.

The previous history proofs and this correspondence are not
the global normalized proper-M component theorem.
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

/-- The two-block history is built on the exact original pair state. -/
theorem historyPair_result_eq
    (M : Proper S) (p c : Atom S old) :
    (historyPair D S old L M p c).result =
      pair D S old L p c := rfl

/-- Appending a block to a history does not alter its original
LinkChain.next state. -/
theorem historyNext_result_eq
    (M : Proper S) {p c : Atom S old}
    (H : HistoryPairResult D S old L M p c)
    (z : Atom S old)
    (hsep : tripleSeparated D S old L p c z) :
    (historyNext D S old L M H z hsep).result =
      next D S old L H.result z hsep := rfl

/-- Forgetting the finite historical charts after an arbitrary
tail gives exactly the same dependent SomeState as the manuscript's
original chain builder, with identical quotient and last block. -/
theorem historyBuildTail_result_eq
    (M : Proper S) (p c : Atom S old)
    (H : HistoryPairResult D S old L M p c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (historyBuildTail D S old L M p c H rest hsep).result =
      buildTail D S old L p c H.result rest hsep := by
  induction rest generalizing p c with
  | nil =>
      rfl
  | cons z zs ih =>
      have htriple : tripleSeparated D S old L p c z := hsep.1
      have htail : separatedList D S old L (c :: z :: zs) := hsep.2
      change
        (historyBuildTail D S old L M c z
          (historyNext D S old L M H z htriple) zs htail).result =
        buildTail D S old L c z
          (next D S old L H.result z htriple) zs htail
      exact ih c z (historyNext D S old L M H z htriple) htail

/-- The all-block component history is a genuine *refinement*
of the existing separated-chain realization on every nonempty
list, not an independent model with possibly different points. -/
theorem historyBuildNonempty_result_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (historyBuildNonempty D S old L M atoms hne hsep).result =
      buildNonempty D S old L atoms hne hsep := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          rfl
      | cons y ys =>
          change
            (historyBuildTail D S old L M x y
              (historyPair D S old L M x y) ys hsep).result =
            buildTail D S old L x y
              (pair D S old L x y) ys hsep
          exact historyBuildTail_result_eq D S old L M
            x y (historyPair D S old L M x y) ys hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
