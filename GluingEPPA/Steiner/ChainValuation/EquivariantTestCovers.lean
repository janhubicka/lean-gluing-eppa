import GluingEPPA.Steiner.ChainValuation.WordAction

/-!
# Transferring the restricted word action through equivariant covers

The inclusion step of the recursive chain-valuation construction does
not require a *bijective* normal form merely to establish that a word
relation in K_M acts trivially on a larger chain test. It suffices to
cover the larger test by images of earlier tests in a way that
commutes with every M-letter permutation.

We prove that statement independently of the chain construction.
It leaves the existence of the required finite family of equivariant
covers as a separate, geometric obligation. No normal-form theorem or
higher acyclicity is asserted here.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u v w z
variable {E : Type u} {X : Type v} {Y : Type w}

/-- A map commuting with all selected letter permutations also commutes
with every word built from those letters, in the right-action word order
used by the recursive valuation construction. -/
theorem testWordPerm_map_of_generator_intertwining
    (σ : E → Equiv.Perm Y) (τ : E → Equiv.Perm X)
    (M : Finset E) (f : Y → X)
    (hmap : ∀ e, e ∈ M → ∀ y, f (σ e y) = τ e (f y))
    (word : List E) (hword : ∀ e ∈ word, e ∈ M) (y : Y) :
    f (testWordPerm σ word y) =
      testWordPerm τ word (f y) := by
  induction word generalizing y with
  | nil =>
      rfl
  | cons e rest ih =>
      have he : e ∈ M := hword e (by simp)
      have hrest : ∀ a ∈ rest, a ∈ M := by
        intro a ha
        exact hword a (by simp [ha])
      change
        f (testWordPerm σ rest (σ e y)) =
          testWordPerm τ rest (τ e (f y))
      calc
        f (testWordPerm σ rest (σ e y)) =
            testWordPerm τ rest (f (σ e y)) :=
              ih hrest (σ e y)
        _ = testWordPerm τ rest (τ e (f y)) := by
              rw [hmap e he y]

/-- A jointly surjective family of M-letter-equivariant maps from
earlier tests to a given test transfers every word equality.

The source tests may overlap and their maps need not be injective:
surjectivity of the *family*, not a component isomorphism, suffices
for the implication needed by recursive inclusion. -/
theorem testWordPerm_eq_of_joint_equivariant_cover
    {J : Type z} (W : J → Type w)
    (σ : ∀ j : J, E → Equiv.Perm (W j))
    (τ : E → Equiv.Perm X)
    (M : Finset E) (f : ∀ j : J, W j → X)
    (hcover : ∀ x : X, ∃ j : J, ∃ y : W j, f j y = x)
    (hmap : ∀ j e, e ∈ M → ∀ y,
      f j (σ j e y) = τ e (f j y))
    (p q : List E)
    (hp : ∀ e ∈ p, e ∈ M)
    (hq : ∀ e ∈ q, e ∈ M)
    (heq : ∀ j : J, testWordPerm (σ j) p =
      testWordPerm (σ j) q) :
    testWordPerm τ p = testWordPerm τ q := by
  ext x
  obtain ⟨j, y, rfl⟩ := hcover x
  calc
    testWordPerm τ p (f j y) =
        f j (testWordPerm (σ j) p y) :=
      (testWordPerm_map_of_generator_intertwining
        (σ j) τ M (f j) (hmap j) p hp y).symm
    _ = f j (testWordPerm (σ j) q y) := by
      exact congrArg (f j)
        (congrArg (fun g : Equiv.Perm (W j) => g y) (heq j))
    _ = testWordPerm τ q (f j y) :=
      testWordPerm_map_of_generator_intertwining
        (σ j) τ M (f j) (hmap j) q hq y

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
