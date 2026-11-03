import GluingEPPA.Steiner.ChainValuation.AugmentedRecord

/-!
# The word contradiction at the end of chain unwinding

The finite chain test is recorded as an actual permutation coordinate of the
augmented valuation. If a closed cycle word evaluates to the identity, it
fixes every test point. Hence an unrolled chain on which that word moves an
endpoint contradicts the identity relation. The combinatorial construction
of the moving chain endpoint is a separate obligation.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u
variable {G : Type u} [Group G]

/-- The product of successive differences telescopes even in noncommutative
groups. The last point is included explicitly. -/
def differenceProduct (first : G) : List G → G
  | [] => 1
  | next :: rest => (first⁻¹ * next) * differenceProduct next rest

theorem differenceProduct_to_last (first last : G) (middle : List G) :
    differenceProduct first (middle ++ [last]) = first⁻¹ * last := by
  induction middle generalizing first with
  | nil =>
      simp [differenceProduct]
  | cons next rest ih =>
      change (first⁻¹ * next) * differenceProduct next (rest ++ [last]) =
        first⁻¹ * last
      rw [ih]
      group

/-- The cyclic product of consecutive transport values is always the identity. -/
theorem differenceProduct_cycle (first : G) (middle : List G) :
    differenceProduct first (middle ++ [first]) = 1 := by
  rw [differenceProduct_to_last]
  group

end GluingEPPA.Steiner.ChainValuation

namespace GluingEPPA.Steiner.EdgeGraph.AugmentedRecord

universe u v w z q
variable {V : Type u} {E : Type v} {I : Type z} {J : Type q}
variable (D : EdgeGraph V E) (T : I → Set E) (K : I → Type w)
variable [∀ i, Group (K i)]
variable (a : ∀ i, E → K i)
variable (ha : ∀ i e, e ∈ T i → a i e * a i e = 1)
variable (X : J → Type q) (τ : ∀ j, E → Equiv.Perm (X j))
variable (hsquare : ∀ j e, τ j e * τ j e = 1)

/-- A word representing the identity in the augmented group fixes all points
of every recorded chain test. No faithful action assumption is required. -/
theorem valuation_one_test_fixed (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (j : J) (x : X j)
    (hval : valuation D T K a ha X τ hsquare S w hw = 1) :
    MulOpposite.unop (testValue X τ w j) x = x := by
  have h := congrArg
    (fun g : imageGroup D T K a ha X τ hsquare S =>
      MulOpposite.unop (g.val.2 j) x) hval
  change MulOpposite.unop (testValue X τ w j) x = x at h
  exact h

/-- A single moved endpoint witnesses that the word is nontrivial. -/
theorem moved_test_implies_nontrivial (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (j : J) (x : X j)
    (hmoves : MulOpposite.unop (testValue X τ w j) x ≠ x) :
    valuation D T K a ha X τ hsquare S w hw ≠ 1 := by
  intro hval
  exact hmoves (valuation_one_test_fixed D T K a ha X τ hsquare
    S w hw j x hval)

/-- The last step of the bounded-cycle contradiction: if the cycle word has
identity value, the included chain test cannot move its starting point. -/
theorem impossible_identity_cycle_test (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (j : J) (x : X j)
    (hword : (w.map (totalGenerator D T K a ha X τ hsquare S)).prod = 1)
    (hmoves : MulOpposite.unop (testValue X τ w j) x ≠ x) : False := by
  have hval : valuation D T K a ha X τ hsquare S w hw =
      (w.map (totalGenerator D T K a ha X τ hsquare S)).prod := by
    apply Subtype.ext
    exact (totalGenerator_product D T K a ha X τ hsquare S w hw).symm
  exact moved_test_implies_nontrivial D T K a ha X τ hsquare
    S w hw j x hmoves (hval.trans hword)

end GluingEPPA.Steiner.EdgeGraph.AugmentedRecord
