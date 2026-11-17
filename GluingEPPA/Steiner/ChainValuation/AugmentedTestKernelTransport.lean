import GluingEPPA.Steiner.ChainValuation.AugmentedRecord

/-!
# Transport of the added finite test coordinates under relabelling

The augmented valuation records a permutation for every finite test.  Once
each source test has an equivariant target test, equality of all recorded
word permutations is invariant under relabelling.  This bridge does not
assume naturality of the recursive family: the missing geometric task is
to construct the coordinate maps from actual relabelled chain tests.
-/

namespace GluingEPPA.Steiner.EdgeGraph.AugmentedRecord

universe u
variable {E E' J J' : Type u}
variable {X : J → Type u} {X' : J' → Type u}

/-- A relabelling of test indices and letters, and a homomorphism between
each test-permutation coordinate which respects every named letter. -/
theorem testValue_coordinate_transport
    (p : E ≃ E') (q : J ≃ J')
    (τ : ∀ j : J, E → Equiv.Perm (X j))
    (τ' : ∀ j' : J', E' → Equiv.Perm (X' j'))
    (F : ∀ j : J,
      (Equiv.Perm (X j))ᵐᵒᵖ →*
        (Equiv.Perm (X' (q j)))ᵐᵒᵖ)
    (hF : ∀ j e, F j (MulOpposite.op (τ j e)) =
      MulOpposite.op (τ' (q j) (p e)))
    (w : List E) (j : J) :
    F j (testValue X τ w j) =
      testValue X' τ' (w.map p) (q j) := by
  induction w with
  | nil =>
      simp [testValue]
  | cons e w ih =>
      change F j (MulOpposite.op (τ j e) * testValue X τ w j) =
        MulOpposite.op (τ' (q j) (p e)) *
          testValue X' τ' (w.map p) (q j)
      rw [map_mul, hF j e, ih]

/-- When every coordinate transport is injective and all target tests are
relabelled source tests, the finite-test word kernel is exactly invariant.
This is the test-coordinate half of the augmented naturality induction. -/
theorem testValue_kernel_iff
    (p : E ≃ E') (q : J ≃ J')
    (τ : ∀ j : J, E → Equiv.Perm (X j))
    (τ' : ∀ j' : J', E' → Equiv.Perm (X' j'))
    (F : ∀ j : J,
      (Equiv.Perm (X j))ᵐᵒᵖ →*
        (Equiv.Perm (X' (q j)))ᵐᵒᵖ)
    (hF : ∀ j e, F j (MulOpposite.op (τ j e)) =
      MulOpposite.op (τ' (q j) (p e)))
    (hInj : ∀ j, Function.Injective (F j))
    (w v : List E) :
    testValue X τ w = testValue X τ v ↔
      testValue X' τ' (w.map p) = testValue X' τ' (v.map p) := by
  constructor
  · intro hw
    funext j'
    obtain ⟨j, rfl⟩ := q.surjective j'
    calc
      testValue X' τ' (w.map p) (q j) =
          F j (testValue X τ w j) :=
            (testValue_coordinate_transport p q τ τ' F hF w j).symm
      _ = F j (testValue X τ v j) := congrArg (F j) (congrFun hw j)
      _ = testValue X' τ' (v.map p) (q j) :=
            testValue_coordinate_transport p q τ τ' F hF v j
  · intro hw
    funext j
    apply hInj j
    calc
      F j (testValue X τ w j) =
          testValue X' τ' (w.map p) (q j) :=
            testValue_coordinate_transport p q τ τ' F hF w j
      _ = testValue X' τ' (v.map p) (q j) := congrFun hw (q j)
      _ = F j (testValue X τ v j) :=
            (testValue_coordinate_transport p q τ τ' F hF v j).symm

end GluingEPPA.Steiner.EdgeGraph.AugmentedRecord
