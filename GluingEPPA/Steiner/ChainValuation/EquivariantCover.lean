import GluingEPPA.Steiner.ChainValuation.WordAction

/-!
# Equality of word actions from equivariant covers

For the inclusion step in the chain valuation, the strong geometric statement
"each restricted component is *isomorphic* to an earlier test" is more than
is needed to extend the action of the earlier group.

It suffices to cover the new test by equivariant maps from earlier test
spaces (including regular Cayley diagrams). Surjectivity plus preservation
of each allowed generator transfers every word equality.

No freeness, injectivity, disjointness, or inverse map is required of the
covering maps. The actual geometric construction of such covers remains the
separate chain-restriction obligation.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u v w z
variable {E : Type u} {X : Type v} {I : Type w} {Y : I → Type z}
variable {S : Finset E}

variable (τ : E → Equiv.Perm X)
variable (σ : ∀ i : I, E → Equiv.Perm (Y i))
variable (f : ∀ i : I, Y i → X)

/-- Letterwise equivariance transports every allowed word, in the same
left-to-right convention as the manuscript's valuation. -/
theorem equivariantCover_word
    (hletter : ∀ i e, e ∈ S → ∀ y, f i ((σ i e) y) = τ e (f i y))
    (i : I) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (y : Y i) :
    f i (testWordPerm (σ i) w y) =
      testWordPerm τ w (f i y) := by
  induction w generalizing y with
  | nil => rfl
  | cons e w ih =>
      have he : e ∈ S := hw e (by simp)
      have htail : ∀ a ∈ w, a ∈ S := fun a ha => hw a (by simp [ha])
      change f i (testWordPerm (σ i) w ((σ i e) y)) =
        testWordPerm τ w (τ e (f i y))
      calc
        f i (testWordPerm (σ i) w ((σ i e) y)) =
            testWordPerm τ w (f i ((σ i e) y)) :=
          ih htail ((σ i e) y)
        _ = testWordPerm τ w (τ e (f i y)) := by
          rw [hletter i e he y]

/-- Equality of word values in the earlier group is reflected on the whole
new test as soon as it has a surjective equivariant cover by earlier tests.

In particular there is no need to choose one 'preferred' point of a
component, or to prove an injective chart map merely for this step. -/
theorem testWordPerm_eq_of_equivariantCover
    (A : Data E S)
    (hcover : ∀ x : X, ∃ i : I, ∃ y : Y i, f i y = x)
    (hletter : ∀ i e, e ∈ S → ∀ y, f i ((σ i e) y) = τ e (f i y))
    (hmodels : ∀ i p q : List E,
      (∀ e ∈ p, e ∈ S) → (∀ e ∈ q, e ∈ S) →
      (p.map A.edge).prod = (q.map A.edge).prod →
      testWordPerm (σ i) p = testWordPerm (σ i) q)
    (p q : List E)
    (hp : ∀ e ∈ p, e ∈ S)
    (hq : ∀ e ∈ q, e ∈ S)
    (hvalue : (p.map A.edge).prod = (q.map A.edge).prod) :
    testWordPerm τ p = testWordPerm τ q := by
  ext x
  obtain ⟨i, y, rfl⟩ := hcover x
  have hP := equivariantCover_word τ σ f hletter i p hp y
  have hQ := equivariantCover_word τ σ f hletter i q hq y
  calc
    testWordPerm τ p (f i y) =
        f i (testWordPerm (σ i) p y) := hP.symm
    _ = f i (testWordPerm (σ i) q y) := by
      rw [hmodels i p q hp hq hvalue]
    _ = testWordPerm τ q (f i y) := hQ

/-- Construct the earlier group's actual right action on the new test
directly from an equivariant cover by earlier tests. -/
noncomputable def rightAction_of_equivariantCover
    (A : Data E S)
    (hcover : ∀ x : X, ∃ i : I, ∃ y : Y i, f i y = x)
    (hletter : ∀ i e, e ∈ S → ∀ y, f i ((σ i e) y) = τ e (f i y))
    (hmodels : ∀ i p q : List E,
      (∀ e ∈ p, e ∈ S) → (∀ e ∈ q, e ∈ S) →
      (p.map A.edge).prod = (q.map A.edge).prod →
      testWordPerm (σ i) p = testWordPerm (σ i) q) :
    RightAction A.Carrier X :=
  wordRightAction A τ
    (testWordPerm_eq_of_equivariantCover τ σ f A hcover hletter hmodels)

/-- The resulting action has precisely the intended named transitions. -/
theorem rightAction_of_equivariantCover_edge
    (A : Data E S)
    (hcover : ∀ x : X, ∃ i : I, ∃ y : Y i, f i y = x)
    (hletter : ∀ i e, e ∈ S → ∀ y, f i ((σ i e) y) = τ e (f i y))
    (hmodels : ∀ i p q : List E,
      (∀ e ∈ p, e ∈ S) → (∀ e ∈ q, e ∈ S) →
      (p.map A.edge).prod = (q.map A.edge).prod →
      testWordPerm (σ i) p = testWordPerm (σ i) q)
    (e : E) (he : e ∈ S) (x : X) :
    (rightAction_of_equivariantCover τ σ f A hcover hletter hmodels).act
        x (A.edge e) = τ e x :=
  wordRightAction_edge A τ
    (testWordPerm_eq_of_equivariantCover τ σ f A hcover hletter hmodels)
    e he x

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
