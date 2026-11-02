import GluingEPPA.Steiner.RightAction
import GluingEPPA.Steiner.RecursiveRecord

/-!
# Right actions reconstructed from word-kernel compatibility

If a finite test cannot distinguish two allowed words with the same value in
an earlier recursive group, then the whole earlier group acts on that test.
This is the interface needed by augmented inclusion.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u v
variable {E : Type u} {X : Type v}

/-- Read test letters from left to right. -/
def testWordPerm (τ : E → Equiv.Perm X) : List E → Equiv.Perm X
  | [] => Equiv.refl _
  | e :: w => (τ e).trans (testWordPerm τ w)

@[simp] theorem testWordPerm_nil (τ : E → Equiv.Perm X) (x : X) :
    testWordPerm τ [] x = x := rfl

@[simp] theorem testWordPerm_cons (τ : E → Equiv.Perm X)
    (e : E) (w : List E) (x : X) :
    testWordPerm τ (e :: w) x = testWordPerm τ w (τ e x) := rfl

theorem testWordPerm_append (τ : E → Equiv.Perm X)
    (p q : List E) (x : X) :
    testWordPerm τ (p ++ q) x =
      testWordPerm τ q (testWordPerm τ p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih =>
      simpa only [List.cons_append, testWordPerm_cons] using ih (τ e x)

variable {S : Finset E} (A : Data E S) (τ : E → Equiv.Perm X)
variable (hker : ∀ p q : List E,
  (∀ e ∈ p, e ∈ S) → (∀ e ∈ q, e ∈ S) →
  (p.map A.edge).prod = (q.map A.edge).prod →
  testWordPerm τ p = testWordPerm τ q)

noncomputable def chosenWord (g : A.Carrier) : List E :=
  Classical.choose (A.generated g)

theorem chosenWord_letters (g : A.Carrier) :
    ∀ e ∈ chosenWord A g, e ∈ S :=
  (Classical.choose_spec (A.generated g)).1

theorem chosenWord_value (g : A.Carrier) :
    ((chosenWord A g).map A.edge).prod = g :=
  (Classical.choose_spec (A.generated g)).2

/-- The action obtained from any chosen allowed word for the group element. -/
noncomputable def wordActionValue (x : X) (g : A.Carrier) : X :=
  testWordPerm τ (chosenWord A g) x

include hker

theorem wordActionValue_word (w : List E) (hw : ∀ e ∈ w, e ∈ S)
    (x : X) :
    wordActionValue A τ x ((w.map A.edge).prod) =
      testWordPerm τ w x := by
  unfold wordActionValue
  have heq := hker (chosenWord A ((w.map A.edge).prod)) w
    (chosenWord_letters A _) hw
    ((chosenWord_value A _).trans rfl)
  exact DFunLike.congr_fun heq x

/-- Kernel compatibility is exactly what is needed to reconstruct a right
action of the earlier group on the test. -/
noncomputable def wordRightAction : RightAction A.Carrier X where
  act := wordActionValue A τ
  one x := by
    have h := wordActionValue_word A τ hker [] (by simp) x
    simpa using h
  mul x g h := by
    obtain ⟨p, hp, rfl⟩ := A.generated g
    obtain ⟨q, hq, rfl⟩ := A.generated h
    have hpq : ∀ e ∈ p ++ q, e ∈ S := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hp e he
      · exact hq e he
    rw [wordActionValue_word A τ hker p hp,
      wordActionValue_word A τ hker q hq,
      ← testWordPerm_append]
    have hprod :
        (p.map A.edge).prod * (q.map A.edge).prod =
          ((p ++ q).map A.edge).prod := by simp
    rw [hprod, wordActionValue_word A τ hker (p ++ q) hpq]

theorem wordRightAction_edge (e : E) (he : e ∈ S) (x : X) :
    (wordRightAction A τ hker).act x (A.edge e) = τ e x := by
  change wordActionValue A τ x (A.edge e) = τ e x
  have h := wordActionValue_word A τ hker [e] (by
    intro f hf
    have hfe : f = e := by simpa using hf
    simpa [hfe] using he) x
  simpa using h

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
