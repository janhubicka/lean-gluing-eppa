import GluingEPPA.Basic

namespace GluingEPPA
universe u v w z

/-- Symbols are indexed by their arity; tuples may have repeated coordinates. -/
structure RelStructure (L : Nat → Type u) (A : Type v) where
  rel : {n : Nat} → L n → (Fin n → A) → Prop

structure Embedding {L : Nat → Type u} {A : Type v} {B : Type w}
    (S : RelStructure L A) (T : RelStructure L B) where
  toFun : A → B
  injective : Function.Injective toFun
  rel_iff : ∀ {n} (r : L n) (x : Fin n → A),
    T.rel r (fun i => toFun (x i)) ↔ S.rel r x

namespace System
variable {L : Nat → Type u} {A : Type v} {V : Type w}
variable (D : System V A) (S : RelStructure L A)

/-- The quotient has exactly the tuples contributed by the original copies. -/
def quotientStructure : RelStructure L D.Realization where
  rel r q := ∃ a x, S.rel r x ∧ ∀ i, D.copy a (x i) = q i

/-- A complete compatibility condition, not an assumed EPPA theorem. -/
structure Compatible : Prop where
  injective : ∀ a, Function.Injective (D.copy a)
  relations : ∀ {n} (r : L n) (a b : V) (x y : Fin n → A),
    (∀ i, D.Connected (a, x i) (b, y i)) → (S.rel r x ↔ S.rel r y)

def embedding (h : D.Compatible S) (a : V) : Embedding S (D.quotientStructure S) where
  toFun := D.copy a
  injective := h.injective a
  rel_iff r x := by
    constructor
    · rintro ⟨b, y, hy, heq⟩
      exact (h.relations r b a y x (fun i => Quotient.exact (heq i))).mp hy
    · intro hx
      exact ⟨a, x, hx, fun _ => rfl⟩

/-- Any genuine realization supplies the compatibility of the free quotient. -/
theorem compatible_of_realization {B : Type z} (T : RelStructure L B)
    (rho : V → Embedding S T)
    (commute : ∀ {a b x y}, D.step (a, x) (b, y) →
      (rho a).toFun x = (rho b).toFun y) : D.Compatible S := by
  let F : D.Frame B := ⟨fun a => (rho a).toFun, fun a => (rho a).injective, commute⟩
  refine ⟨F.copy_injective, ?_⟩
  intro n r a b x y h
  have heq : (fun i => (rho a).toFun (x i)) = (fun i => (rho b).toFun (y i)) :=
    funext (fun i => F.path_value (h i))
  rw [← (rho a).rel_iff r x, ← (rho b).rel_iff r y, heq]

/-- A failure of the canonical map is a failure of injectivity or reflection.
The second alternative uses a family of assignments, not a pre-assumed function. -/
theorem obstruction (a : V)
    (h : ¬ (Function.Injective (D.copy a) ∧
      ∀ {n} (r : L n) (x : Fin n → A),
        (D.quotientStructure S).rel r (fun i => D.copy a (x i)) → S.rel r x)) :
    (∃ x y, x ≠ y ∧ D.Connected (a, x) (a, y)) ∨
    (∃ (n : Nat) (r : L n) (b : V) (x y : Fin n → A),
      ¬ S.rel r x ∧ S.rel r y ∧ ∀ i, D.Connected (a, x i) (b, y i)) := by
  classical
  by_cases hinj : Function.Injective (D.copy a)
  · right
    have hh : ¬ ∀ {n} (r : L n) (x : Fin n → A),
        (D.quotientStructure S).rel r (fun i => D.copy a (x i)) → S.rel r x :=
      fun hk => h ⟨hinj, hk⟩
    push Not at hh
    obtain ⟨n, r, x, hx, hn⟩ := hh
    obtain ⟨b, y, hy, heq⟩ := hx
    exact ⟨n, r, b, x, y, hn, hy, fun i => D.connected_symm (Quotient.exact (heq i))⟩
  · left
    simp only [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨x, y, heq, hne⟩ := hinj
    exact ⟨x, y, hne, Quotient.exact heq⟩
end System
end GluingEPPA
