import GluingEPPA.Relational

namespace GluingEPPA
universe u v w z
namespace System
variable {L : Nat → Type u} {A : Type v} {V : Type w} {U : Type z}
variable (D : System V A) (S : RelStructure L A) (F : D.Frame U)

/-- Every edge transports each tuple on which all coordinates are defined. -/
def RespectsRelations : Prop :=
  ∀ {n} (r : L n) (a b : V) (x y : Fin n → A),
    (∀ i, D.step (a, x i) (b, y i)) → (S.rel r x ↔ S.rel r y)

/-- A supported base edge occurs on a transport from each initial coordinate.
Reverse occurrences are included using symmetry of the transport relation. -/
def Available {n : Nat} (a : V) (x : Fin n → A) (b c : V) : Prop :=
  ∀ i, ∃ y z, D.Connected (a, x i) (b, y) ∧ D.step (b, y) (c, z)

/-- Simultaneous replay on a common supported base walk. This is the induction
inside the free-realization proof, including its domain check. -/
theorem replay {n : Nat} (r : L n) (a b : V) (x y : Fin n → A)
    (respect : D.RespectsRelations S)
    (walk : Relation.ReflTransGen (D.Available a x) a b)
    (ends : ∀ i, D.Connected (a, x i) (b, y i)) : S.rel r x ↔ S.rel r y := by
  classical
  have build : ∃ t : Fin n → A,
      (∀ i, D.Connected (a, x i) (b, t i)) ∧ (S.rel r x ↔ S.rel r t) := by
    induction walk with
    | refl => exact ⟨x, fun _ => .refl, Iff.rfl⟩
    | @tail b c walk available ih =>
      obtain ⟨t, paths, ht⟩ := ih
      choose v z hv hz using available
      have heq : ∀ i, t i = v i := fun i => F.path_unique (paths i) (hv i)
      have edges : ∀ i, D.step (b, t i) (c, z i) := by
        intro i
        rw [heq i]
        exact hz i
      exact ⟨z, fun i => (paths i).tail (edges i), ht.trans (respect r b c t z edges)⟩
  obtain ⟨t, paths, ht⟩ := build
  have heq : t = y := funext (fun i => F.path_unique (paths i) (ends i))
  simpa only [heq] using ht
end System
end GluingEPPA
