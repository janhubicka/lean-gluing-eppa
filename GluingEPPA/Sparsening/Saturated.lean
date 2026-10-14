import GluingEPPA.Cover

/-!
Foundations of saturated Boolean sparsening. The index type parametrizes
actual induced copies, not merely selected generator maps. The system
includes every overlap between different charts. No sparsening or clique
faithfulness assumption is hidden in these definitions.
-/
namespace GluingEPPA
namespace Sparsening
universe u v w z
variable {L : Nat → Type u} {A : Type v} {B : Type w} {V : Type z}
variable {S : RelStructure L A} {T : RelStructure L B}

/-- All actual overlaps of the specified chart embeddings. -/
def saturated (rho : V → Embedding S T) : System V A where
  step p q := p.1 ≠ q.1 ∧ (rho p.1).toFun p.2 = (rho q.1).toFun q.2
  reverse h := ⟨Ne.symm h.1, h.2.symm⟩

/-- The ambient structure supplies the faithful empty-language frame. -/
def frame (rho : V → Embedding S T) : (saturated rho).Frame B where
  value a := (rho a).toFun
  injective a := (rho a).injective
  commute h := h.2

/-- Full overlap relations, including the empty-tuple case. -/
theorem respects (rho : V → Embedding S T) :
    (saturated rho).RespectsRelations S := by
  intro n r a b x y h
  have heq : (fun i => (rho a).toFun (x i)) =
      (fun i => (rho b).toFun (y i)) := funext (fun i => (h i).2)
  rw [← (rho a).rel_iff r x, ← (rho b).rel_iff r y, heq]

end Sparsening

namespace System.Frame
universe u v w z
variable {V : Type u} {A : Type v} {B : Type w}
variable {D : System V A} (F : D.Frame B)

/-- The projection remembers the actual ambient point of each germ. -/
def projection : D.Realization → B :=
  Quotient.lift (fun p => F.value p.1 p.2) (fun _ _ h => F.path_value h)

@[simp] theorem projection_copy (a : V) (x : A) :
    F.projection (D.copy a x) = F.value a x := rfl

/-- A projection is a homomorphism whenever the frames are relational charts.
The conclusion deliberately does not assert global injectivity. -/
theorem projection_rel {L : Nat → Type z} (S : RelStructure L A)
    (T : RelStructure L B)
    (charts : ∀ {n} (r : L n) a (x : Fin n → A),
      T.rel r (fun i => F.value a (x i)) ↔ S.rel r x)
    {n : Nat} (r : L n) (q : Fin n → D.Realization)
    (h : (D.quotientStructure S).rel r q) :
    T.rel r (fun i => F.projection (q i)) := by
  obtain ⟨a, x, hx, heq⟩ := h
  have heq' : (fun i => F.projection (q i)) =
      (fun i => F.value a (x i)) := by
    funext i
    rw [← heq i, projection_copy]
  rw [heq']
  exact (charts r a x).mpr hx

end System.Frame

namespace Sparsening
universe u v w z t
variable {L : Nat → Type u} {A : Type v} {B : Type w}
variable {V : Type z} {E : Type t}
variable {S : RelStructure L A} {T : RelStructure L B}

/-- The general Boolean realization has induced copies for the saturated data.
The new clique-containment conclusion still requires the affine Helly proof. -/
theorem saturated_cover_compatible (rho : V → Embedding S T)
    (G : EdgeGraph V E) [DecidableEq E] [Fintype E] :
    (G.cover (saturated rho)).Compatible S :=
  G.cover_compatible (saturated rho) S (frame rho) (respects rho)

end Sparsening
end GluingEPPA
