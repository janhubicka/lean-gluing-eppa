import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic

/-! Generic pullback presentations, stable quotients and surjective-natural
readouts. No affine or reduct-specific completion assumption is built in. -/
namespace GluingEPPA.Reducts.PullbackPresentations
universe u v w

structure Presentation where
  Obj : Type u → Type v
  pull : {X Y : Type u} → (X → Y) → Obj Y → Obj X
  pull_id : ∀ {X : Type u} (T : Obj X), pull (id : X → X) T = T
  pull_comp : ∀ {X Y Z : Type u} (f : X → Y) (g : Y → Z) (T : Obj Z),
    pull (g ∘ f) T = pull f (pull g T)

namespace Presentation
variable (P : Presentation.{u,v})
def IsEmbedding {X Y : Type u} (A : P.Obj X) (B : P.Obj Y) (f : X → Y) : Prop :=
  Function.Injective f ∧ P.pull f B = A

def IsInvariant {X : Type u} (T : P.Obj X) (h : Equiv.Perm X) : Prop :=
  P.pull h T = T

theorem embedding_comp {X Y Z : Type u} {A : P.Obj X} {B : P.Obj Y}
    {C : P.Obj Z} {f : X → Y} {g : Y → Z}
    (hf : P.IsEmbedding A B f) (hg : P.IsEmbedding B C g) :
    P.IsEmbedding A C (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  rw [P.pull_comp, hg.2, hf.2]

theorem equivariant_pullback {X Y : Type u} (p : X → Y) (g : Equiv.Perm X)
    (h : Equiv.Perm Y) (T : P.Obj Y)
    (heq : ∀ x, p (g x) = h (p x)) (hh : P.IsInvariant T h) :
    P.IsInvariant (P.pull p T) g := by
  change P.pull g (P.pull p T) = P.pull p T
  calc
    P.pull g (P.pull p T) = P.pull (p ∘ g) T := (P.pull_comp g p T).symm
    _ = P.pull (h ∘ p) T := congrArg (fun f => P.pull f T) (funext heq)
    _ = P.pull p (P.pull h T) := P.pull_comp p h T
    _ = P.pull p T := congrArg (P.pull p) hh

/-- This yields an induced section of a completed structure, not a free union. -/
theorem pullback_section {X Y T : Type u} (B : P.Obj Y)
    (r : X ↪ Y) (q : T → Y) (s : X → T) (hs : q ∘ s = r) :
    P.IsEmbedding (P.pull r B) (P.pull q B) s := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply r.injective
    calc
      r x = q (s x) := (congrFun hs x).symm
      _ = q (s y) := congrArg q hxy
      _ = r y := congrFun hs y
  · rw [← P.pull_comp, hs]
end Presentation

structure StableCongruence (P : Presentation.{u,v}) where
  rel : (X : Type u) → Setoid (P.Obj X)
  stable : ∀ {X Y : Type u} (f : X → Y) {a b : P.Obj Y},
    (rel Y).r a b → (rel X).r (P.pull f a) (P.pull f b)

namespace StableCongruence
variable {P : Presentation.{u,v}} (C : StableCongruence P)
def quotient : Presentation.{u,v} where
  Obj X := Quotient (C.rel X)
  pull f := Quotient.map (P.pull f) (fun _ _ h => C.stable f h)
  pull_id := by
    intro X T
    refine Quotient.inductionOn T ?_
    intro a
    change Quotient.mk (C.rel X) (P.pull id a) = Quotient.mk (C.rel X) a
    rw [P.pull_id]
  pull_comp := by
    intro X Y Z f g T
    refine Quotient.inductionOn T ?_
    intro a
    change Quotient.mk (C.rel X) (P.pull (g ∘ f) a) =
      Quotient.mk (C.rel X) (P.pull f (P.pull g a))
    rw [P.pull_comp]

theorem quotient_embedding {X Y : Type u} (a : P.Obj X) (b : P.Obj Y)
    (f : X → Y) :
    C.quotient.IsEmbedding (Quotient.mk (C.rel X) a)
      (Quotient.mk (C.rel Y) b) f ↔
      Function.Injective f ∧ (C.rel X).r (P.pull f b) a := by
  change (Function.Injective f ∧
    Quotient.mk (C.rel X) (P.pull f b) = Quotient.mk (C.rel X) a) ↔ _
  constructor
  · rintro ⟨hi, he⟩
    exact ⟨hi, Quotient.exact he⟩
  · rintro ⟨hi, he⟩
    exact ⟨hi, Quotient.sound he⟩
end StableCongruence

structure NaturalReduct (P : Presentation.{u,v}) (Q : Presentation.{u,w}) where
  interpret : {X : Type u} → P.Obj X → Q.Obj X
  natural : ∀ {X Y : Type u} (f : X → Y) (T : P.Obj Y),
    interpret (P.pull f T) = Q.pull f (interpret T)

namespace NaturalReduct
variable {P : Presentation.{u,v}} {Q : Presentation.{u,w}} (R : NaturalReduct P Q)
theorem embedding {X Y : Type u} {a : P.Obj X} {b : P.Obj Y} {f : X → Y}
    (hf : P.IsEmbedding a b f) : Q.IsEmbedding (R.interpret a) (R.interpret b) f := by
  refine ⟨hf.1, ?_⟩
  exact (R.natural f b).symm.trans (congrArg R.interpret hf.2)

theorem invariant {X : Type u} {T : P.Obj X} {h : Equiv.Perm X}
    (hh : P.IsInvariant T h) : Q.IsInvariant (R.interpret T) h := by
  exact (R.natural h T).symm.trans (congrArg R.interpret hh)
end NaturalReduct

/-- Only surjective naturality is needed for quantified readouts. -/
structure SurjectiveReduct (P : Presentation.{u,v}) (Q : Presentation.{u,w}) where
  interpret : {X : Type u} → P.Obj X → Q.Obj X
  natural : ∀ {X Y : Type u} (f : X → Y), Function.Surjective f →
    ∀ T : P.Obj Y, interpret (P.pull f T) = Q.pull f (interpret T)

namespace SurjectiveReduct
variable {P : Presentation.{u,v}} {Q : Presentation.{u,w}} (R : SurjectiveReduct P Q)
/-- H need preserve only the readout, not the source presentation. -/
theorem equivariant_readout {X Y : Type u} (p : X → Y)
    (hp : Function.Surjective p) (T : P.Obj Y)
    (g : Equiv.Perm X) (h : Equiv.Perm Y)
    (heq : ∀ x, p (g x) = h (p x))
    (hh : Q.IsInvariant (R.interpret T) h) :
    Q.IsInvariant (R.interpret (P.pull p T)) g := by
  rw [R.natural p hp]
  exact Q.equivariant_pullback p g h (R.interpret T) heq hh
end SurjectiveReduct

def relational (Symbol : Type v) (arity : Symbol → Nat) :
    Presentation.{u,max u v} where
  Obj X := (r : Symbol) → (Fin (arity r) → X) → Prop
  pull f T r t := T r (f ∘ t)
  pull_id := by intro X T; rfl
  pull_comp := by intro X Y Z f g T; rfl
end GluingEPPA.Reducts.PullbackPresentations
