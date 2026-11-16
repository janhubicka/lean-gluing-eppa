import Mathlib.Data.Fin.Basic

/-! Same-domain relational interpretations commute with surjective pullback,
including quantifiers. Equality is absent; repeated variables, negation,
quantifiers and nullary symbols remain. No geometric realization is assumed. -/
namespace GluingEPPA.Reducts.EqualityFreePullback
universe u v w
variable {R : Type u} (arity : R → Nat)
abbrev Table (X : Type v) := (r : R) → (Fin (arity r) → X) → Prop
inductive Formula : Nat → Type u
  | atom {n : Nat} (r : R) (args : Fin (arity r) → Fin n) : Formula n
  | falsum {n : Nat} : Formula n
  | imp {n : Nat} (p q : Formula n) : Formula n
  | all {n : Nat} (p : Formula (n+1)) : Formula n
  | ex {n : Nat} (p : Formula (n+1)) : Formula n
variable {arity}
def eval {X : Type v} (M : Table arity X) :
    {n : Nat} → Formula arity n → (Fin n → X) → Prop
  | _, .atom r args, env => M r (env ∘ args)
  | _, .falsum, _ => False
  | _, .imp p q, env => eval M p env → eval M q env
  | _, .all p, env => ∀ x, eval M p (Fin.cases x env)
  | _, .ex p, env => ∃ x, eval M p (Fin.cases x env)
def pullback {X : Type v} {Y : Type w} (M : Table arity X) (p : Y → X) : Table arity Y :=
  fun r t => M r (p ∘ t)

theorem map_extend {X : Type v} {Y : Type w} {n : Nat}
    (p : Y → X) (y : Y) (env : Fin n → Y) :
    p ∘ Fin.cases y env = Fin.cases (p y) (p ∘ env) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The complete equality-free first-order truth lemma, in both directions. -/
theorem eval_pullback {X : Type v} {Y : Type w}
    (M : Table arity X) (p : Y → X) (hp : Function.Surjective p) :
    ∀ {n : Nat} (f : Formula arity n) (env : Fin n → Y),
      eval (pullback M p) f env ↔ eval M f (p ∘ env) := by
  intro n f
  induction f with
  | atom r args => intro env; rfl
  | falsum => intro env; rfl
  | imp f g ihf ihg =>
    intro env
    exact imp_congr (ihf env) (ihg env)
  | all f ih =>
    intro env
    constructor
    · intro h x
      obtain ⟨y,rfl⟩ := hp x
      simpa only [map_extend] using (ih (Fin.cases y env)).1 (h y)
    · intro h y
      apply (ih (Fin.cases y env)).2
      simpa only [map_extend] using h (p y)
  | ex f ih =>
    intro env
    constructor
    · rintro ⟨y,hy⟩
      exact ⟨p y, by simpa only [map_extend] using (ih (Fin.cases y env)).1 hy⟩
    · rintro ⟨x,hx⟩
      obtain ⟨y,rfl⟩ := hp x
      exact ⟨y, (ih (Fin.cases y env)).2 (by simpa only [map_extend] using hx)⟩

abbrev Theory := Set (Formula arity 0)
def Models {X : Type v} (M : Table arity X) (T : Theory (arity := arity)) : Prop :=
  ∀ f, f ∈ T → eval M f (fun i => Fin.elim0 i)

theorem models_pullback {X : Type v} {Y : Type w}
    (M : Table arity X) (p : Y → X) (hp : Function.Surjective p)
    (T : Theory (arity := arity)) : Models (pullback M p) T ↔ Models M T := by
  have he : p ∘ (fun i : Fin 0 => Fin.elim0 i) = (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  constructor
  · intro h f hf
    have ht := (eval_pullback M p hp f (fun i => Fin.elim0 i)).1 (h f hf)
    simpa only [he] using ht
  · intro h f hf
    apply (eval_pullback M p hp f (fun i => Fin.elim0 i)).2
    simpa only [he] using h f hf

variable {Q : Type u} {qarity : Q → Nat}
abbrev Interpretation := (q : Q) → Formula arity (qarity q)
def interpret {X : Type v} (I : Interpretation (arity := arity) (qarity := qarity))
    (M : Table arity X) : Table qarity X := fun q t => eval M (I q) t

theorem interpretation_pullback {X : Type v} {Y : Type w}
    (I : Interpretation (arity := arity) (qarity := qarity))
    (M : Table arity X) (p : Y → X) (hp : Function.Surjective p) :
    interpret I (pullback M p) = pullback (interpret I M) p := by
  funext q t
  exact propext (eval_pullback M p hp (I q) t)

def Preserves {X : Type v} (M : Table arity X) (h : X → X) : Prop :=
  ∀ r t, M r (h ∘ t) ↔ M r t
def Induces {X : Type v} {Y : Type w}
    (M : Table arity X) (N : Table arity Y) (j : Y → X) : Prop :=
  ∀ r t, M r (j ∘ t) ↔ N r t

/-- Only reduct preservation is assumed; h need not preserve the presentation. -/
theorem interpreted_action {X : Type v} {Y : Type w}
    (I : Interpretation (arity := arity) (qarity := qarity))
    (M : Table arity X) (p : Y → X) (hp : Function.Surjective p)
    (g : Y → Y) (h : X → X) (heq : ∀ y, p (g y) = h (p y))
    (hh : Preserves (interpret I M) h) : Preserves (interpret I (pullback M p)) g := by
  rw [interpretation_pullback I M p hp]
  intro r t
  change interpret I M r (p ∘ (g ∘ t)) ↔ interpret I M r (p ∘ t)
  have ht : p ∘ (g ∘ t) = h ∘ (p ∘ t) := funext (fun i => heq (t i))
  rw [ht]
  exact hh r (p ∘ t)

theorem theory_and_interpretation {X : Type v} {Y : Type w}
    (I : Interpretation (arity := arity) (qarity := qarity))
    (M : Table arity X) (p : Y → X) (hp : Function.Surjective p)
    (T : Theory (arity := arity)) :
    (Models (pullback M p) T ↔ Models M T) ∧
      interpret I (pullback M p) = pullback (interpret I M) p :=
  ⟨models_pullback M p hp T, interpretation_pullback I M p hp⟩
end GluingEPPA.Reducts.EqualityFreePullback
