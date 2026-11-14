import Init

/-!
A four-point obstruction to extending a partial involution of a semigeneric
multipartite tournament to an involution of any larger such tournament.

The ambient carrier is arbitrary: no finiteness assumption is used. The
rectangle axiom below is equality of the two row-agreement bits; for Boolean
orientations it is exactly even rectangular parity. Repeated rows/columns
are harmless. All structure axioms of the concrete input are checked below.
This file uses Lean core only, independently of the Part II development.
-/

namespace GluingEPPA.Reducts.SemigenericObstruction

universe u

structure Semigeneric (V : Type u) where
  part : V → V → Prop
  part_refl : ∀ x, part x x
  part_symm : ∀ x y, part x y → part y x
  part_trans : ∀ x y z, part x y → part y z → part x z
  edge : V → V → Bool
  within : ∀ x y, part x y → edge x y = false
  reverse : ∀ x y, ¬ part x y → edge y x = !(edge x y)
  rectangle : ∀ x x' y y', part x x' → part y y' → ¬ part x y →
    (edge x y == edge x' y) = (edge x y' == edge x' y')

structure Embedding {U : Type} {V : Type u}
    (A : Semigeneric U) (B : Semigeneric V) where
  map : U → V
  injective : ∀ x y, map x = map y → x = y
  part_iff : ∀ x y, B.part (map x) (map y) ↔ A.part x y
  edge_eq : ∀ x y, B.edge (map x) (map y) = A.edge x y

/-- An involution of a multipartite tournament cannot exchange parts. -/
theorem involution_fixes_parts {V : Type u} (S : Semigeneric V)
    (f : V → V) (h2 : ∀ x, f (f x) = x)
    (hEdge : ∀ x y, S.edge (f x) (f y) = S.edge x y) :
    ∀ x, S.part x (f x) := by
  intro x
  classical
  by_cases hp : S.part x (f x)
  · exact hp
  · have hforward := hEdge x (f x)
    rw [h2 x] at hforward
    have hreverse := S.reverse x (f x) hp
    have hbad : Bool.not (S.edge x (f x)) = S.edge x (f x) :=
      hreverse.symm.trans hforward
    cases hv : S.edge x (f x) <;> simp [hv] at hbad

/-- The required three-row partial map cannot stabilize the outside part.
No involutivity is used in this lemma. -/
theorem pattern_forces_part_movement {V : Type u} (S : Semigeneric V)
    (a b c v : V) (f : V → V)
    (hEdge : ∀ x y, S.edge (f x) (f y) = S.edge x y)
    (hb : f b = a) (hc : f c = c)
    (hac : S.part a c) (hav : ¬ S.part a v)
    (hea : S.edge a v = true) (heb : S.edge b v = false)
    (hec : S.edge c v = true) : ¬ S.part v (f v) := by
  intro hv
  have hrowa : S.edge a (f v) = false := by
    simpa only [hb, heb] using hEdge b v
  have hrowc : S.edge c (f v) = true := by
    simpa only [hc, hec] using hEdge c v
  have hrect := S.rectangle a c v (f v) hac hv hav
  simp [hea, hec, hrowa, hrowc] at hrect

/-- The ambient obstruction, with its exact hypotheses exposed. -/
theorem no_involution_on_pattern {V : Type u} (S : Semigeneric V)
    (a b c v : V) (f : V → V)
    (h2 : ∀ x, f (f x) = x)
    (hEdge : ∀ x y, S.edge (f x) (f y) = S.edge x y)
    (hb : f b = a) (hc : f c = c)
    (hac : S.part a c) (hav : ¬ S.part a v)
    (hea : S.edge a v = true) (heb : S.edge b v = false)
    (hec : S.edge c v = true) : False := by
  exact pattern_forces_part_movement S a b c v f hEdge hb hc hac hav hea heb hec
    (involution_fixes_parts S f h2 hEdge v)

inductive Four where
  | a | b | c | v
  deriving DecidableEq, Repr

namespace Four

def outer : Four → Bool
  | v => true
  | _ => false

def part (x y : Four) : Prop := outer x = outer y

def edge : Four → Four → Bool
  | a, v => true
  | c, v => true
  | v, b => true
  | _, _ => false

/-- All equivalence, orientation and parity laws of the four-point input. -/
def model : Semigeneric Four where
  part := part
  part_refl := fun _ => rfl
  part_symm := fun _ _ h => h.symm
  part_trans := fun _ _ _ h k => h.trans k
  edge := edge
  within := by
    intro x y h
    cases x <;> cases y <;> simp_all [part, outer, edge]
  reverse := by
    intro x y h
    cases x <;> cases y <;> simp_all [part, outer, edge]
  rectangle := by
    intro x x' y y' hxx hyy hxy
    cases x <;> cases x' <;> cases y <;> cases y' <;>
      simp_all [part, outer, edge]

inductive Domain where
  | a | b | c
  deriving DecidableEq, Repr

def inclusion : Domain → Four
  | Domain.a => Four.a
  | Domain.b => Four.b
  | Domain.c => Four.c

def swap : Domain → Domain
  | Domain.a => Domain.b
  | Domain.b => Domain.a
  | Domain.c => Domain.c

theorem swap_involutive : ∀ x, swap (swap x) = x := by
  intro x
  cases x <;> rfl

/-- The local swap is an isomorphism of the actual induced domain. -/
theorem swap_preserves : ∀ x y,
    (part (inclusion (swap x)) (inclusion (swap y)) ↔
      part (inclusion x) (inclusion y)) ∧
    edge (inclusion (swap x)) (inclusion (swap y)) =
      edge (inclusion x) (inclusion y) := by
  intro x y
  cases x <;> cases y <;> simp [part, outer, edge, inclusion, swap]

end Four

/-- The concrete input has no involutive extension of its local swap,
in any finite or infinite semigeneric extension. -/
theorem four_no_involutive_extension {V : Type u} (S : Semigeneric V)
    (e : Embedding Four.model S) (f : V → V)
    (h2 : ∀ x, f (f x) = x)
    (hEdge : ∀ x y, S.edge (f x) (f y) = S.edge x y)
    (hb : f (e.map Four.b) = e.map Four.a)
    (hc : f (e.map Four.c) = e.map Four.c) : False := by
  have hac : S.part (e.map Four.a) (e.map Four.c) :=
    (e.part_iff Four.a Four.c).2 rfl
  have hav : ¬ S.part (e.map Four.a) (e.map Four.v) := by
    intro h
    have h' := (e.part_iff Four.a Four.v).1 h
    change false = true at h'
    cases h'
  exact no_involution_on_pattern S (e.map Four.a) (e.map Four.b)
    (e.map Four.c) (e.map Four.v) f h2 hEdge hb hc hac hav
    (e.edge_eq Four.a Four.v) (e.edge_eq Four.b Four.v)
    (e.edge_eq Four.c Four.v)

/-- A homomorphic action of the two-element local group would give an
involution. Thus no coherent choice of extensions can exist. -/
theorem four_no_coherent_C2_lift {V : Type u} (S : Semigeneric V)
    (e : Embedding Four.model S) (F : Bool → V → V)
    (hzero : ∀ x, F false x = x)
    (hcomp : ∀ g h x, F (Bool.xor g h) x = F g (F h x))
    (hEdge : ∀ x y, S.edge (F true x) (F true y) = S.edge x y)
    (hb : F true (e.map Four.b) = e.map Four.a)
    (hc : F true (e.map Four.c) = e.map Four.c) : False := by
  have h2 : ∀ x, F true (F true x) = x := by
    intro x
    calc
      F true (F true x) = F (Bool.xor true true) x := (hcomp true true x).symm
      _ = x := hzero x
  exact four_no_involutive_extension S e (F true) h2 hEdge hb hc

#print axioms involution_fixes_parts
#print axioms pattern_forces_part_movement
#print axioms no_involution_on_pattern
#print axioms Four.model
#print axioms Four.swap_involutive
#print axioms Four.swap_preserves
#print axioms four_no_involutive_extension
#print axioms four_no_coherent_C2_lift

end GluingEPPA.Reducts.SemigenericObstruction
