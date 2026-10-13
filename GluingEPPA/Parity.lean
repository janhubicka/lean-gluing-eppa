import GluingEPPA.Basic

namespace GluingEPPA
universe u v

/-- Edge-indexed undirected graph; the parity lemma also permits loops. -/
structure EdgeGraph (V : Type u) (E : Type v) where
  left : E → V
  right : E → V

namespace EdgeGraph
variable {V : Type u} {E : Type v} (G : EdgeGraph V E)
abbrev Valuation := E → ZMod 2

def Inc (e : E) (a b : V) : Prop :=
  (a = G.left e ∧ b = G.right e) ∨ (a = G.right e ∧ b = G.left e)

theorem inc_symm {e a b} (h : G.Inc e a b) : G.Inc e b a := by
  rcases h with ⟨h, k⟩ | ⟨h, k⟩
  · exact Or.inr ⟨k, h⟩
  · exact Or.inl ⟨k, h⟩

theorem two_zero : (2 : ZMod 2) = 0 := by decide

variable [DecidableEq E]
def flip (chi : Valuation (E := E)) (e : E) : Valuation (E := E) :=
  fun d => chi d + if d = e then 1 else 0

theorem flip_flip (chi : Valuation (E := E)) (e : E) : flip (flip chi e) e = chi := by
  funext d
  by_cases h : d = e <;> norm_num [flip, h, add_assoc] <;> exact two_zero

def LiftEdge (p q : V × Valuation (E := E)) : Prop :=
  ∃ e, G.Inc e p.1 q.1 ∧ q.2 = flip p.2 e

theorem liftEdge_symm {p q} (h : G.LiftEdge p q) : G.LiftEdge q p := by
  obtain ⟨e, he, hq⟩ := h
  refine ⟨e, G.inc_symm he, ?_⟩
  rw [hq, flip_flip]

variable [Fintype E]
def dot (w chi : Valuation (E := E)) : ZMod 2 := ∑ e, w e * chi e

theorem dot_flip (w chi : Valuation (E := E)) (e : E) :
    dot w (flip chi e) = dot w chi + w e := by
  simp [dot, flip, mul_add, mul_ite, Finset.sum_add_distrib]

def weight (c : V → ZMod 2) (e : E) : ZMod 2 := c (G.left e) + c (G.right e)
def potential (c : V → ZMod 2) (p : V × Valuation (E := E)) : ZMod 2 :=
  c p.1 + dot (G.weight c) p.2

theorem step_potential (c : V → ZMod 2) {p q} (h : G.LiftEdge p q) :
    G.potential c p = G.potential c q := by
  obtain ⟨e, he, hq⟩ := h
  rcases he with ⟨hp, ht⟩ | ⟨hp, ht⟩
  · simp only [potential, hq, dot_flip, weight, hp, ht]
    ring_nf <;> simp only [two_zero, mul_zero, add_zero]
  · simp only [potential, hq, dot_flip, weight, hp, ht]
    ring_nf <;> simp only [two_zero, mul_zero, add_zero]

theorem path_potential (c : V → ZMod 2) {p q}
    (h : Relation.ReflTransGen G.LiftEdge p q) : G.potential c p = G.potential c q := by
  induction h with
  | refl => rfl
  | tail _ e ih => exact ih.trans (G.step_potential c e)

def SupportAdj (chi psi : Valuation (E := E)) (a b : V) : Prop :=
  ∃ e, chi e ≠ psi e ∧ G.Inc e a b

/-- Odd support connects the projected endpoints. This is a base walk,
not a lift with prescribed terminal valuation. -/
theorem support_reachable {a b : V} {chi psi : Valuation (E := E)}
    (h : Relation.ReflTransGen G.LiftEdge (a, chi) (b, psi)) :
    Relation.ReflTransGen (G.SupportAdj chi psi) a b := by
  classical
  by_contra hn
  let reach (v : V) : Prop := Relation.ReflTransGen (G.SupportAdj chi psi) a v
  let c (v : V) : ZMod 2 := if reach v then 0 else 1
  have ha : c a = 0 := by simp [c, reach, Relation.ReflTransGen.refl]
  have hb : c b = 1 := by simp [c, reach, hn]
  have hw : ∀ e, chi e ≠ psi e → G.weight c e = 0 := by
    intro e he
    have hr : reach (G.left e) ↔ reach (G.right e) := by
      constructor
      · intro hp
        exact hp.tail ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
      · intro hp
        exact hp.tail ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩
    by_cases hl : reach (G.left e)
    · have ht := hr.mp hl
      simp [weight, c, hl, ht]
    · have ht : ¬ reach (G.right e) := fun h => hl (hr.mpr h)
      norm_num [weight, c, hl, ht]
      exact two_zero
  have hd : dot (G.weight c) chi = dot (G.weight c) psi := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : chi e = psi e
    · rw [he]
    · rw [hw e he]
      simp
  have hp := G.path_potential c h
  change c a + dot (G.weight c) chi = c b + dot (G.weight c) psi at hp
  rw [ha, hb, hd] at hp
  have impossible : (0 : ZMod 2) = 1 := add_right_cancel hp
  exact zero_ne_one impossible
end EdgeGraph
end GluingEPPA
