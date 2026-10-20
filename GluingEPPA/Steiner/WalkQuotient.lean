import GluingEPPA.Steiner.WalkValues

/-!
# The finite quotient used in the recursive construction

This file proves the quotient relation, its right action, the injective marking,
and the marked-part comparison in Lemma 2.1 of `steiner_eppa.tex`.
-/

namespace GluingEPPA.Steiner.Transport

universe u v w
variable {V : Type u} {G : Type v} [Group G]

variable (T : Transport V G)

def setoid : Setoid (V × G) where
  r p q := T.Rel p.1 q.1 (p.2 * q.2⁻¹)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simpa using T.refl p.1
    · intro p q h
      simpa only [mul_inv_rev, inv_inv] using T.symm h
    · intro p q r hpq hqr
      have h := T.trans hpq hqr
      have heq : (p.2 * q.2⁻¹) * (q.2 * r.2⁻¹) = p.2 * r.2⁻¹ := by group
      simpa only [heq] using h

abbrev Space := Quotient T.setoid

def point (v : V) (g : G) : T.Space := Quotient.mk T.setoid (v, g)

def marked (v : V) : T.Space := T.point v 1

@[simp] theorem point_eq_iff (u v : V) (g h : G) :
    T.point u g = T.point v h ↔ T.Rel u v (g * h⁻¹) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

@[simp] theorem point_eq_marked_iff (u v : V) (g : G) :
    T.point u g = T.marked v ↔ T.Rel u v g := by
  simp [marked, point_eq_iff]

theorem marked_injective (sep : ∀ u v, T.Rel u v 1 → u = v) :
    Function.Injective T.marked := by
  intro u v h
  apply sep u v
  simpa [marked] using (T.point_eq_iff u v 1 1).mp h

/-- Right multiplication on representatives descends to the quotient. -/
def rightMul (x : T.Space) (a : G) : T.Space :=
  Quotient.liftOn x (fun p => T.point p.1 (p.2 * a)) (by
    intro p q h
    apply Quotient.sound
    change T.Rel p.1 q.1 ((p.2 * a) * (q.2 * a)⁻¹)
    have heq : (p.2 * a) * (q.2 * a)⁻¹ = p.2 * q.2⁻¹ := by group
    rw [heq]
    exact h)

@[simp] theorem rightMul_point (v : V) (g a : G) :
    T.rightMul (T.point v g) a = T.point v (g * a) := rfl

@[simp] theorem rightMul_marked (v : V) (a : G) :
    T.rightMul (T.marked v) a = T.point v a := by
  simp [marked]

@[simp] theorem rightMul_one (x : T.Space) : T.rightMul x 1 = x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨v, g⟩
  change T.point v (g * 1) = T.point v g
  rw [mul_one]

theorem rightMul_mul (x : T.Space) (a b : G) :
    T.rightMul (T.rightMul x a) b = T.rightMul x (a * b) := by
  refine Quotient.inductionOn x ?_
  rintro ⟨v, g⟩
  change T.point v ((g * a) * b) = T.point v (g * (a * b))
  rw [mul_assoc]

def rightPerm (a : G) : Equiv.Perm T.Space where
  toFun x := T.rightMul x a
  invFun x := T.rightMul x a⁻¹
  left_inv x := by simp [rightMul_mul]
  right_inv x := by simp [rightMul_mul]

instance [Finite V] [Finite G] : Finite T.Space := inferInstance

variable {H : Type w} [Group H]
variable (L : Transport V H) (i : H →* G)

/-- Membership in the larger walk-value relation reflects to the smaller one.
This is exactly the old path-replacement property and injectivity of `i`. -/
theorem reflects_of_membership (hi : Function.Injective i)
    (hm : ∀ u v g, T.Rel u v (i g) →
      ∃ h, L.Rel u v h ∧ i h = i g) :
    ∀ u v g, T.Rel u v (i g) → L.Rel u v g := by
  intro u v g h
  obtain ⟨k, hk, hkg⟩ := hm u v g h
  have : k = g := hi hkg
  simpa [this] using hk

variable (pres : ∀ u v g, L.Rel u v g → T.Rel u v (i g))

def inclusion : L.Space → T.Space :=
  Quotient.map (fun p => (p.1, i p.2)) (by
    intro p q h
    change T.Rel p.1 q.1 (i p.2 * (i q.2)⁻¹)
    simpa only [map_mul, map_inv] using pres p.1 q.1 (p.2 * q.2⁻¹) h)

@[simp] theorem inclusion_point (v : V) (g : H) :
    T.inclusion L i pres (L.point v g) = T.point v (i g) := rfl

@[simp] theorem inclusion_marked (v : V) :
    T.inclusion L i pres (L.marked v) = T.marked v := by
  simp [marked]

theorem inclusion_injective
    (refl : ∀ u v g, T.Rel u v (i g) → L.Rel u v g) :
    Function.Injective (T.inclusion L i pres) := by
  intro x y hxy
  revert hxy
  refine Quotient.inductionOn₂ x y ?_
  intro p q hxy
  apply Quotient.sound
  change L.Rel p.1 q.1 (p.2 * q.2⁻¹)
  apply refl
  have h := Quotient.exact hxy
  change T.Rel p.1 q.1 (i p.2 * (i q.2)⁻¹) at h
  simpa only [map_mul, map_inv] using h

theorem inclusion_rightMul (x : L.Space) (g : H) :
    T.inclusion L i pres (L.rightMul x g) =
      T.rightMul (T.inclusion L i pres x) (i g) := by
  refine Quotient.inductionOn x ?_
  rintro ⟨v, h⟩
  change T.point v (i (h * g)) = T.point v (i h * i g)
  rw [map_mul]

/-- The distinguished part is the union of smaller-group orbits through
all marked graph vertices, including isolated vertices. -/
def MarkedPart (x : T.Space) : Prop := ∃ v g, x = T.point v (i g)

theorem range_inclusion :
    Set.range (T.inclusion L i pres) = {x | T.MarkedPart i x} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine Quotient.inductionOn y ?_
    rintro ⟨v, g⟩
    exact ⟨v, g, rfl⟩
  · rintro ⟨v, g, rfl⟩
    exact ⟨L.point v g, rfl⟩

theorem marked_mem (v : V) : T.MarkedPart i (T.marked v) := by
  refine ⟨v, 1, ?_⟩
  simp [marked]

theorem markedPart_rightMul_iff (x : T.Space) (h : H) :
    T.MarkedPart i (T.rightMul x (i h)) ↔ T.MarkedPart i x := by
  constructor
  · rintro ⟨v, g, hg⟩
    refine ⟨v, g * h⁻¹, ?_⟩
    have hh := congrArg (fun y => T.rightMul y (i h)⁻¹) hg
    simpa [rightMul_mul, map_mul, map_inv] using hh
  · rintro ⟨v, g, rfl⟩
    refine ⟨v, g * h, ?_⟩
    simp [map_mul]

noncomputable def swapPoints (u v : V) : Equiv.Perm T.Space := by
  classical
  exact Equiv.swap (T.marked u) (T.marked v)

/-- On the complement, an outside-edge transposition fixes every point. -/
theorem swap_fixes_complement (u v : V) (x : T.Space)
    (hx : ¬ T.MarkedPart i x) :
    T.swapPoints u v x = x := by
  classical
  have hu : x ≠ T.marked u := by
    intro h
    apply hx
    rw [h]
    exact T.marked_mem i u
  have hv : x ≠ T.marked v := by
    intro h
    apply hx
    rw [h]
    exact T.marked_mem i v
  simp [swapPoints, Equiv.swap_apply_def, hu, hv]

end GluingEPPA.Steiner.Transport
