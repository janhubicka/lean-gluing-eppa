import Init

/-!
Algebraic core of the coherent multipartite valuation construction.

A fixed row translation conjugates permutation actions on valuation vertices.
The checked statements include the complete valuation maps, their identity,
composition and inverse, preservation of the actual supported reading relation,
and extension of distinguished rows. Within-part row coordinates are retained
and ignored by the relation: this is the harmless larger full-row model.

This module does not construct the finite replicated base, its invariant
auxiliary table, the cross-coordinate restriction, or the groupoid transports.
In particular it does not assume or claim the end-to-end EPPA theorem.
-/

namespace GluingEPPA.Reducts.PairValuationConjugation

universe u
variable {W : Type u}

structure BasePerm (W : Type u) where
  forward : W → W
  backward : W → W
  left_inv : ∀ x, backward (forward x) = x
  right_inv : ∀ x, forward (backward x) = x

namespace BasePerm

def identity (W : Type u) : BasePerm W where
  forward := id
  backward := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def comp (g f : BasePerm W) : BasePerm W where
  forward := fun x => g.forward (f.forward x)
  backward := fun x => f.backward (g.backward x)
  left_inv := by
    intro x
    rw [g.left_inv, f.left_inv]
  right_inv := by
    intro x
    rw [f.right_inv, g.right_inv]

def inverse (f : BasePerm W) : BasePerm W where
  forward := f.backward
  backward := f.forward
  left_inv := f.right_inv
  right_inv := f.left_inv

end BasePerm

abbrev Vertex (W : Type u) := W × (W → Bool)

def translate (mu : W → W → Bool) (v : Vertex W) : Vertex W :=
  (v.1, fun y => Bool.xor (v.2 y) (mu v.1 y))

def rename (p : BasePerm W) (v : Vertex W) : Vertex W :=
  (p.forward v.1, fun y => v.2 (p.backward y))

def lift (mu : W → W → Bool) (p : BasePerm W) (v : Vertex W) : Vertex W :=
  translate mu (rename p (translate mu v))

theorem xor_twice (a b : Bool) : Bool.xor (Bool.xor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem translate_twice (mu : W → W → Bool) (v : Vertex W) :
    translate mu (translate mu v) = v := by
  apply Prod.ext
  · rfl
  · funext y
    exact xor_twice (v.2 y) (mu v.1 y)

theorem rename_identity (v : Vertex W) : rename (BasePerm.identity W) v = v := by
  cases v
  rfl

theorem rename_comp (g f : BasePerm W) (v : Vertex W) :
    rename (g.comp f) v = rename g (rename f v) := rfl

theorem rename_inverse (p : BasePerm W) (v : Vertex W) :
    rename p.inverse (rename p v) = v := by
  apply Prod.ext
  · exact p.left_inv v.1
  · funext y
    change v.2 (p.backward (p.forward y)) = v.2 y
    rw [p.left_inv]

theorem lift_identity (mu : W → W → Bool) (v : Vertex W) :
    lift mu (BasePerm.identity W) v = v := by
  simp only [lift, rename_identity, translate_twice]

theorem lift_comp (mu : W → W → Bool) (g f : BasePerm W) (v : Vertex W) :
    lift mu (g.comp f) v = lift mu g (lift mu f v) := by
  simp only [lift, rename_comp, translate_twice]

theorem lift_inverse (mu : W → W → Bool) (p : BasePerm W) (v : Vertex W) :
    lift mu p.inverse (lift mu p v) = v := by
  simp only [lift, translate_twice, rename_inverse]

theorem lift_base (mu : W → W → Bool) (p : BasePerm W) (v : Vertex W) :
    (lift mu p v).1 = p.forward v.1 := rfl

def reading (b : W → W → Bool) (u v : Vertex W) : Bool :=
  Bool.xor (Bool.xor (b u.1 v.1) (u.2 v.1)) (v.2 u.1)

def twistedBase (b mu : W → W → Bool) (x y : W) : Bool :=
  Bool.xor (Bool.xor (b x y) (mu x y)) (mu y x)

theorem xor_reassociate (b l r m n : Bool) :
    Bool.xor (Bool.xor b (Bool.xor l m)) (Bool.xor r n) =
      Bool.xor (Bool.xor (Bool.xor (Bool.xor b m) n) l) r := by
  cases b <;> cases l <;> cases r <;> cases m <;> cases n <;> rfl

theorem reading_translate (b mu : W → W → Bool) (u v : Vertex W) :
    reading b (translate mu u) (translate mu v) =
      reading (twistedBase b mu) u v := by
  exact xor_reassociate (b u.1 v.1) (u.2 v.1) (v.2 u.1)
    (mu u.1 v.1) (mu v.1 u.1)

theorem reading_rename (q : W → W → Bool) (p : BasePerm W)
    (u v : Vertex W)
    (hq : q (p.forward u.1) (p.forward v.1) = q u.1 v.1) :
    reading q (rename p u) (rename p v) = reading q u v := by
  change Bool.xor (Bool.xor (q (p.forward u.1) (p.forward v.1))
    (u.2 (p.backward (p.forward v.1))))
    (v.2 (p.backward (p.forward u.1))) = reading q u v
  rw [p.left_inv, p.left_inv, hq]
  rfl

theorem lift_preserves_reading (b mu : W → W → Bool) (p : BasePerm W)
    (u v : Vertex W)
    (hq : twistedBase b mu (p.forward u.1) (p.forward v.1) =
      twistedBase b mu u.1 v.1) :
    reading b (lift mu p u) (lift mu p v) = reading b u v := by
  calc
    reading b (lift mu p u) (lift mu p v) =
        reading (twistedBase b mu) (rename p (translate mu u))
          (rename p (translate mu v)) :=
      reading_translate b mu (rename p (translate mu u)) (rename p (translate mu v))
    _ = reading (twistedBase b mu) (translate mu u) (translate mu v) :=
      reading_rename (twistedBase b mu) p (translate mu u) (translate mu v) hq
    _ = reading b u v := by
      have h := reading_translate b mu (translate mu u) (translate mu v)
      rw [translate_twice, translate_twice] at h
      exact h.symm

def Edge (cross : W → W → Prop) (b : W → W → Bool) (u v : Vertex W) : Prop :=
  cross u.1 v.1 ∧ reading b u v = true

theorem lift_preserves_edge (cross : W → W → Prop) (b mu : W → W → Bool)
    (p : BasePerm W)
    (hc : ∀ x y, cross (p.forward x) (p.forward y) ↔ cross x y)
    (hq : ∀ x y, cross x y →
      twistedBase b mu (p.forward x) (p.forward y) = twistedBase b mu x y)
    (u v : Vertex W) :
    Edge cross b (lift mu p u) (lift mu p v) ↔ Edge cross b u v := by
  constructor
  · intro h
    have hcross : cross u.1 v.1 := (hc u.1 v.1).1 h.1
    have hread := lift_preserves_reading b mu p u v (hq u.1 v.1 hcross)
    exact ⟨hcross, hread.symm.trans h.2⟩
  · intro h
    have hcross : cross (p.forward u.1) (p.forward v.1) := (hc u.1 v.1).2 h.1
    have hread := lift_preserves_reading b mu p u v (hq u.1 v.1 h.1)
    exact ⟨hcross, hread.trans h.2⟩

def embed (rows : W → W → Bool) (x : W) : Vertex W := (x, rows x)

theorem lift_extends_rows (mu rows : W → W → Bool) (p : BasePerm W) (x : W)
    (hsource : ∀ y, mu x y = rows x y)
    (htarget : ∀ y, mu (p.forward x) y = rows (p.forward x) y) :
    lift mu p (embed rows x) = embed rows (p.forward x) := by
  apply Prod.ext
  · rfl
  · funext y
    change Bool.xor (Bool.xor (rows x (p.backward y)) (mu x (p.backward y)))
      (mu (p.forward x) y) = rows (p.forward x) y
    rw [hsource, htarget]
    cases rows x (p.backward y) <;> cases rows (p.forward x) y <;> rfl

#print axioms translate_twice
#print axioms rename_comp
#print axioms lift_identity
#print axioms lift_comp
#print axioms lift_inverse
#print axioms reading_translate
#print axioms lift_preserves_reading
#print axioms lift_preserves_edge
#print axioms lift_extends_rows

end GluingEPPA.Reducts.PairValuationConjugation
