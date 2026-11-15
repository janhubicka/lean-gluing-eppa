import GluingEPPA.Reducts.PairValuationConjugation

/-!
Variable-multiplicity replication and its explicitly invariant orientation.
Copies have actual bounded natural-number layers; multiplicities need only
be invariant under the action, not constant across all occupied parts.
Unused points are fixed. The auxiliary table is defined, not postulated.

The common-cardinality equivalence from this local model to the manuscript's
fixed balanced carrier is a remaining bridge; it is not hidden in this file.
-/
namespace GluingEPPA.Reducts.MultipartiteReplication
open GluingEPPA.Reducts.PairValuationConjugation
universe u
variable {D U I : Type u}

abbrev Copies (m : D → Nat) := {z : D × Nat // z.2 < m z.1}
abbrev Space (m : D → Nat) (U : Type u) := Sum (Copies m) U

def copyPerm {m : D → Nat} (p : BasePerm D)
    (hm : ∀ x, m (p.forward x) = m x) : BasePerm (Copies m) where
  forward z := ⟨(p.forward z.1.1, z.1.2), by
    rw [hm]
    exact z.2⟩
  backward z := ⟨(p.backward z.1.1, z.1.2), by
    have h := hm (p.backward z.1.1)
    rw [p.right_inv] at h
    rw [h.symm]
    exact z.2⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact Prod.ext (p.left_inv z.1.1) rfl
  right_inv := by
    intro z
    apply Subtype.ext
    exact Prod.ext (p.right_inv z.1.1) rfl

def sumPerm {X : Type u} (p : BasePerm X) : BasePerm (Sum X U) where
  forward := fun z => match z with
    | .inl x => .inl (p.forward x)
    | .inr x => .inr x
  backward := fun z => match z with
    | .inl x => .inl (p.backward x)
    | .inr x => .inr x
  left_inv := by
    intro z
    cases z with
    | inl x => exact congrArg Sum.inl (p.left_inv x)
    | inr x => rfl
  right_inv := by
    intro z
    cases z with
    | inl x => exact congrArg Sum.inl (p.right_inv x)
    | inr x => rfl

def paddedPerm {m : D → Nat} (p : BasePerm D)
    (hm : ∀ x, m (p.forward x) = m x) : BasePerm (Space m U) :=
  sumPerm (copyPerm p hm)

theorem padded_comp_forward {m : D → Nat} (g f : BasePerm D)
    (hg : ∀ x, m (g.forward x) = m x)
    (hf : ∀ x, m (f.forward x) = m x) (z : Space m U) :
    (paddedPerm (g.comp f) (fun x => (hg (f.forward x)).trans (hf x))).forward z =
      (paddedPerm g hg).forward ((paddedPerm f hf).forward z) := by
  cases z with
  | inl x =>
    apply congrArg Sum.inl
    apply Subtype.ext
    rfl
  | inr x => rfl

theorem padded_identity_forward {m : D → Nat} (z : Space m U) :
    (paddedPerm (BasePerm.identity D) (fun _ => rfl)).forward z = z := by
  cases z with
  | inl x =>
    apply congrArg Sum.inl
    apply Subtype.ext
    rfl
  | inr x => rfl

def embed {m : D → Nat} (positive : ∀ x, 0 < m x) (x : D) : Space m U :=
  .inl ⟨(x, 0), positive x⟩

theorem embed_injective {m : D → Nat} (positive : ∀ x, 0 < m x)
    (x y : D) (h : embed (U := U) positive x = embed positive y) : x = y := by
  have h' := Sum.inl.inj h
  exact congrArg (fun z : Copies m => z.1.1) h'

theorem padded_embed {m : D → Nat} (positive : ∀ x, 0 < m x)
    (p : BasePerm D) (hm : ∀ x, m (p.forward x) = m x) (x : D) :
    (paddedPerm (U := U) p hm).forward (embed positive x) =
      embed positive (p.forward x) := by
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl

def owner {m : D → Nat} (od : D → I) (ou : U → I) : Space m U → I
  | .inl x => od x.1.1
  | .inr x => ou x

def auxiliary {m : D → Nat} (cd : D → D → Bool) (cu : U → U → Bool) :
    Space m U → Space m U → Bool
  | .inl x, .inl y => cd x.1.1 y.1.1
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false
  | .inr x, .inr y => cu x y

theorem auxiliary_restrict {m : D → Nat} (positive : ∀ x, 0 < m x)
    (cd : D → D → Bool) (cu : U → U → Bool) (x y : D) :
    auxiliary cd cu (embed positive x) (embed positive y) = cd x y := rfl

theorem auxiliary_invariant {m : D → Nat} (cd : D → D → Bool)
    (cu : U → U → Bool) (p : BasePerm D)
    (hm : ∀ x, m (p.forward x) = m x)
    (hc : ∀ x y, cd (p.forward x) (p.forward y) = cd x y)
    (x y : Space m U) :
    auxiliary cd cu ((paddedPerm p hm).forward x) ((paddedPerm p hm).forward y) =
      auxiliary cd cu x y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hc x.1.1 y.1.1
    | inr y => rfl
  | inr x =>
    cases y <;> rfl

theorem auxiliary_reverse {m : D → Nat} (od : D → I) (ou : U → I)
    (cd : D → D → Bool) (cu : U → U → Bool)
    (hd : ∀ x y, od x ≠ od y → cd y x = Bool.not (cd x y))
    (hu : ∀ x y, ou x ≠ ou y → cu y x = Bool.not (cu x y))
    (x y : Space m U) (h : owner od ou x ≠ owner od ou y) :
    auxiliary cd cu y x = Bool.not (auxiliary cd cu x y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hd x.1.1 y.1.1 h
    | inr y => rfl
  | inr x =>
    cases y with
    | inl y => rfl
    | inr y => exact hu x y h

theorem auxiliary_within {m : D → Nat} (od : D → I) (ou : U → I)
    (cd : D → D → Bool) (cu : U → U → Bool)
    (separate : ∀ x y, od x ≠ ou y)
    (hd : ∀ x y, od x = od y → cd x y = false)
    (hu : ∀ x y, ou x = ou y → cu x y = false)
    (x y : Space m U) (h : owner od ou x = owner od ou y) :
    auxiliary cd cu x y = false := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hd x.1.1 y.1.1 h
    | inr y => exact False.elim (separate x.1.1 y h)
  | inr x =>
    cases y with
    | inl y => exact False.elim (separate y.1.1 x h.symm)
    | inr y => exact hu x y h

theorem padded_part_iff {m : D → Nat} (od : D → I) (ou : U → I)
    (separate : ∀ x y, od x ≠ ou y) (p : BasePerm D)
    (hm : ∀ x, m (p.forward x) = m x)
    (hp : ∀ x y, od (p.forward x) = od (p.forward y) ↔ od x = od y)
    (x y : Space m U) :
    (owner od ou ((paddedPerm p hm).forward x) =
      owner od ou ((paddedPerm p hm).forward y)) ↔
      owner od ou x = owner od ou y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hp x.1.1 y.1.1
    | inr y =>
      constructor
      · intro h
        exact False.elim (separate (p.forward x.1.1) y h)
      · intro h
        exact False.elim (separate x.1.1 y h)
  | inr x =>
    cases y with
    | inl y =>
      constructor
      · intro h
        exact False.elim (separate (p.forward y.1.1) x h.symm)
      · intro h
        exact False.elim (separate y.1.1 x h.symm)
    | inr y => exact Iff.rfl

end GluingEPPA.Reducts.MultipartiteReplication
