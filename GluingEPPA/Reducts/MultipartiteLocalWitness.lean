import GluingEPPA.Reducts.MultipartiteActualLocalActions

/-!
One concrete finite multipartite witness, with an input embedding and a
homomorphic extension of EVERY actual local automorphism group. Neither
an upstairs action, an invariant completion, nor an atlas is a hypothesis.
The global assignment to arrows between different domains remains separate.
-/
namespace GluingEPPA.Reducts.MultipartiteLocalWitness
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.PairRowCompletion
open GluingEPPA.Reducts.FixedCarrierTransport
open GluingEPPA.Reducts.MultipartiteConcreteCarrier
open GluingEPPA.Reducts.MultipartiteActualLocalActions

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {A I : Type u} [Fintype A] [Fintype I]

abbrev Carrier (A I : Type u) [Fintype A] := Vertex (Base A I)

def decode (o : A → I) (w : Base A I) : Option A :=
  if h : ∃ a, inputEmbedding o a = w then some (Classical.choose h) else none

theorem decode_input (o : A → I) (a : A) : decode o (inputEmbedding o a) = some a := by
  have hw : ∃ x, inputEmbedding o x = inputEmbedding o a := ⟨a, rfl⟩
  rw [decode, dif_pos hw]
  exact congrArg some ((inputEmbedding o).injective (Classical.choose_spec hw))

theorem decode_sound (o : A → I) (w : Base A I) (a : A) (h : decode o w = some a) :
    inputEmbedding o a = w := by
  unfold decode at h
  split at h
  · rename_i hw
    have ha : Classical.choose hw = a := Option.some.inj h
    simpa only [ha] using Classical.choose_spec hw
  · cases h

def initialTable (S : Input A I) (x y : Base A I) : Bool :=
  match decode S.owner x, decode S.owner y with
  | some a, some b => S.color a b
  | _, _ => baseline x y

theorem initialTable_restrict (S : Input A I) (a b : A) :
    initialTable S (inputEmbedding S.owner a) (inputEmbedding S.owner b) = S.color a b := by
  simp only [initialTable, decode_input]

theorem initialTable_reverse (S : Input A I) (x y : Base A I) (h : x.1 ≠ y.1) :
    initialTable S y x = Bool.not (initialTable S x y) := by
  cases hx : decode S.owner x with
  | none =>
    cases hy : decode S.owner y <;>
      simpa only [initialTable, hx, hy] using baseline_reverse x y h
  | some a =>
    cases hy : decode S.owner y with
    | none => simpa only [initialTable, hx, hy] using baseline_reverse x y h
    | some b =>
      have ha := decode_sound S.owner x a hx
      have hb := decode_sound S.owner y b hy
      have hab : S.owner a ≠ S.owner b := by simpa [← ha, ← hb, inputEmbedding] using h
      simpa only [initialTable, hx, hy] using S.reverse a b hab

def rows (S : Input A I) : Base A I → Base A I → Bool :=
  completeRows (fun _ => false) baseline (initialTable S) (fun _ _ => false)

theorem rows_sum (S : Input A I) (x y : Base A I) (h : x.1 ≠ y.1) :
    Bool.xor (rows S x y) (rows S y x) = Bool.xor (initialTable S x y) (baseline x y) := by
  exact completeRows_pair (fun _ => false) baseline (initialTable S) (fun _ _ => false)
    x y (baseline_reverse x y h) (initialTable_reverse S x y h)
    (by intro hf; cases hf)

def inputCopy (S : Input A I) : A ↪ Carrier A I where
  toFun a := embed (rows S) (inputEmbedding S.owner a)
  inj' := by
    intro a b h
    exact (inputEmbedding S.owner).injective (congrArg Prod.fst h)

def label (x y : Carrier A I) : Bool :=
  if x.1.1 = y.1.1 then false else reading baseline x y

theorem label_within (x y : Carrier A I) (h : x.1.1 = y.1.1) : label x y = false := by
  simp only [label, if_pos h]

theorem label_reverse (x y : Carrier A I) (h : x.1.1 ≠ y.1.1) :
    label y x = Bool.not (label x y) := by
  simp only [label, if_neg h, if_neg (Ne.symm h), reading]
  rw [baseline_reverse x.1 y.1 h]
  cases baseline x.1 y.1 <;> cases x.2 y.1 <;> cases y.2 x.1 <;> rfl

def witness : Input (Carrier A I) I where
  owner x := x.1.1
  color := label
  within := label_within
  reverse := label_reverse

theorem inputCopy_part (S : Input A I) (a b : A) :
    (witness (A := A) (I := I)).owner (inputCopy S a) = witness.owner (inputCopy S b) ↔
      S.owner a = S.owner b := Iff.rfl

theorem inputCopy_color (S : Input A I) (a b : A) :
    label (inputCopy S a) (inputCopy S b) = S.color a b := by
  by_cases h : S.owner a = S.owner b
  · exact (label_within (inputCopy S a) (inputCopy S b) h).trans (S.within a b h).symm
  · change (if S.owner a = S.owner b then false else
      reading baseline (embed (rows S) (inputEmbedding S.owner a))
        (embed (rows S) (inputEmbedding S.owner b))) = S.color a b
    rw [if_neg h]
    have hr := rows_sum S (inputEmbedding S.owner a) (inputEmbedding S.owner b) h
    change Bool.xor (Bool.xor (baseline (inputEmbedding S.owner a) (inputEmbedding S.owner b))
      (rows S (inputEmbedding S.owner a) (inputEmbedding S.owner b)))
      (rows S (inputEmbedding S.owner b) (inputEmbedding S.owner a)) = _
    exact (undo_defect _ _ _ _ hr).trans (initialTable_restrict S a b)

def inside (S : Input A I) (D : Set A) (w : Base A I) : Bool :=
  decide (∃ d : D, inputEmbedding S.owner d.val = w)

theorem inside_input (S : Input A I) (D : Set A) (d : D) :
    inside S D (inputEmbedding S.owner d.val) = true := by
  simp only [inside, decide_eq_true_eq]
  exact ⟨d, rfl⟩

def localRows (S : Input A I) (D : Set A) : Base A I → Base A I → Bool :=
  completeRows (inside S D) baseline (localTable S D) (rows S)

theorem localRows_compatible (S : Input A I) (D : Set A) (x y : Base A I)
    (hxy : x.1 ≠ y.1) (hx : inside S D x = true) (hy : inside S D y = true) :
    Bool.xor (rows S x y) (rows S y x) = Bool.xor (localTable S D x y) (baseline x y) := by
  obtain ⟨d, rfl⟩ := of_decide_eq_true hx
  obtain ⟨e, rfl⟩ := of_decide_eq_true hy
  rw [localTable_restrict, ← initialTable_restrict S d.val e.val]
  exact rows_sum S _ _ hxy

/-- Package the actual valuation bijection, not an assumed automorphism. -/
def valuationPerm {W : Type u} (mu : W → W → Bool) (p : BasePerm W) : BasePerm (Vertex W) where
  forward := lift mu p
  backward := lift mu p.inverse
  left_inv := lift_inverse mu p
  right_inv := by
    intro v
    have hi : p.inverse.inverse = p := basePerm_ext _ _ (fun _ => rfl)
    have h := lift_inverse mu p.inverse v
    simpa only [hi] using h

def localLift {S : Input A I} {D : Set A} (f : LocalAut S D) : BasePerm (Carrier A I) :=
  valuationPerm (localRows S D) (baseAction f)

theorem localLift_identity (S : Input A I) (D : Set A) :
    localLift (LocalAut.identity S D) = BasePerm.identity (Carrier A I) := by
  apply basePerm_ext
  intro v
  change lift (localRows S D) (baseAction (LocalAut.identity S D)) v = v
  rw [baseAction_identity, lift_identity]

theorem localLift_comp {S : Input A I} {D : Set A} (g f : LocalAut S D) :
    localLift (g.comp f) = (localLift g).comp (localLift f) := by
  apply basePerm_ext
  intro v
  change lift (localRows S D) (baseAction (g.comp f)) v =
    lift (localRows S D) (baseAction g) (lift (localRows S D) (baseAction f) v)
  rw [baseAction_comp, lift_comp]

theorem localLift_extends {S : Input A I} {D : Set A} (f : LocalAut S D) (d : D) :
    (localLift f).forward (inputCopy S d.val) = inputCopy S (f.perm.forward d).val := by
  have hs := baseAction_extends f d
  have ht : inside S D ((baseAction f).forward (inputEmbedding S.owner d.val)) = true := by
    rw [hs]
    exact inside_input S D (f.perm.forward d)
  exact (completed_lift_extends (inside S D) baseline (localTable S D) (rows S)
    (baseAction f) (inputEmbedding S.owner d.val) (inside_input S D d) ht).trans
      (congrArg (embed (rows S)) hs)

theorem localLift_part {S : Input A I} {D : Set A} (f : LocalAut S D) (x y : Carrier A I) :
    ((localLift f).forward x).1.1 = ((localLift f).forward y).1.1 ↔ x.1.1 = y.1.1 :=
  baseAction_part f x.1 y.1

theorem edge_iff_label (x y : Carrier A I) :
    Edge (fun v w : Base A I => v.1 ≠ w.1) baseline x y ↔ label x y = true := by
  by_cases h : x.1.1 = y.1.1 <;> simp [Edge, label, h]

theorem localLift_color {S : Input A I} {D : Set A} (f : LocalAut S D) (x y : Carrier A I) :
    label ((localLift f).forward x) ((localLift f).forward y) = label x y := by
  have hc : ∀ v w : Base A I, ((baseAction f).forward v).1 ≠ ((baseAction f).forward w).1 ↔ v.1 ≠ w.1 :=
    fun v w => not_congr (baseAction_part f v w)
  have he := completed_lift_preserves_edge (inside S D)
    (fun v w : Base A I => v.1 ≠ w.1) baseline (localTable S D) (rows S) (baseAction f)
    baseline_reverse (localTable_reverse S D) (localRows_compatible S D) hc
    (fun v w _ => localTable_invariant f v w) x y
  change Edge (fun v w : Base A I => v.1 ≠ w.1) baseline ((localLift f).forward x)
    ((localLift f).forward y) ↔ Edge (fun v w : Base A I => v.1 ≠ w.1) baseline x y at he
  rw [edge_iff_label, edge_iff_label] at he
  cases h1 : label ((localLift f).forward x) ((localLift f).forward y) <;>
    cases h2 : label x y <;> simp_all

theorem carrier_finite : Finite (Carrier A I) := by infer_instance

/-- The same finite witness and input embedding work for every actual domain;
all local group representations and their preservation laws are constructed. -/
theorem finite_local_witness (S : Input A I) :
    ∃ j : A ↪ Carrier A I,
      (∀ a b, label (j a) (j b) = S.color a b) ∧
      (∀ a b, (j a).1.1 = (j b).1.1 ↔ S.owner a = S.owner b) ∧
      ∀ D : Set A, ∃ L : LocalAut S D → BasePerm (Carrier A I),
        L (LocalAut.identity S D) = BasePerm.identity (Carrier A I) ∧
        (∀ g f, L (g.comp f) = (L g).comp (L f)) ∧
        (∀ f d, (L f).forward (j d.val) = j (f.perm.forward d).val) ∧
        (∀ f x y, label ((L f).forward x) ((L f).forward y) = label x y) ∧
        (∀ f x y, ((L f).forward x).1.1 = ((L f).forward y).1.1 ↔ x.1.1 = y.1.1) := by
  exact ⟨inputCopy S, inputCopy_color S, inputCopy_part S, fun D =>
    ⟨localLift, localLift_identity S D, localLift_comp,
      localLift_extends, localLift_color, localLift_part⟩⟩

end
end GluingEPPA.Reducts.MultipartiteLocalWitness
