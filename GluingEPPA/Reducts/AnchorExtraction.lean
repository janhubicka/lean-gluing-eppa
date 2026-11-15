import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic

/-! Common-anchor extraction from full decorated overlaps. The projection,
its well-definedness, exact overlaps and trace identities are conclusions.
Existence of the incoming geometric realization is not asserted here. -/
namespace GluingEPPA.Reducts.AnchorExtraction
noncomputable section
universe u
variable {A V Z J : Type u}
abbrev Rel (X : Type u) := X → X → Prop
def emptyRel (X : Type u) : Rel X := fun _ _ => False
def decorated (f : Rel A) (h : Equiv.Perm V) : Rel (Sum A V)
  | .inl a, .inl b => f a b
  | .inr v, .inr w => h v = w
  | _, _ => False
def Compatible (e : A ↪ V) (f : Rel A) (h : Equiv.Perm V) : Prop :=
  ∀ a b, f a b → h (e a) = e b
def Allowed (e : A ↪ V) (L : Rel A → Prop) (H : Equiv.Perm V → Prop)
    (r : Rel (Sum A V)) : Prop :=
  r = emptyRel _ ∨ ∃ f, L f ∧ ∃ h, H h ∧ Compatible e f h ∧ r = decorated f h
structure System (e : A ↪ V) (L : Rel A → Prop) (H : Equiv.Perm V → Prop)
    (Z J : Type u) where
  copy : J → (Sum A V ↪ Z)
  root : J
  overlap_allowed : ∀ j k, Allowed e L H (fun x y => copy j x = copy k y)
variable {e : A ↪ V} {L : Rel A → Prop} {H : Equiv.Perm V → Prop}
variable (S : System e L H Z J)
def anchor (j : J) (z : Z) : Prop := ∃ v, S.copy j (.inr v) = z
def retained (j : J) : Prop := ∀ z, anchor S j z ↔ anchor S S.root z
def carrier (z : Z) : Prop :=
  ∃ p : J × A, retained S p.1 ∧ S.copy p.1 (.inl p.2) = z
abbrev Real := {z : Z // carrier S z}
theorem root_retained : retained S S.root := fun _ => Iff.rfl

theorem meeting_decorated (j k : J) (x y : Sum A V)
    (hxy : S.copy j x = S.copy k y) :
    ∃ f, L f ∧ ∃ h, H h ∧ Compatible e f h ∧
      (∀ s t, S.copy j s = S.copy k t ↔ decorated f h s t) := by
  rcases S.overlap_allowed j k with hz | ⟨f, hf, h, hh, hc, he⟩
  · have hempty := congrFun (congrFun hz x) y
    exact False.elim (hempty.mp hxy)
  · exact ⟨f, hf, h, hh, hc, fun s t => (congrFun (congrFun he s) t).to_iff⟩

theorem anchors_equal_of_meet (j k : J) (x y : Sum A V)
    (hxy : S.copy j x = S.copy k y) :
    ∀ z, anchor S j z ↔ anchor S k z := by
  obtain ⟨f, hf, h, hh, hc, he⟩ := meeting_decorated S j k x y hxy
  intro z
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨h v, ((he (.inr v) (.inr (h v))).2 rfl).symm.trans hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨h.symm v, ((he (.inr (h.symm v)) (.inr v)).2 (h.apply_symm_apply v)).trans hv⟩

theorem companion_equal (j k : J) (a b : A)
    (hab : S.copy j (.inl a) = S.copy k (.inl b)) :
    S.copy j (.inr (e a)) = S.copy k (.inr (e b)) := by
  obtain ⟨f, hf, h, hh, hc, he⟩ := meeting_decorated S j k (.inl a) (.inl b) hab
  exact (he (.inr (e a)) (.inr (e b))).2 (hc a b ((he (.inl a) (.inl b)).1 hab))

theorem label_exists (j : J) (hj : retained S j) (a : A) :
    ∃ v, S.copy S.root (.inr v) = S.copy j (.inr (e a)) :=
  (hj _).1 ⟨e a, rfl⟩
def occurrenceLabel (j : J) (hj : retained S j) (a : A) : V :=
  Classical.choose (label_exists S j hj a)
theorem occurrenceLabel_spec (j : J) (hj : retained S j) (a : A) :
    S.copy S.root (.inr (occurrenceLabel S j hj a)) = S.copy j (.inr (e a)) :=
  Classical.choose_spec (label_exists S j hj a)

theorem labels_equal (j k : J) (hj : retained S j) (hk : retained S k)
    (a b : A) (hab : S.copy j (.inl a) = S.copy k (.inl b)) :
    occurrenceLabel S j hj a = occurrenceLabel S k hk b := by
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  exact (occurrenceLabel_spec S j hj a).trans
    ((companion_equal S j k a b hab).trans (occurrenceLabel_spec S k hk b).symm)

def occurrence (y : Real S) : J × A := Classical.choose y.property
theorem occurrence_spec (y : Real S) :
    retained S (occurrence S y).1 ∧ S.copy (occurrence S y).1 (.inl (occurrence S y).2) = y.val :=
  Classical.choose_spec y.property
def projection (y : Real S) : V :=
  occurrenceLabel S (occurrence S y).1 (occurrence_spec S y).1 (occurrence S y).2

def chart (j : J) (hj : retained S j) : A ↪ Real S where
  toFun a := ⟨S.copy j (.inl a), ⟨(j,a), hj, rfl⟩⟩
  inj' := by
    intro a b h
    exact Sum.inl.inj ((S.copy j).injective (congrArg Subtype.val h))

theorem projection_chart (j : J) (hj : retained S j) (a : A) :
    projection S (chart S j hj a) = occurrenceLabel S j hj a := by
  exact labels_equal S (occurrence S (chart S j hj a)).1 j
    (occurrence_spec S (chart S j hj a)).1 hj
    (occurrence S (chart S j hj a)).2 a (occurrence_spec S (chart S j hj a)).2

theorem projection_anchor (j : J) (hj : retained S j) (a : A) :
    S.copy S.root (.inr (projection S (chart S j hj a))) = S.copy j (.inr (e a)) := by
  rw [projection_chart S]
  exact occurrenceLabel_spec S j hj a

theorem projection_root (a : A) :
    projection S (chart S S.root (root_retained S) a) = e a := by
  exact Sum.inr.inj ((S.copy S.root).injective (projection_anchor S S.root (root_retained S) a))

theorem projection_chart_injective (j : J) (hj : retained S j) :
    Function.Injective (fun a => projection S (chart S j hj a)) := by
  intro a b h
  apply e.injective
  apply Sum.inr.inj
  apply (S.copy j).injective
  exact (projection_anchor S j hj a).symm.trans
    ((congrArg (fun v => S.copy S.root (.inr v)) h).trans (projection_anchor S j hj b))

theorem carrier_disjoint_anchor (y : Real S) (v : V) :
    S.copy S.root (.inr v) ≠ y.val := by
  intro hv
  obtain ⟨⟨j,a⟩, hj, ha⟩ := y.property
  obtain ⟨w, hw⟩ := (hj _).2 ⟨v,rfl⟩
  have hbad := (S.copy j).injective (hw.trans (hv.trans ha.symm))
  cases hbad

theorem chart_meeting_carrier_retained (j : J) (x : Sum A V) (y : Real S)
    (hxy : S.copy j x = y.val) : retained S j := by
  obtain ⟨⟨k,a⟩, hk, ha⟩ := y.property
  intro z
  exact (anchors_equal_of_meet S j k x (.inl a) (hxy.trans ha.symm) z).trans (hk z)

theorem trace_restriction (j : J) (hj : retained S j) (y : Real S) :
    (∃ x : Sum A V, S.copy j x = y.val) ↔ ∃ a : A, S.copy j (.inl a) = y.val := by
  constructor
  · rintro ⟨x,hx⟩
    cases x with
    | inl a => exact ⟨a,hx⟩
    | inr v =>
      obtain ⟨w,hw⟩ := (hj _).1 ⟨v,rfl⟩
      exact False.elim (carrier_disjoint_anchor S y w (hw.trans hx))
  · rintro ⟨a,ha⟩
    exact ⟨.inl a,ha⟩

theorem nonempty_trace_preserved (X : Real S → Prop) (j : J)
    (hne : ∃ y : Real S, X y ∧ ∃ x, S.copy j x = y.val) :
    retained S j ∧ ∀ y : Real S,
      (X y ∧ ∃ x : Sum A V, S.copy j x = y.val) ↔
        (X y ∧ ∃ a : A, S.copy j (.inl a) = y.val) := by
  obtain ⟨y,hy,x,hx⟩ := hne
  have hj := chart_meeting_carrier_retained S j x y hx
  exact ⟨hj, fun z => and_congr_right (fun _ => trace_restriction S j hj z)⟩

theorem trace_family_equivalence (X T : Real S → Prop) (hne : ∃ y, T y) :
    (∃ j, ∀ y : Real S, T y ↔ X y ∧ ∃ x : Sum A V, S.copy j x = y.val) ↔
    (∃ j, ∃ hj : retained S j, ∀ y : Real S, T y ↔ X y ∧ ∃ a : A, S.copy j (.inl a) = y.val) := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨y,hy⟩ := hne
    have ht : ∃ z : Real S, X z ∧ ∃ x, S.copy j x = z.val := ⟨y,(hj y).1 hy⟩
    obtain ⟨hr,htr⟩ := nonempty_trace_preserved S X j ht
    exact ⟨hr,fun z => (hj z).trans (htr z)⟩ |> fun ⟨hr,hh⟩ => ⟨j,hr,hh⟩
  · rintro ⟨j,hr,hj⟩
    exact ⟨j,fun z => (hj z).trans (and_congr_right (fun _ => (trace_restriction S j hr z).symm))⟩

theorem projection_unique (p : Real S → V)
    (hp : ∀ j (hj : retained S j) a,
      S.copy S.root (.inr (p (chart S j hj a))) = S.copy j (.inr (e a))) : p = projection S := by
  funext y
  obtain ⟨⟨j,a⟩,hj,ha⟩ := y.property
  have hy : chart S j hj a = y := Subtype.ext ha
  rw [← hy]
  exact Sum.inr.inj ((S.copy S.root).injective ((hp j hj a).trans (projection_anchor S j hj a).symm))

variable [Nonempty V]
theorem retained_meet (j k : J) (hj : retained S j) (hk : retained S k) :
    ∃ v w : V, S.copy j (.inr v) = S.copy k (.inr w) := by
  let v : V := Classical.choice inferInstance
  obtain ⟨t,ht⟩ := (hj _).1 ⟨v,rfl⟩
  obtain ⟨w,hw⟩ := (hk _).2 ⟨t,rfl⟩
  exact ⟨v,w,(hw.trans ht).symm⟩

theorem full_real_overlap (j k : J) (hj : retained S j) (hk : retained S k) :
    ∃ f, L f ∧ ∀ a b, chart S j hj a = chart S k hk b ↔ f a b := by
  obtain ⟨v,w,hvw⟩ := retained_meet S j k hj hk
  obtain ⟨f,hf,h,hh,hc,he⟩ := meeting_decorated S j k (.inr v) (.inr w) hvw
  refine ⟨f,hf,fun a b => ?_⟩
  constructor
  · intro hab
    exact (he (.inl a) (.inl b)).1 (congrArg Subtype.val hab)
  · intro hab
    exact Subtype.ext ((he (.inl a) (.inl b)).2 hab)

theorem chart_has_ambient_label (j : J) (hj : retained S j) :
    ∃ h : Equiv.Perm V, H h ∧
      (∀ v, S.copy j (.inr v) = S.copy S.root (.inr (h v))) ∧
      (∀ a, projection S (chart S j hj a) = h (e a)) := by
  obtain ⟨v,w,hvw⟩ := retained_meet S j S.root hj (root_retained S)
  obtain ⟨f,hf,h,hh,hc,he⟩ := meeting_decorated S j S.root (.inr v) (.inr w) hvw
  have ha : ∀ v, S.copy j (.inr v) = S.copy S.root (.inr (h v)) :=
    fun v => (he (.inr v) (.inr (h v))).2 rfl
  refine ⟨h,hh,ha,fun a => ?_⟩
  exact Sum.inr.inj ((S.copy S.root).injective ((projection_anchor S j hj a).trans (ha (e a))))

def Realizes : Prop := ∀ r, Allowed e L H r →
  ∃ j, ∀ x y, S.copy S.root x = S.copy j y ↔ r x y

theorem realized_decorated_retained (f : Rel A) (h : Equiv.Perm V) (j : J)
    (he : ∀ x y, S.copy S.root x = S.copy j y ↔ decorated f h x y) : retained S j := by
  let v : V := Classical.choice inferInstance
  have hv := (he (.inr v) (.inr (h v))).2 rfl
  exact anchors_equal_of_meet S j S.root (.inr (h v)) (.inr v) hv.symm

theorem every_real_overlap (hr : Realizes S) (f : Rel A) (hf : L f)
    (h : Equiv.Perm V) (hh : H h) (hc : Compatible e f h) :
    ∃ j, ∃ hj : retained S j, ∀ a b,
      chart S S.root (root_retained S) a = chart S j hj b ↔ f a b := by
  obtain ⟨j,he⟩ := hr (decorated f h) (Or.inr ⟨f,hf,h,hh,hc,rfl⟩)
  have hj := realized_decorated_retained S f h j he
  refine ⟨j,hj,fun a b => ?_⟩
  constructor
  · intro hab
    exact (he (.inl a) (.inl b)).1 (congrArg Subtype.val hab)
  · intro hab
    exact Subtype.ext ((he (.inl a) (.inl b)).2 hab)

theorem projection_surjective (hr : Realizes S) (hzero : L (emptyRel A))
    (hinv : ∀ h, H h → H h.symm)
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, H h ∧ ∃ a : A, h (e a) = v) :
    Function.Surjective (projection S) := by
  intro v
  obtain ⟨h,hh,a,ha⟩ := horbit v
  obtain ⟨j,he⟩ := hr (decorated (emptyRel A) h.symm)
    (Or.inr ⟨emptyRel A,hzero,h.symm,hinv h hh,by intro _ _ hf; exact False.elim hf,rfl⟩)
  have hj := realized_decorated_retained S (emptyRel A) h.symm j he
  refine ⟨chart S j hj a, ?_⟩
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  calc
    S.copy S.root (.inr (projection S (chart S j hj a))) = S.copy j (.inr (e a)) :=
      projection_anchor S j hj a
    _ = S.copy S.root (.inr (h (e a))) :=
      ((he (.inr (h (e a))) (.inr (e a))).2 (h.symm_apply_apply (e a))).symm
    _ = S.copy S.root (.inr v) := congrArg (fun v => S.copy S.root (.inr v)) ha

theorem extracted_finite [Finite Z] : Finite (Real S) :=
  Finite.of_injective (fun y : Real S => y.val) (fun _ _ h => Subtype.ext h)
end
end GluingEPPA.Reducts.AnchorExtraction
