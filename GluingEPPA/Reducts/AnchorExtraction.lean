import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic

/-!
Extract the common-anchor component from actual full decorated overlaps.
The projection is constructed from occurrences and proved well-defined;
it is not a hypothesis. Full overlaps and nonempty traces are retained.
This module does not assert existence of the incoming geometric realization.
-/
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
  exact : ∀ j k, Allowed e L H (fun x y => copy j x = copy k y)

variable {e : A ↪ V} {L : Rel A → Prop} {H : Equiv.Perm V → Prop}
variable (S : System e L H Z J)

def anchor (j : J) (z : Z) : Prop := ∃ v, S.copy j (.inr v) = z

def retained (j : J) : Prop := ∀ z, S.anchor j z ↔ S.anchor S.root z

def carrier (z : Z) : Prop :=
  ∃ p : J × A, S.retained p.1 ∧ S.copy p.1 (.inl p.2) = z

abbrev Real := {z : Z // S.carrier z}

theorem root_retained : S.retained S.root := fun _ => Iff.rfl

theorem meeting_decorated (j k : J) (x y : Sum A V)
    (hxy : S.copy j x = S.copy k y) :
    ∃ f, L f ∧ ∃ h, H h ∧ Compatible e f h ∧
      (∀ s t, S.copy j s = S.copy k t ↔ decorated f h s t) := by
  rcases S.exact j k with hz | ⟨f, hf, h, hh, hc, he⟩
  · have hempty := congrFun (congrFun hz x) y
    exact False.elim (hempty.mp hxy)
  · exact ⟨f, hf, h, hh, hc, fun s t => (congrFun (congrFun he s) t).to_iff⟩

theorem anchors_equal_of_meet (j k : J) (x y : Sum A V)
    (hxy : S.copy j x = S.copy k y) :
    ∀ z, S.anchor j z ↔ S.anchor k z := by
  obtain ⟨f, hf, h, hh, hc, he⟩ := S.meeting_decorated j k x y hxy
  intro z
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨h v, ((he (.inr v) (.inr (h v))).2 rfl).symm.trans hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨h.symm v, ((he (.inr (h.symm v)) (.inr v)).2 (h.apply_symm_apply v)).trans hv⟩

theorem companion_equal (j k : J) (a b : A)
    (hab : S.copy j (.inl a) = S.copy k (.inl b)) :
    S.copy j (.inr (e a)) = S.copy k (.inr (e b)) := by
  obtain ⟨f, hf, h, hh, hc, he⟩ := S.meeting_decorated j k (.inl a) (.inl b) hab
  exact (he (.inr (e a)) (.inr (e b))).2 (hc a b ((he (.inl a) (.inl b)).1 hab))

theorem label_exists (j : J) (hj : S.retained j) (a : A) :
    ∃ v, S.copy S.root (.inr v) = S.copy j (.inr (e a)) :=
  (hj _).1 ⟨e a, rfl⟩

def occurrenceLabel (j : J) (hj : S.retained j) (a : A) : V :=
  Classical.choose (S.label_exists j hj a)

theorem occurrenceLabel_spec (j : J) (hj : S.retained j) (a : A) :
    S.copy S.root (.inr (S.occurrenceLabel j hj a)) = S.copy j (.inr (e a)) :=
  Classical.choose_spec (S.label_exists j hj a)

theorem labels_equal (j k : J) (hj : S.retained j) (hk : S.retained k)
    (a b : A) (hab : S.copy j (.inl a) = S.copy k (.inl b)) :
    S.occurrenceLabel j hj a = S.occurrenceLabel k hk b := by
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  exact (S.occurrenceLabel_spec j hj a).trans
    ((S.companion_equal j k a b hab).trans (S.occurrenceLabel_spec k hk b).symm)

def occurrence (y : S.Real) : J × A := Classical.choose y.property

theorem occurrence_spec (y : S.Real) :
    S.retained (S.occurrence y).1 ∧ S.copy (S.occurrence y).1 (.inl (S.occurrence y).2) = y.val :=
  Classical.choose_spec y.property

def projection (y : S.Real) : V :=
  S.occurrenceLabel (S.occurrence y).1 (S.occurrence_spec y).1 (S.occurrence y).2

def chart (j : J) (hj : S.retained j) : A ↪ S.Real where
  toFun a := ⟨S.copy j (.inl a), ⟨(j,a), hj, rfl⟩⟩
  inj' := by
    intro a b h
    exact Sum.inl.inj ((S.copy j).injective (congrArg Subtype.val h))

theorem projection_chart (j : J) (hj : S.retained j) (a : A) :
    S.projection (S.chart j hj a) = S.occurrenceLabel j hj a := by
  exact S.labels_equal (S.occurrence (S.chart j hj a)).1 j
    (S.occurrence_spec (S.chart j hj a)).1 hj
    (S.occurrence (S.chart j hj a)).2 a (S.occurrence_spec (S.chart j hj a)).2

theorem projection_anchor (j : J) (hj : S.retained j) (a : A) :
    S.copy S.root (.inr (S.projection (S.chart j hj a))) = S.copy j (.inr (e a)) := by
  rw [S.projection_chart]
  exact S.occurrenceLabel_spec j hj a

theorem projection_root (a : A) :
    S.projection (S.chart S.root S.root_retained a) = e a := by
  exact Sum.inr.inj ((S.copy S.root).injective (S.projection_anchor S.root S.root_retained a))

theorem projection_chart_injective (j : J) (hj : S.retained j) :
    Function.Injective (fun a => S.projection (S.chart j hj a)) := by
  intro a b h
  apply e.injective
  apply Sum.inr.inj
  apply (S.copy j).injective
  rw [← S.projection_anchor j hj a, ← S.projection_anchor j hj b, h]

theorem carrier_disjoint_anchor (y : S.Real) (v : V) :
    S.copy S.root (.inr v) ≠ y.val := by
  intro hv
  obtain ⟨⟨j,a⟩, hj, ha⟩ := y.property
  obtain ⟨w, hw⟩ := (hj _).2 ⟨v,rfl⟩
  have hbad := (S.copy j).injective (hw.trans (hv.trans ha.symm))
  cases hbad

theorem chart_meeting_carrier_retained (j : J) (x : Sum A V) (y : S.Real)
    (hxy : S.copy j x = y.val) : S.retained j := by
  obtain ⟨⟨k,a⟩, hk, ha⟩ := y.property
  intro z
  exact (S.anchors_equal_of_meet j k x (.inl a) (hxy.trans ha.symm) z).trans (hk z)

theorem trace_restriction (j : J) (hj : S.retained j) (y : S.Real) :
    (∃ x : Sum A V, S.copy j x = y.val) ↔ ∃ a : A, S.copy j (.inl a) = y.val := by
  constructor
  · rintro ⟨x,hx⟩
    cases x with
    | inl a => exact ⟨a,hx⟩
    | inr v =>
      obtain ⟨w,hw⟩ := (hj _).1 ⟨v,rfl⟩
      exact False.elim (S.carrier_disjoint_anchor y w (hw.trans hx))
  · rintro ⟨a,ha⟩
    exact ⟨.inl a,ha⟩

theorem nonempty_trace_preserved (X : S.Real → Prop) (j : J)
    (hne : ∃ y : S.Real, X y ∧ ∃ x, S.copy j x = y.val) :
    S.retained j ∧ ∀ y : S.Real,
      (X y ∧ ∃ x : Sum A V, S.copy j x = y.val) ↔
        (X y ∧ ∃ a : A, S.copy j (.inl a) = y.val) := by
  obtain ⟨y,hy,x,hx⟩ := hne
  have hj := S.chart_meeting_carrier_retained j x y hx
  exact ⟨hj, fun z => and_congr_right (fun _ => S.trace_restriction j hj z)⟩

variable [Nonempty V]

theorem retained_meet (j k : J) (hj : S.retained j) (hk : S.retained k) :
    ∃ v w : V, S.copy j (.inr v) = S.copy k (.inr w) := by
  let v : V := Classical.choice inferInstance
  obtain ⟨t,ht⟩ := (hj _).1 ⟨v,rfl⟩
  obtain ⟨w,hw⟩ := (hk _).2 ⟨t,rfl⟩
  exact ⟨v,w,(hw.trans ht).symm⟩

theorem full_real_overlap (j k : J) (hj : S.retained j) (hk : S.retained k) :
    ∃ f, L f ∧ ∀ a b, S.chart j hj a = S.chart k hk b ↔ f a b := by
  obtain ⟨v,w,hvw⟩ := S.retained_meet j k hj hk
  obtain ⟨f,hf,h,hh,hc,he⟩ := S.meeting_decorated j k (.inr v) (.inr w) hvw
  refine ⟨f,hf,fun a b => ?_⟩
  constructor
  · intro hab
    exact (he (.inl a) (.inl b)).1 (congrArg Subtype.val hab)
  · intro hab
    exact Subtype.ext ((he (.inl a) (.inl b)).2 hab)

theorem chart_has_ambient_label (j : J) (hj : S.retained j) :
    ∃ h : Equiv.Perm V, H h ∧
      (∀ v, S.copy j (.inr v) = S.copy S.root (.inr (h v))) ∧
      (∀ a, S.projection (S.chart j hj a) = h (e a)) := by
  obtain ⟨v,w,hvw⟩ := S.retained_meet j S.root hj S.root_retained
  obtain ⟨f,hf,h,hh,hc,he⟩ := S.meeting_decorated j S.root (.inr v) (.inr w) hvw
  have ha : ∀ v, S.copy j (.inr v) = S.copy S.root (.inr (h v)) :=
    fun v => (he (.inr v) (.inr (h v))).2 rfl
  refine ⟨h,hh,ha,fun a => ?_⟩
  exact Sum.inr.inj ((S.copy S.root).injective ((S.projection_anchor j hj a).trans (ha (e a))))

/-- The realization clause is about the complete graph of the overlap. -/
def Realizes : Prop := ∀ r, Allowed e L H r →
  ∃ j, ∀ x y, S.copy S.root x = S.copy j y ↔ r x y

theorem realized_decorated_retained (f : Rel A) (h : Equiv.Perm V) (j : J)
    (he : ∀ x y, S.copy S.root x = S.copy j y ↔ decorated f h x y) : S.retained j := by
  let v : V := Classical.choice inferInstance
  have hv := (he (.inr v) (.inr (h v))).2 rfl
  exact S.anchors_equal_of_meet j S.root (.inr (h v)) (.inr v) hv.symm

theorem every_real_overlap (hr : S.Realizes) (f : Rel A) (hf : L f)
    (h : Equiv.Perm V) (hh : H h) (hc : Compatible e f h) :
    ∃ j, ∃ hj : S.retained j, ∀ a b,
      S.chart S.root S.root_retained a = S.chart j hj b ↔ f a b := by
  obtain ⟨j,he⟩ := hr (decorated f h) (Or.inr ⟨f,hf,h,hh,hc,rfl⟩)
  have hj := S.realized_decorated_retained f h j he
  refine ⟨j,hj,fun a b => ?_⟩
  constructor
  · intro hab
    exact (he (.inl a) (.inl b)).1 (congrArg Subtype.val hab)
  · intro hab
    exact Subtype.ext ((he (.inl a) (.inl b)).2 hab)

theorem projection_surjective (hr : S.Realizes) (hzero : L (emptyRel A))
    (hinv : ∀ h, H h → H h.symm)
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, H h ∧ ∃ a : A, h (e a) = v) :
    Function.Surjective S.projection := by
  intro v
  obtain ⟨h,hh,a,ha⟩ := horbit v
  obtain ⟨j,he⟩ := hr (decorated (emptyRel A) h.symm)
    (Or.inr ⟨emptyRel A,hzero,h.symm,hinv h hh,by intro _ _ hf; exact False.elim hf,rfl⟩)
  have hj := S.realized_decorated_retained (emptyRel A) h.symm j he
  refine ⟨S.chart j hj a, ?_⟩
  apply Sum.inr.inj
  apply (S.copy S.root).injective
  calc
    S.copy S.root (.inr (S.projection (S.chart j hj a))) = S.copy j (.inr (e a)) :=
      S.projection_anchor j hj a
    _ = S.copy S.root (.inr (h (e a))) :=
      ((he (.inr (h (e a))) (.inr (e a))).2 (h.symm_apply_apply (e a))).symm
    _ = S.copy S.root (.inr v) := congrArg (fun v => S.copy S.root (.inr v)) ha

theorem extracted_finite [Finite Z] : Finite S.Real := by infer_instance

end
end GluingEPPA.Reducts.AnchorExtraction
