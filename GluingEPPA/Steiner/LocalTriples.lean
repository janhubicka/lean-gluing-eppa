import GluingEPPA.Basic

/-!
# Closed gluing of local Steiner triples

An edge transports each named point. If two points travel along the same
sequence of edges, closedness transports their third point. This proves
third-point uniqueness in the quotient under the explicit synchronization
hypothesis. The finite group construction supplies that hypothesis later.
-/

namespace GluingEPPA.Steiner

universe u v

structure TripleDiagram (V : Type u) (A : Type v) where
  step : V → V → A → Prop
  step_symm : ∀ {s t x}, step s t x → step t s x
  triple : V → A → A → A → Prop
  triple_unique : ∀ {s x y z z'}, triple s x y z → triple s x y z' → z = z'
  close_step : ∀ {s t x y z}, triple s x y z → step s t x → step s t y →
    step s t z ∧ triple t x y z

namespace TripleDiagram

variable {V : Type u} {A : Type v} (D : TripleDiagram V A)

def Carries (x : A) (s t : V) : Prop :=
  Relation.ReflTransGen (fun u v => D.step u v x) s t

def CarriesPair (x y : A) (s t : V) : Prop :=
  Relation.ReflTransGen (fun u v => D.step u v x ∧ D.step u v y) s t

theorem carries_symm {x : A} {s t : V} (h : D.Carries x s t) :
    D.Carries x t s := by
  induction h with
  | refl => exact .refl
  | tail _ e ih =>
      exact (Relation.ReflTransGen.single (D.step_symm e)).trans ih

theorem pair_first {x y : A} {s t : V} (h : D.CarriesPair x y s t) :
    D.Carries x s t := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.trans (.single e.1)

theorem pair_second {x y : A} {s t : V} (h : D.CarriesPair x y s t) :
    D.Carries y s t := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.trans (.single e.2)

theorem triple_along_pair {s t : V} {x y : A}
    (h : D.CarriesPair x y s t) :
    ∀ z, D.triple s x y z → D.Carries z s t ∧ D.triple t x y z := by
  induction h with
  | refl =>
      intro z hz
      exact ⟨.refl, hz⟩
  | tail _ he ih =>
      intro z hz
      obtain ⟨hcarry, htri⟩ := ih z hz
      obtain ⟨hzstep, htri'⟩ := D.close_step htri he.1 he.2
      exact ⟨hcarry.trans (.single hzstep), htri'⟩

/-- Two separately carried points can be carried along a common walk. -/
def Synchronizes : Prop :=
  ∀ {s t x y}, D.Carries x s t → D.Carries y s t →
    D.CarriesPair x y s t

theorem completion_carries (hs : D.Synchronizes)
    {s t : V} {x y z : A} (htr : D.triple s x y z)
    (hx : D.Carries x s t) (hy : D.Carries y s t) :
    D.Carries z s t ∧ D.triple t x y z :=
  D.triple_along_pair (hs hx hy) z htr

theorem completion_unique (hs : D.Synchronizes)
    {s t : V} {x y z z' : A}
    (htr : D.triple s x y z) (htr' : D.triple t x y z')
    (hx : D.Carries x s t) (hy : D.Carries y s t) :
    D.Carries z s t ∧ z = z' := by
  obtain ⟨hc, ht⟩ := D.completion_carries hs htr hx hy
  exact ⟨hc, D.triple_unique ht htr'⟩

/-- Two point occurrences are equivalent precisely if their labels agree
and this label travels between the two chart sites. -/
def setoid : Setoid (V × A) where
  r p q := p.2 = q.2 ∧ D.Carries p.2 p.1 q.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨rfl, .refl⟩
    · intro p q h
      rcases h with ⟨he, hc⟩
      exact ⟨he.symm, he.symm ▸ D.carries_symm hc⟩
    · intro p q r hp hq
      rcases hp with ⟨he, hp⟩
      rcases hq with ⟨hf, hq⟩
      exact ⟨he.trans hf, hp.trans (he.symm ▸ hq)⟩

abbrev Realization := Quotient D.setoid

def copy (s : V) (x : A) : D.Realization := Quotient.mk D.setoid (s, x)

theorem copy_eq_iff (s t : V) (x y : A) :
    D.copy s x = D.copy t y ↔ x = y ∧ D.Carries x s t :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem copy_injective (s : V) : Function.Injective (D.copy s) := by
  intro x y h
  exact ((D.copy_eq_iff s s x y).mp h).1

/-- The two identified labels force the same completed point. -/
theorem completion_eq_in_realization (hs : D.Synchronizes)
    {s t : V} {x y z x' y' z' : A}
    (htr : D.triple s x y z) (htr' : D.triple t x' y' z')
    (hx : D.copy s x = D.copy t x')
    (hy : D.copy s y = D.copy t y') :
    D.copy s z = D.copy t z' := by
  obtain ⟨hxx, hxc⟩ := (D.copy_eq_iff s t x x').mp hx
  obtain ⟨hyy, hyc⟩ := (D.copy_eq_iff s t y y').mp hy
  subst x'
  subst y'
  obtain ⟨hzc, hzz⟩ := D.completion_unique hs htr htr' hxc hyc
  subst z'
  exact (D.copy_eq_iff s t z z).mpr ⟨rfl, hzc⟩

/-- The quotient contains exactly the triples contributed by its charts. -/
def tripleOnRealization (b c d : D.Realization) : Prop :=
  ∃ s x y z, D.triple s x y z ∧ D.copy s x = b ∧
    D.copy s y = c ∧ D.copy s z = d

theorem tripleOnRealization_unique (hs : D.Synchronizes)
    {b c d e : D.Realization}
    (h : D.tripleOnRealization b c d)
    (h' : D.tripleOnRealization b c e) : d = e := by
  obtain ⟨s, x, y, z, ht, hx, hy, hz⟩ := h
  obtain ⟨t, x', y', z', ht', hx', hy', hz'⟩ := h'
  have hxx : D.copy s x = D.copy t x' := hx.trans hx'.symm
  have hyy : D.copy s y = D.copy t y' := hy.trans hy'.symm
  have hzz := D.completion_eq_in_realization hs ht ht' hxx hyy
  calc
    d = D.copy s z := hz.symm
    _ = D.copy t z' := hzz
    _ = e := hz'

/-- If a contributed triple meets a chart in its first two points, that
chart contains the entire triple and the same third point. -/
theorem tripleOnRealization_closed (hs : D.Synchronizes)
    {s : V} {x y : A} {d : D.Realization}
    (h : D.tripleOnRealization (D.copy s x) (D.copy s y) d) :
    ∃ z, D.triple s x y z ∧ D.copy s z = d := by
  obtain ⟨t, x', y', z', ht, hx, hy, hz⟩ := h
  obtain ⟨heqX, hcx⟩ := (D.copy_eq_iff t s x' x).mp hx
  obtain ⟨heqY, hcy⟩ := (D.copy_eq_iff t s y' y).mp hy
  subst x'
  subst y'
  obtain ⟨hcz, htri⟩ := D.completion_carries hs ht hcx hcy
  refine ⟨z', htri, ?_⟩
  have heqZ : D.copy t z' = D.copy s z' :=
    (D.copy_eq_iff t s z' z').mpr ⟨rfl, hcz⟩
  exact heqZ.symm.trans hz

end TripleDiagram
end GluingEPPA.Steiner
