import GluingEPPA.Steiner.WalkQuotient
import GluingEPPA.Steiner.WordLift

/-!
# Preservation of all word relations under crossing restrictions

The main theorem `restriction_relations` is the relation-preservation content
of Lemma 2.1 in `steiner_eppa.tex`. The smaller-group action and deletion map
are explicit hypotheses, exactly as in the induction. The marked quotient
bijection and the complementary action are proved, not assumed.
-/

namespace GluingEPPA.Steiner

universe u v w z t

section TwoParts

variable {K : Type u} [Group K] {E : Type v} {X : Type w} {Y : Type z}
variable (a : E → K) (d : E → Equiv.Perm Y)
variable (ρ : K →* Equiv.Perm X) (τ : K →* Equiv.Perm Y) (f : X → Y)

/-- Equivariance for generators gives equivariance for every word. -/
theorem word_on_image
    (hon : ∀ e x, d e (f x) = f (ρ (a e) x))
    (word : List E) (x : X) :
    (word.map d).prod (f x) = f (ρ (word.map a).prod x) := by
  induction word generalizing x with
  | nil => simp
  | cons e word ih =>
      change d e ((word.map d).prod (f x)) =
        f (ρ (a e * (word.map a).prod) x)
      rw [ih, hon e]
      simp only [map_mul, Equiv.Perm.mul_apply]

/-- The complementary action need not be trivial: it must factor through τ. -/
theorem word_on_complement (P : Y → Prop)
    (hinv : ∀ g x, ¬ P x → ¬ P (τ g x))
    (hoff : ∀ e x, ¬ P x → d e x = τ (a e) x)
    (word : List E) (x : Y) (hx : ¬ P x) :
    (word.map d).prod x = τ (word.map a).prod x := by
  induction word generalizing x with
  | nil => simp
  | cons e word ih =>
      change d e ((word.map d).prod x) = τ (a e * (word.map a).prod) x
      rw [ih x hx, hoff e _ (hinv _ x hx)]
      simp only [map_mul, Equiv.Perm.mul_apply]

/-- All relations of K are respected, not just relations represented by walks. -/
theorem relations_of_two_parts (P : Y → Prop)
    (hcover : ∀ y, P y → ∃ x, f x = y)
    (hon : ∀ e x, d e (f x) = f (ρ (a e) x))
    (hinv : ∀ g x, ¬ P x → ¬ P (τ g x))
    (hoff : ∀ e x, ¬ P x → d e x = τ (a e) x)
    (word : List E) (hword : (word.map a).prod = 1) :
    (word.map d).prod = 1 := by
  apply Equiv.ext
  intro y
  by_cases hy : P y
  · obtain ⟨x, rfl⟩ := hcover y hy
    simpa [hword] using word_on_image a d ρ f hon word x
  · simpa [hword] using word_on_complement a d τ P hinv hoff word y hy

end TwoParts

namespace Transport

variable {V : Type u} {G : Type v} [Group G]
variable (T : Transport V G)

/-- Ordinary left permutation convention, implemented by inverse right
multiplication. On the involutive edge generators this is the paper's action. -/
def action : G →* Equiv.Perm T.Space where
  toFun g := T.rightPerm g⁻¹
  map_one' := by
    apply Equiv.ext
    intro x
    simp [rightPerm]
  map_mul' g h := by
    apply Equiv.ext
    intro x
    change T.rightMul x (g * h)⁻¹ =
      T.rightMul (T.rightMul x h⁻¹) g⁻¹
    rw [mul_inv_rev, rightMul_mul]

@[simp] theorem action_apply (g : G) (x : T.Space) :
    T.action g x = T.rightMul x g⁻¹ := rfl

variable {H : Type w} [Group H] (L : Transport V H) (i : H →* G)
variable (pres : ∀ u v g, L.Rel u v g → T.Rel u v (i g))

theorem inclusion_action (x : L.Space) (g : H) :
    T.inclusion L i pres (L.action g x) =
      T.action (i g) (T.inclusion L i pres x) := by
  simpa only [action_apply, map_inv] using
    T.inclusion_rightMul L i pres x g⁻¹

/-- Injective maps intertwine the two endpoint transpositions. -/
theorem inclusion_swap
    (refl : ∀ u v g, T.Rel u v (i g) → L.Rel u v g)
    (u v : V) (x : L.Space) :
    T.inclusion L i pres (L.swapPoints u v x) =
      T.swapPoints u v (T.inclusion L i pres x) := by
  classical
  let f := T.inclusion L i pres
  have hf : Function.Injective f := T.inclusion_injective L i pres refl
  have hfu : f (L.marked u) = T.marked u := T.inclusion_marked L i pres u
  have hfv : f (L.marked v) = T.marked v := T.inclusion_marked L i pres v
  change f (L.swapPoints u v x) = T.swapPoints u v (f x)
  by_cases hu : x = L.marked u
  · subst x
    simp [swapPoints, hfu, hfv]
  · by_cases hv : x = L.marked v
    · subst x
      simp [swapPoints, hfu, hfv]
    · have hu' : f x ≠ T.marked u := by
        intro h
        exact hu (hf (h.trans hfu.symm))
      have hv' : f x ≠ T.marked v := by
        intro h
        exact hv (hf (h.trans hfv.symm))
      simp [swapPoints, Equiv.swap_apply_def, hu, hv, hu', hv']

theorem markedPart_action_iff (x : T.Space) (h : H) :
    T.MarkedPart i (T.action (i h) x) ↔ T.MarkedPart i x := by
  simpa only [action_apply, map_inv] using
    T.markedPart_rightMul_iff i x h⁻¹

variable {K : Type z} [Group K] {E : Type t}

/-- Edge action for a restriction: old-group multiplication on internal edges,
and the two marked endpoint transposition on every other edge. -/
noncomputable def restrictedEdge (inside : E → Prop) (b : E → H)
    (source target : E → V) (e : E) : Equiv.Perm T.Space := by
  classical
  exact if inside e then T.action (i (b e)) else T.swapPoints (source e) (target e)

include pres

/-- The crossing-set restriction respects every relation of the source group.

`K` is G_R, `H` is G_(R∩T), and `G` is G_T. The old source action on
X_(R∩T) and the deletion homomorphism are the induction hypotheses. -/
theorem restriction_relations
    (refl : ∀ u v g, T.Rel u v (i g) → L.Rel u v g)
    (a : E → K) (b : E → H) (inside : E → Prop) (source target : E → V)
    (ρ : K →* Equiv.Perm L.Space) (del : K →* H)
    (hon : ∀ e, inside e → ρ (a e) = L.action (b e))
    (hout : ∀ e, ¬ inside e → ρ (a e) = L.swapPoints (source e) (target e))
    (hdel : ∀ e, inside e → del (a e) = b e)
    (hdelout : ∀ e, ¬ inside e → del (a e) = 1)
    (word : List E) (hword : (word.map a).prod = 1) :
    (word.map (T.restrictedEdge i inside b source target)).prod = 1 := by
  classical
  let f := T.inclusion L i pres
  let τ : K →* Equiv.Perm T.Space := T.action.comp (i.comp del)
  apply relations_of_two_parts a (T.restrictedEdge i inside b source target)
    ρ τ f (T.MarkedPart i) ?_ ?_ ?_ ?_ word hword
  · intro y hy
    obtain ⟨v, g, rfl⟩ := hy
    exact ⟨L.point v g, rfl⟩
  · intro e x
    by_cases he : inside e
    · simp only [restrictedEdge, ite_eq_left he, hon e he]
      exact (T.inclusion_action L i pres x (b e)).symm
    · simp only [restrictedEdge, ite_eq_right he, hout e he]
      exact (T.inclusion_swap L i pres refl (source e) (target e) x).symm
  · intro g x hx h
    apply hx
    exact (T.markedPart_action_iff i x (del g)).mp h
  · intro e x hx
    by_cases he : inside e
    · simp only [restrictedEdge, ite_eq_left he]
      change T.action (i (b e)) x = T.action (i (del (a e))) x
      rw [hdel e he]
    · simp only [restrictedEdge, ite_eq_right he]
      rw [T.swap_fixes_complement i (source e) (target e) x hx]
      change x = T.action (i (del (a e))) x
      simp [hdelout e he]

/-- The action factorization in Lemma 2.1 follows from the proved preservation
of every relation and generation by involutions. -/
theorem restriction_factors
    (refl : ∀ u v g, T.Rel u v (i g) → L.Rel u v g)
    (a : E → K) (b : E → H) (inside : E → Prop) (source target : E → V)
    (ρ : K →* Equiv.Perm L.Space) (del : K →* H)
    (hon : ∀ e, inside e → ρ (a e) = L.action (b e))
    (hout : ∀ e, ¬ inside e → ρ (a e) = L.swapPoints (source e) (target e))
    (hdel : ∀ e, inside e → del (a e) = b e)
    (hdelout : ∀ e, ¬ inside e → del (a e) = 1)
    (ha : ∀ e, a e * a e = 1)
    (hgen : ∀ g, ∃ w, wordValue a w = g) :
    ∃ φ : K →* Equiv.Perm T.Space,
      ∀ e, φ (a e) = T.restrictedEdge i inside b source target e := by
  let d := T.restrictedEdge i inside b source target
  have hrel : ∀ w, wordValue a w = 1 → wordValue d w = 1 :=
    T.restriction_relations L i pres refl a b inside source target ρ del
      hon hout hdel hdelout
  refine ⟨involutiveWordLift a d ha hgen hrel, ?_⟩
  intro e
  exact involutiveWordLift_generator a d ha hgen hrel e

end Transport
end GluingEPPA.Steiner
