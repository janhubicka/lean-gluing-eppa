import GluingEPPA.Steiner.DiagramExactProperties

/-!
# The singleton recursive valuation diagram has exactly two vertices

At S = {e}, the only nonempty proper subset is the empty set.
Its component-coordinate permutation swaps the two distinct
endpoint components of e; consequently the generator e is not
the identity. Every element at this stage is a product of the
single involution e, so the entire valuation diagram has exactly
the identity vertex and the vertex represented by e.

This proves the first assertion of the Boolean-quotient remark in
the main Steiner manuscript directly for the literal recursion.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} (D : EdgeGraph V E)
variable [Finite V] [Fintype E] [DecidableEq E]

/-- An empty-edge walk cannot move its base vertex. -/
theorem emptyCayleyWalk_same_base {G : Type u} [Group G]
    (a : E → G) {u v : V} {g h : G}
    (p : D.CayleyWalk (∅ : Set E) a u g v h) : u = v := by
  cases p with
  | nil => rfl
  | cons he _ _ => exact False.elim (by simpa using he)

/-- A word using only one named edge is valued either at the identity
or at that edge's generator, because the generator is an involution. -/
theorem singleton_word_value (e : E) (w : List E)
    (hw : ∀ a ∈ w, a = e) :
    wordValue D ({e} : Finset E) w = 1 ∨
      wordValue D ({e} : Finset E) w =
        (family D ({e} : Finset E)).edge e := by
  induction w with
  | nil =>
      left
      rfl
  | cons a w ih =>
      have hae : a = e := hw a (by simp)
      subst a
      have htail : ∀ b ∈ w, b = e := by
        intro b hb
        exact hw b (by simp [hb])
      rcases ih htail with hzero | hone
      · right
        change (family D ({e} : Finset E)).edge e *
            wordValue D ({e} : Finset E) w = _
        rw [hzero, mul_one]
      · left
        change (family D ({e} : Finset E)).edge e *
            wordValue D ({e} : Finset E) w = 1
        rw [hone]
        exact family_square D ({e} : Finset E) e

/-- No other valuation vertices exist at a singleton edge set. -/
theorem singleton_covered (e : E)
    (g : (family D ({e} : Finset E)).Carrier) :
    g = 1 ∨ g = (family D ({e} : Finset E)).edge e := by
  obtain ⟨w, hw, hg⟩ := family_generated D ({e} : Finset E) g
  have onlyE : ∀ a ∈ w, a = e := by
    intro a ha
    simpa using hw a ha
  have hv : wordValue D ({e} : Finset E) w = g := hg
  rcases singleton_word_value D e w onlyE with h | h
  · exact Or.inl (hv.symm.trans h)
  · exact Or.inr (hv.symm.trans h)

/-- At the empty stage two different base vertices represent
different lifted components: there are no allowed edges. -/
theorem empty_components_distinct
    {G : Type u} [Group G] (a : E → G)
    (ha : ∀ e ∈ (∅ : Set E), a e * a e = 1)
    {u v : V} (hne : u ≠ v) :
    D.component (∅ : Set E) a ha u 1 ≠
      D.component (∅ : Set E) a ha v 1 := by
  intro h
  have hp := (D.component_eq_iff (∅ : Set E) a ha u v 1 1).mp h
  exact hne (emptyCayleyWalk_same_base D a hp)

/-- The nontriviality of the singleton generator is detected
by its genuine action on the empty-stage connected components.
No collapsed or tagged substitute group is used. -/
theorem singleton_edge_ne_one (e : E) :
    (family D ({e} : Finset E)).edge e ≠ 1 := by
  let S : Finset E := {e}
  let old : ∀ i : Proper S, Data E i.val := fun i => family D i.val
  let i : Proper S := ⟨∅, by simp [S]⟩
  have he : e ∈ S := by simp [S]
  let c : Step.components D S old i :=
    D.component (Step.sets S i) (Step.edges S old i)
      (Step.involutions S old i) (D.source e) 1
  let d : Step.components D S old i :=
    D.component (Step.sets S i) (Step.edges S old i)
      (Step.involutions S old i) (D.target e) 1
  have hcd : c ≠ d := by
    intro h
    have p : D.CayleyWalk (Step.sets S i) (Step.edges S old i)
        (D.source e) 1 (D.target e) 1 :=
      (D.component_eq_iff (Step.sets S i) (Step.edges S old i)
        (Step.involutions S old i) (D.source e) (D.target e) 1 1).mp h
    have hset : Step.sets S i = (∅ : Set E) := by
      simp [Step.sets, i]
    rw [hset] at p
    exact D.loopless e (emptyCayleyWalk_same_base D (Step.edges S old i) p)
  have hstep :
      ((Step.data D S old).edge e) ≠ 1 := by
    intro hz
    have ht := Step.action_edge D S old i e he c
    rw [hz, (Step.action D S old i).one] at ht
    have hc :
        D.componentEdgePerm (Step.sets S i)
          (Step.edges S old i) (Step.involutions S old i) e c = d :=
      D.componentEdgePerm_endpoint
        (Step.sets S i) (Step.edges S old i)
        (Step.involutions S old i) (D.joins_endpoints e)
    rw [hc] at ht
    exact hcd ht
  change (family D S).edge e ≠ 1
  rw [family_step D S]
  exact hstep

/-- The singleton valuation has precisely two distinct vertices. -/
theorem singleton_exactly_two (e : E) :
    (∀ g : (family D ({e} : Finset E)).Carrier,
       g = 1 ∨ g = (family D ({e} : Finset E)).edge e) ∧
    (family D ({e} : Finset E)).edge e ≠ 1 :=
  ⟨singleton_covered D e, singleton_edge_ne_one D e⟩

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
