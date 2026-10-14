import GluingEPPA.Sparsening.OrbitIrreducible

/-!
# A genuine binary auxiliary relation J for sparsening

The survey adds a fresh binary relation, complete on each old chart.
Here J is an actual arity-indexed relation symbol, not a metatheoretic
"connectedness" assumption. Its free-amalgamation semantics agrees with
the existing verified AllThoseEPPA.Structure.FreeDecomposition.

This avoids invoking the already-proved restricted EPPA theorem.
-/
namespace GluingEPPA.Sparsening
universe u v w z

/-- One genuinely binary relation symbol. -/
structure JSymbol (n : Nat) where
  arity_two : n = 2

/-- Old relation symbols together with the new binary J. -/
abbrev WithJ (L : Nat → Type u) (n : Nat) : Type u :=
  L n ⊕ JSymbol n

/-- The relational expansion by a given interpretation of J. -/
def withJ {L : Nat → Type u} {P : Type v}
    (R : RelStructure L P) (J : P → P → Prop) :
    RelStructure (WithJ L) P where
  rel := by
    intro n r xs
    cases r with
    | inl r => exact R.rel r xs
    | inr j =>
      obtain ⟨hn⟩ := j
      cases hn
      exact J (xs 0) (xs 1)

@[simp] theorem withJ_old_rel {L : Nat → Type u} {P : Type v}
    (R : RelStructure L P) (J : P → P → Prop)
    {n : Nat} (r : L n) (xs : Fin n → P) :
    (withJ R J).rel (Sum.inl r) xs ↔ R.rel r xs := Iff.rfl

@[simp] theorem withJ_binary_rel {L : Nat → Type u} {P : Type v}
    (R : RelStructure L P) (J : P → P → Prop)
    (xs : Fin 2 → P) :
    (withJ R J).rel (Sum.inr (⟨rfl⟩ : JSymbol 2)) xs ↔
      J (xs 0) (xs 1) := Iff.rfl

/-- An actual J-clique is irreducible for arbitrary unary set-valued
functions, regardless of the old relation arities. This is exactly the
free-decomposition argument used in AllThoseEPPA/Irreducible.lean. -/
theorem j_clique_irreducible {L : Nat → Type u} {P : Type v} {F : Type w}
    (R : RelStructure L P) (out : F → P → Set P)
    (J : P → P → Prop) (complete : ∀ p q : P, J p q) :
    IsIrreducible (withJ R J) out := by
  classical
  constructor
  intro d
  obtain ⟨p, hp⟩ : ∃ p : P, p ∉ d.left := by
    by_contra h
    push_neg at h
    exact d.left_proper (Set.eq_univ_of_forall h)
  obtain ⟨q, hq⟩ : ∃ q : P, q ∉ d.right := by
    by_contra h
    push_neg at h
    exact d.right_proper (Set.eq_univ_of_forall h)
  let xs : Fin 2 → P := fun i => if i.val = 0 then q else p
  have hrel : (withJ R J).rel (Sum.inr (⟨rfl⟩ : JSymbol 2)) xs := by
    change J (xs 0) (xs 1)
    simpa [xs] using complete q p
  rcases d.rel_local (Sum.inr (⟨rfl⟩ : JSymbol 2)) xs hrel with hl | hr
  · exact hp (by simpa [xs] using hl (1 : Fin 2))
  · exact hq (by simpa [xs] using hr (0 : Fin 2))

/-- In *every* free-amalgamation step, a complete J-clique remains entirely
on one side. No closure assumption on the clique is needed: a single J-pair
between two exclusive points witnesses the forbidden crossing. This is the
one-line inductive ingredient for the strict tree-amalgamation target. -/
theorem j_clique_subset_one_side {L : Nat → Type u} {P : Type v}
    {F : Type w} (R : RelStructure L P) (J : P → P → Prop)
    (out : F → P → Set P)
    (d : UnaryFreeDecomposition (withJ R J) out)
    (S : Set P)
    (clique : ∀ p ∈ S, ∀ q ∈ S, J p q) :
    S ⊆ d.left ∨ S ⊆ d.right := by
  classical
  by_cases hl : S ⊆ d.left
  · exact Or.inl hl
  by_cases hr : S ⊆ d.right
  · exact Or.inr hr
  obtain ⟨p, hpS, hpL⟩ := Set.not_subset.mp hl
  obtain ⟨q, hqS, hqR⟩ := Set.not_subset.mp hr
  let xs : Fin 2 → P := fun i => if i.val = 0 then q else p
  have hrel : (withJ R J).rel (Sum.inr (⟨rfl⟩ : JSymbol 2)) xs := by
    change J (xs 0) (xs 1)
    simpa [xs] using clique q hqS p hpS
  rcases d.rel_local (Sum.inr (⟨rfl⟩ : JSymbol 2)) xs hrel with hleft | hright
  · exact False.elim (hpL (by simpa [xs] using hleft (1 : Fin 2)))
  · exact False.elim (hqR (by simpa [xs] using hright (0 : Fin 2)))

namespace ChartAtlas
variable {V : Type u} {E : Type v} {P : Type w} {L : Nat → Type z}
variable (G : GluingEPPA.EdgeGraph V E) (support : P → V → Prop)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- J upstairs is literally the co-chart relation already used to control
the Boolean quotient; it is symmetric and true of every chart pair. -/
def expandedRelations (R : RelStructure L P) :
    RelStructure (WithJ L) (Vertex G support) :=
  withJ (quotientStructure G support R) (CoChart G support)

theorem chart_is_J_clique (s : V) (chi : E → ZMod 2)
    {x y : P} (hx : support x s) (hy : support y s) :
    CoChart G support
      (copy G support s chi x hx) (copy G support s chi y hy) :=
  ⟨s, chi, x, y, hx, hy, rfl, rfl⟩

/-- Every new J-edge projects to an old J-edge once the old J-relation is
complete on each of the chosen closed charts. -/
theorem coChart_projects_to_J (J : P → P → Prop)
    (old_chart_cliques :
      ∀ s x y, support x s → support y s → J x y)
    {p q : Vertex G support} (h : CoChart G support p q) :
    J (project G support p) (project G support q) := by
  obtain ⟨s, chi, x, y, hx, hy, hp, hq⟩ := h
  have hpx : project G support p = x := by
    rw [← hp]
    rfl
  have hqy : project G support q = y := by
    rw [← hq]
    rfl
  rw [hpx, hqy]
  exact old_chart_cliques s x y hx hy

end ChartAtlas

namespace OrbitAtlas
variable {L : Nat → Type u} {A : Type v} {F : Type w}

/-- Actual closed subcharts of the automorphism orbit inherit completeness
of J from the distinguished root. This is the concrete input needed for
the J-part of the projection homomorphism. -/
theorem chart_J_complete
    (R : RelStructure L A) (J : A → A → Prop)
    (out : F → A → Set A) (root : Set A)
    (hroot : ∀ x y, x ∈ root → y ∈ root → J x y)
    (s : Chart (withJ R J) out root)
    (x y : A) (hx : support (withJ R J) out root x s)
    (hy : support (withJ R J) out root y s) : J x y := by
  obtain ⟨h, hs⟩ := s.property.2
  obtain ⟨a, ha, hax⟩ := hs hx
  obtain ⟨b, hb, hby⟩ := hs hy
  let xs : Fin 2 → A := fun i => if i.val = 0 then a else b
  have hrel : (withJ R J).rel (Sum.inr (⟨rfl⟩ : JSymbol 2)) xs := by
    change J (xs 0) (xs 1)
    simpa [xs] using hroot a b ha hb
  have hh := (h.rel_iff (Sum.inr (⟨rfl⟩ : JSymbol 2)) xs).mpr hrel
  have hJ : J (h.perm a) (h.perm b) := by
    change J (h.perm (xs 0)) (h.perm (xs 1)) at hh
    simpa [xs] using hh
  rw [← hax, ← hby]
  exact hJ

/-- Every auxiliary edge of the new canonical quotient projects to a
genuine old J-edge. This handles the induction's projection homomorphism
for the fresh relation without treating J merely as a meta-relation. -/
theorem coChart_projection_J
    (R : RelStructure L A) (J : A → A → Prop)
    (out : F → A → Set A) (root : Set A)
    (hroot : ∀ x y, x ∈ root → y ∈ root → J x y)
    [Finite A]
    {p q : Vertex (withJ R J) out root}
    (h : ChartAtlas.CoChart (graph (withJ R J) out root)
      (support (withJ R J) out root) p q) :
    J (ChartAtlas.project (graph (withJ R J) out root)
      (support (withJ R J) out root) p)
      (ChartAtlas.project (graph (withJ R J) out root)
      (support (withJ R J) out root) q) := by
  classical
  letI : Fintype (Chart (withJ R J) out root) := Fintype.ofFinite _
  letI : Fintype (Edges (withJ R J) out root) := Fintype.ofFinite _
  exact ChartAtlas.coChart_projects_to_J
    (graph (withJ R J) out root) (support (withJ R J) out root)
    J (fun s x y hx hy =>
      chart_J_complete R J out root hroot s x y hx hy) h

end OrbitAtlas
end GluingEPPA.Sparsening
