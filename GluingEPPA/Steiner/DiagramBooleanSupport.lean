import GluingEPPA.Steiner.DiagramWordNaturality

/-!
# Boolean support of a projected Steiner gluing walk

The first-stage Boolean lift records each *named* edge separately.
An edge belongs to the support iff its number of occurrences in the
word is odd. We prove directly that the endpoints of any genuine
walk are joined by a path in the graph consisting of these edges.

The proof uses cuts rather than Eulerian trails. A cut crossed by a
walk has odd total parity precisely when its endpoints lie on
opposite sides. If the endpoints were disconnected in the parity
subgraph, their connected-component cut would have zero parity
on every edge. Contradiction.

Parallel named edges stay separate throughout, and the argument
does not depend on the recursive group construction.
-/

namespace GluingEPPA.Steiner.EdgeGraph

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} (D : EdgeGraph V E)
variable [Fintype E] [DecidableEq E]

/-- Multiplicity of a named edge in a word, reduced modulo two. -/
def edgeParity : List E → E → ZMod 2
  | [], _ => 0
  | a :: w, e => (if e = a then 1 else 0) + edgeParity w e

/-- The set of named edge occurrences traversed an odd number of times. -/
def oddEdges (w : List E) : Set E :=
  {e | edgeParity w e ≠ 0}

/-- For any edge set, forget edge names when constructing the
ordinary undirected graph. Multiple parallel names may witness
the same adjacency; parity is computed *before* forgetting names. -/
noncomputable def supportedGraph (M : Set E) : SimpleGraph V where
  Adj u v := ∃ e : E, e ∈ M ∧ D.Joins e u v
  symm := by
    constructor
    intro u v h
    rcases h with ⟨e, he, hj⟩
    exact ⟨e, he, D.joins_symm hj⟩
  loopless := by
    constructor
    intro u h
    rcases h with ⟨e, he, hj⟩
    rcases hj with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact D.loopless e (hs.trans ht.symm)
    · exact D.loopless e (ht.trans hs.symm)

/-- Concatenation of actual walks, with both endpoints retained. -/
theorem wordWalk_concat {M : Set E} {u v z : V}
    {p q : List E} (hp : D.WordWalk M u p v)
    (hq : D.WordWalk M v q z) :
    D.WordWalk M u (p ++ q) z := by
  induction hp generalizing z q with
  | nil => simpa using hq
  | cons he hj p ih =>
      simpa only [List.cons_append] using
        (WordWalk.cons he hj (ih hq))

/-- A named-edge walk projects to a walk in the ordinary graph
supported by the same named edges. -/
theorem wordWalk_toGraph_nonempty {M : Set E} {u v : V} {w : List E}
    (p : D.WordWalk M u w v) :
    Nonempty ((D.supportedGraph M).Walk u v) := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v z e w he hj p ih =>
      rcases ih with ⟨q⟩
      exact ⟨SimpleGraph.Walk.cons ⟨e, he, hj⟩ q⟩

private theorem zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc
    x + x = (2 : ZMod 2) * x := by ring
    _ = 0 := by rw [h2]; simp

/-- Sum of any edge weight over a word equals the sum of its
weights multiplied by their parity coordinates. -/
theorem edgeParity_weighted_sum (w : List E) (f : E → ZMod 2) :
    (∑ e : E, edgeParity w e * f e) = (w.map f).sum := by
  classical
  induction w with
  | nil =>
      simp [edgeParity]
  | cons a w ih =>
      have hsingle :
          (∑ e : E, (if e = a then (1 : ZMod 2) else 0) * f e) = f a := by
        simp
      calc
        (∑ e : E, edgeParity (a :: w) e * f e) =
            (∑ e : E, (if e = a then (1 : ZMod 2) else 0) * f e) +
              (∑ e : E, edgeParity w e * f e) := by
                simp only [edgeParity, add_mul, Finset.sum_add_distrib]
        _ = f a + (w.map f).sum := by rw [hsingle, ih]
        _ = ((a :: w).map f).sum := by simp

/-- The indicator of one side of a cut, with values in F2. -/
noncomputable def cutSide (R : V → Prop) (v : V) : ZMod 2 :=
  if R v then 1 else 0

/-- An edge crosses the cut exactly when this weight is nonzero. -/
noncomputable def cutEdge (R : V → Prop) (e : E) : ZMod 2 :=
  cutSide R (D.source e) + cutSide R (D.target e)

theorem cutEdge_joins (R : V → Prop) {e : E} {u v : V}
    (hj : D.Joins e u v) :
    D.cutEdge R e = cutSide R u + cutSide R v := by
  rcases hj with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simp only [cutEdge, hu, hv]
  · simpa only [cutEdge, hu, hv] using
      (add_comm (cutSide R v) (cutSide R u))

/-- Every genuine walk crosses any cut with parity equal to
the sum of the indicators of its two endpoints. -/
theorem wordWalk_cut_sum (R : V → Prop)
    {M : Set E} {u v : V} {w : List E}
    (p : D.WordWalk M u w v) :
    (w.map (D.cutEdge R)).sum = cutSide R u + cutSide R v := by
  induction p with
  | nil u =>
      change (0 : ZMod 2) = cutSide R u + cutSide R u
      exact (zmodTwo_add_self _).symm
  | @cons u v z e w he hj p ih =>
      change D.cutEdge R e + (w.map (D.cutEdge R)).sum =
        cutSide R u + cutSide R z
      rw [D.cutEdge_joins R hj, ih]
      calc
        (cutSide R u + cutSide R v) +
          (cutSide R v + cutSide R z) =
            cutSide R u + (cutSide R v + cutSide R v) +
              cutSide R z := by abel
        _ = cutSide R u + cutSide R z := by
          rw [zmodTwo_add_self]
          simp

/-- The endpoints of a word walk belong to the same component
of the graph of edge occurrences with odd multiplicity. -/
theorem boolean_support_reachable {u v : V} {w : List E}
    (p : D.WordWalk Set.univ u w v) :
    ∃ q : List E, D.WordWalk (oddEdges w) u q v := by
  classical
  let R : V → Prop :=
    fun z => ∃ q : List E, D.WordWalk (oddEdges w) u q z
  by_contra hnot
  have hv : ¬ R v := hnot
  have hu : R u := ⟨[], WordWalk.nil u⟩
  have hstep (e : E) (he : e ∈ oddEdges w)
      {a b : V} (hj : D.Joins e a b) :
      R a → R b := by
    rintro ⟨q, hq⟩
    refine ⟨q ++ [e], ?_⟩
    exact D.wordWalk_concat hq
      (WordWalk.cons he hj (WordWalk.nil b))
  have hsame (e : E) (he : e ∈ oddEdges w) :
      R (D.source e) ↔ R (D.target e) :=
    ⟨hstep e he (D.joins_endpoints e),
      hstep e he (D.joins_symm (D.joins_endpoints e))⟩
  have cutzero (e : E) (he : e ∈ oddEdges w) :
      D.cutEdge R e = 0 := by
    have hsides :
        cutSide R (D.source e) = cutSide R (D.target e) := by
      by_cases hsrc : R (D.source e)
      · have htgt := (hsame e he).mp hsrc
        simp [cutSide, hsrc, htgt]
      · have htgt : ¬ R (D.target e) :=
          fun ht => hsrc ((hsame e he).mpr ht)
        simp [cutSide, hsrc, htgt]
    change cutSide R (D.source e) + cutSide R (D.target e) = 0
    rw [hsides]
    exact zmodTwo_add_self _
  have hsum : (w.map (D.cutEdge R)).sum = 0 := by
    rw [← edgeParity_weighted_sum w (D.cutEdge R)]
    apply Finset.sum_eq_zero
    intro e he
    by_cases hp : edgeParity w e = 0
    · simp [hp]
    · have hz : D.cutEdge R e = 0 := cutzero e hp
      simp [hz]
  have hcut := D.wordWalk_cut_sum R p
  have ha : cutSide R u = 1 := by simp [cutSide, hu]
  have hb : cutSide R v = 0 := by simp [cutSide, hv]
  have absurd : (0 : ZMod 2) = 1 := by
    calc
      0 = (w.map (D.cutEdge R)).sum := hsum.symm
      _ = cutSide R u + cutSide R v := hcut
      _ = 1 := by rw [ha, hb]; simp
  exact (by decide : (0 : ZMod 2) ≠ 1) absurd

/-- The path formulation of Boolean support; removing repeated
vertices from the obtained walk is handled by the standard path
extraction from a finite graph walk. -/
theorem boolean_support_path [DecidableEq V]
    {u v : V} {w : List E} (p : D.WordWalk Set.univ u w v) :
    Nonempty ((D.supportedGraph (oddEdges w)).Path u v) := by
  obtain ⟨q, hq⟩ := D.boolean_support_reachable p
  obtain ⟨r⟩ := D.wordWalk_toGraph_nonempty hq
  exact ⟨r.toPath⟩

/-- If a Boolean lift starts at χ and ends at η, the support
of χ+η is precisely the odd-edge support of the word. -/
theorem boolean_lift_support_path [DecidableEq V]
    {u v : V} {w : List E} (p : D.WordWalk Set.univ u w v)
    (χ η : E → ZMod 2)
    (hη : ∀ e, η e = χ e + edgeParity w e) :
    Nonempty
      ((D.supportedGraph {e | χ e + η e ≠ 0}).Path u v) := by
  have hs : {e : E | χ e + η e ≠ 0} = oddEdges w := by
    ext e
    have hv : χ e + η e = edgeParity w e := by
      rw [hη e]
      calc
        χ e + (χ e + edgeParity w e) =
          (χ e + χ e) + edgeParity w e := by abel
        _ = edgeParity w e := by rw [zmodTwo_add_self]; simp
    change (χ e + η e ≠ 0) ↔ (edgeParity w e ≠ 0)
    rw [hv]
  rw [hs]
  exact D.boolean_support_path p

end GluingEPPA.Steiner.EdgeGraph
