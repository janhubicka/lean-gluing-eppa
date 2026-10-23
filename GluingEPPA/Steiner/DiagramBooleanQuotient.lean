import GluingEPPA.Steiner.DiagramBooleanSingleton

/-!
# The Boolean quotient of the recursive valuation diagrams

For every named edge e of a finite mask S, deletion to the singleton
stage {e} detects precisely one F₂ coordinate. The singleton valuation
has two different elements, 1 and its involutive generator; thus this
coordinate is intrinsically defined on the actual recursive group,
independent of word representatives.

Together these coordinates form a surjective map to the Boolean cube.
The map takes each S-word to its ordinary edge parity vector and
commutes with all labelled transitions. The proof handles distinct
parallel edge names independently.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} (D : EdgeGraph V E)
variable [Finite V] [Fintype E] [DecidableEq E]

private theorem singletonSubset (S : Finset E) (e : E) (he : e ∈ S) :
    ({e} : Finset E) ⊆ S := by
  simpa using he

/-- The numerical bit of an element in a group with exactly
the two elements 1 and a, where a is a nonidentity involution. -/
private theorem twoElementBit_mul
    {G : Type u} [Group G] (a : G)
    (hsquare : a * a = 1) (hne : a ≠ 1)
    (hcover : ∀ g : G, g = 1 ∨ g = a) (g h : G) :
    (if g * h = 1 then (0 : ZMod 2) else 1) =
      (if g = 1 then (0 : ZMod 2) else 1) +
        (if h = 1 then (0 : ZMod 2) else 1) := by
  rcases hcover g with hg | hg
  · rw [hg]
    simp
  · rcases hcover h with hh | hh
    · rw [hg, hh]
      simp [hne]
    · rw [hg, hh, hsquare]
      simp [hne, show (1 : ZMod 2) + 1 = 0 by decide]

/-- The e-coordinate is the image under deletion to the
two-vertex singleton diagram, read as 0 or 1. -/
noncomputable def booleanBit (S : Finset E) (e : E) (he : e ∈ S)
    (g : (family D S).Carrier) : ZMod 2 :=
  if deletion D ({e} : Finset E) S (singletonSubset S e he) g = 1
    then 0 else 1

theorem booleanBit_one (S : Finset E) (e : E) (he : e ∈ S) :
    booleanBit D S e he (1 : (family D S).Carrier) = 0 := by
  simp [booleanBit]

theorem booleanBit_mul (S : Finset E) (e : E) (he : e ∈ S)
    (g h : (family D S).Carrier) :
    booleanBit D S e he (g * h) =
      booleanBit D S e he g + booleanBit D S e he h := by
  let π := deletion D ({e} : Finset E) S (singletonSubset S e he)
  change (if π (g * h) = 1 then (0 : ZMod 2) else 1) =
    (if π g = 1 then (0 : ZMod 2) else 1) +
      (if π h = 1 then (0 : ZMod 2) else 1)
  rw [map_mul]
  exact twoElementBit_mul ((family D ({e} : Finset E)).edge e)
    (family_square D ({e} : Finset E) e)
    (singleton_edge_ne_one D e) (singleton_covered D e) (π g) (π h)

/-- A generator toggles exactly the bit of its own named edge. -/
theorem booleanBit_generator (S : Finset E) (e : E) (he : e ∈ S)
    (f : E) (hf : f ∈ S) :
    booleanBit D S e he ((family D S).edge f) =
      (if f = e then (1 : ZMod 2) else 0) := by
  unfold booleanBit
  rw [deletion_edge D ({e} : Finset E) S
    (singletonSubset S e he) f hf]
  by_cases hfe : f = e
  · subst f
    simp [singleton_edge_ne_one D e]
  · simp [hfe]

/-- The canonical map from the actual recursive diagram Q_S to
the Boolean cube over S. -/
noncomputable def booleanCoordinates (S : Finset E)
    (g : (family D S).Carrier) : ({e : E // e ∈ S} → ZMod 2) :=
  fun e => booleanBit D S e.val e.property g

theorem booleanCoordinates_one (S : Finset E) :
    booleanCoordinates D S (1 : (family D S).Carrier) = 0 := by
  funext e
  exact booleanBit_one D S e.val e.property

theorem booleanCoordinates_mul (S : Finset E)
    (g h : (family D S).Carrier) :
    booleanCoordinates D S (g * h) =
      booleanCoordinates D S g + booleanCoordinates D S h := by
  funext e
  exact booleanBit_mul D S e.val e.property g h

theorem booleanCoordinates_generator (S : Finset E) (f : E) (hf : f ∈ S)
    (e : {e : E // e ∈ S}) :
    booleanCoordinates D S ((family D S).edge f) e =
      (if f = e.val then (1 : ZMod 2) else 0) :=
  booleanBit_generator D S e.val e.property f hf

/-- The Boolean image of a word is its ordinary parity vector. -/
theorem booleanCoordinates_word (S : Finset E)
    (w : List E) (hw : ∀ e ∈ w, e ∈ S)
    (a : {e : E // e ∈ S}) :
    booleanCoordinates D S (wordValue D S w) a =
      EdgeGraph.edgeParity w a.val := by
  induction w with
  | nil =>
      change booleanCoordinates D S (1 : (family D S).Carrier) a = 0
      rw [booleanCoordinates_one]
      rfl
  | cons f w ih =>
      have hf : f ∈ S := hw f (by simp)
      have htail : ∀ e ∈ w, e ∈ S := by
        intro e he
        exact hw e (by simp [he])
      calc
        booleanCoordinates D S (wordValue D S (f :: w)) a =
            booleanCoordinates D S ((family D S).edge f) a +
              booleanCoordinates D S (wordValue D S w) a := by
                change booleanCoordinates D S
                  ((family D S).edge f * wordValue D S w) a = _
                exact congrFun (booleanCoordinates_mul D S _ _) a
        _ = (if f = a.val then (1 : ZMod 2) else 0) +
            EdgeGraph.edgeParity w a.val := by
              rw [booleanCoordinates_generator D S f hf a, ih htail]
        _ = EdgeGraph.edgeParity (f :: w) a.val := by
              change _ = (if a.val = f then (1 : ZMod 2) else 0) +
                EdgeGraph.edgeParity w a.val
              by_cases h : f = a.val
              · simp [h]
              · simp [h, Ne.symm h]

/-- A word parity vector is intrinsic to the valuation vertex:
two words with equal recursive values have the same parities. -/
theorem booleanWord_wellDefined (S : Finset E)
    (p q : List E) (hp : ∀ e ∈ p, e ∈ S)
    (hq : ∀ e ∈ q, e ∈ S)
    (h : wordValue D S p = wordValue D S q)
    (a : {e : E // e ∈ S}) :
    EdgeGraph.edgeParity p a.val = EdgeGraph.edgeParity q a.val := by
  calc
    EdgeGraph.edgeParity p a.val =
      booleanCoordinates D S (wordValue D S p) a :=
        (booleanCoordinates_word D S p hp a).symm
    _ = booleanCoordinates D S (wordValue D S q) a := by rw [h]
    _ = EdgeGraph.edgeParity q a.val :=
      booleanCoordinates_word D S q hq a

/-- An edge occurs with odd parity in a list without duplicate
edge names exactly when it is a member of that list. -/
theorem edgeParity_of_nodup (w : List E) (hn : w.Nodup) (e : E) :
    EdgeGraph.edgeParity w e =
      (if e ∈ w then (1 : ZMod 2) else 0) := by
  revert hn
  induction w with
  | nil =>
      intro _
      simp [EdgeGraph.edgeParity]
  | cons a w ih =>
      intro hn
      obtain ⟨ha, hw⟩ := List.nodup_cons.mp hn
      have hrec := ih hw
      by_cases he : e = a
      · subst e
        simp [EdgeGraph.edgeParity, ha, hrec]
      · have hne : a ≠ e := Ne.symm he
        simp [EdgeGraph.edgeParity, he, hne, hrec]

/-- Extend a Boolean coordinate function by zero outside its mask. -/
noncomputable def extendBooleanCoordinates (S : Finset E)
    (χ : {e : E // e ∈ S} → ZMod 2) (e : E) : ZMod 2 :=
  if he : e ∈ S then χ ⟨e, he⟩ else 0

theorem extendBooleanCoordinates_at (S : Finset E)
    (χ : {e : E // e ∈ S} → ZMod 2)
    (e : {e : E // e ∈ S}) :
    extendBooleanCoordinates S χ e.val = χ e := by
  rcases e with ⟨e, he⟩
  simp [extendBooleanCoordinates, he]

/-- Every Boolean cube vertex is the parity of a list containing
each selected named edge exactly once, hence comes from a
genuine vertex of the recursive valuation group. -/
theorem booleanCoordinates_surjective (S : Finset E) :
    Function.Surjective (booleanCoordinates D S) := by
  classical
  intro χ
  let T : Finset E :=
    S.filter (fun e => extendBooleanCoordinates S χ e ≠ 0)
  let w : List E := T.toList
  have hw : ∀ e ∈ w, e ∈ S := by
    intro e he
    have ht : e ∈ T := by simpa [w] using he
    exact (Finset.mem_filter.mp ht).1
  refine ⟨wordValue D S w, ?_⟩
  funext a
  rw [booleanCoordinates_word D S w hw a]
  have hn : w.Nodup := by
    simpa [w] using T.nodup_toList
  rw [edgeParity_of_nodup w hn a.val]
  have ht : a.val ∈ w ↔ χ a ≠ 0 := by
    have ht' : a.val ∈ w ↔
        a.val ∈ S ∧ extendBooleanCoordinates S χ a.val ≠ 0 := by
      simp [w, T, Finset.mem_filter]
    rw [ht', extendBooleanCoordinates_at S χ a]
    simp [a.property]
  by_cases hzero : χ a = 0
  · have hn' : a.val ∉ w := fun h => hzero (ht.mp h)
    simp [hn', hzero]
  · have hm : a.val ∈ w := ht.mpr hzero
    have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have hone : χ a = 1 :=
      (htwo (χ a)).resolve_left hzero
    simp [hm, hone]

/-- The quotient commutes with all named labelled transitions. -/
theorem booleanCoordinates_transition (S : Finset E)
    (g : (family D S).Carrier) (f : E) (hf : f ∈ S)
    (a : {e : E // e ∈ S}) :
    booleanCoordinates D S (g * (family D S).edge f) a =
      booleanCoordinates D S g a +
        (if f = a.val then (1 : ZMod 2) else 0) := by
  rw [congrFun (booleanCoordinates_mul D S g _) a]
  rw [booleanCoordinates_generator D S f hf a]

/-- The complete Boolean-quotient assertion of the manuscript:
well-defined on all recursive valuation vertices, onto the Boolean
cube, and compatible with every named edge transition. -/
theorem exact_boolean_quotient (S : Finset E) :
    Function.Surjective (booleanCoordinates D S) ∧
      ∀ (g : (family D S).Carrier) (f : E) (hf : f ∈ S)
        (a : {e : E // e ∈ S}),
        booleanCoordinates D S (g * (family D S).edge f) a =
          booleanCoordinates D S g a +
            (if f = a.val then (1 : ZMod 2) else 0) := by
  exact ⟨booleanCoordinates_surjective D S,
    booleanCoordinates_transition D S⟩

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
