import GluingEPPA.Steiner.ChainValuation.WordAction
import GluingEPPA.Steiner.ChainValuation.Matching

/-!
# Mapping completed matching actions through a quotient

A map between partial matchings preserves their *completed permutations*
provided it preserves every labelled edge and lifts every labelled edge
emanating from an image point. The lifting condition is essential: otherwise
an unmatched source vertex could map to a matched target vertex and fixed
points would not be respected.

This is the exact edge-level condition needed to turn a surjective map of
chain pushouts into the equivariant cover used by the valuation inclusion.
No bijectivity of the map is required.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {X : Type u} {Y : Type v} {E : Type w}

/-- A matching map preserves both genuine edges and absence of an edge
at a given source vertex. -/
theorem matchingMap_perm
    (M : Matching X) (N : Matching Y) (f : X → Y)
    (hforward : ∀ {x x'}, M.Rel x x' → N.Rel (f x) (f x'))
    (hlift : ∀ {x y'}, N.Rel (f x) y' →
      ∃ x', M.Rel x x' ∧ f x' = y')
    (x : X) :
    f (M.perm x) = N.perm (f x) := by
  by_cases h : ∃ x', M.Rel x x'
  · obtain ⟨x', hx⟩ := h
    rw [M.perm_eq_of_rel hx, N.perm_eq_of_rel (hforward hx)]
  · have hn : ¬ ∃ y', N.Rel (f x) y' := by
      rintro ⟨y', hy'⟩
      obtain ⟨x', hx', _⟩ := hlift hy'
      exact h ⟨x', hx'⟩
    rw [M.perm_fixed_of_none h, N.perm_fixed_of_none hn]

/-- The same edge preservation/lifting interface transports **all**
left-to-right words in the exact orientation used by the manuscript. -/
theorem matchingMap_word
    (M : E → Matching X) (N : E → Matching Y) (f : X → Y)
    (hforward : ∀ e {x x'}, (M e).Rel x x' →
      (N e).Rel (f x) (f x'))
    (hlift : ∀ e {x y'}, (N e).Rel (f x) y' →
      ∃ x', (M e).Rel x x' ∧ f x' = y')
    (w : List E) (x : X) :
    f (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (M e).perm) w x) =
      EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (N e).perm) w (f x) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    change
      f (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (M e).perm) w ((M e).perm x)) =
      EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (N e).perm) w ((N e).perm (f x))
    calc
      f (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
          (fun e => (M e).perm) w ((M e).perm x)) =
        EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
          (fun e => (N e).perm) w (f ((M e).perm x)) :=
        ih ((M e).perm x)
      _ = EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
          (fun e => (N e).perm) w ((N e).perm (f x)) := by
        rw [matchingMap_perm (M e) (N e) f (hforward e) (hlift e) x]


/-- The actual chain-restriction interface: forward edge preservation and
edge lifting are required **only for letters in the smaller mask S**.
All words in S are therefore transported, without requiring equivariance
for unrelated colours in the full diagram. -/
theorem matchingMap_word_onMask
    (S : Finset E)
    (M : E → Matching X) (N : E → Matching Y) (f : X → Y)
    (hforward : ∀ e, e ∈ S → ∀ {x x'}, (M e).Rel x x' →
      (N e).Rel (f x) (f x'))
    (hlift : ∀ e, e ∈ S → ∀ {x y'}, (N e).Rel (f x) y' →
      ∃ x', (M e).Rel x x' ∧ f x' = y')
    (w : List E) (hw : ∀ e ∈ w, e ∈ S) (x : X) :
    f (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (M e).perm) w x) =
      EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (N e).perm) w (f x) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
      have he : e ∈ S := hw e (by simp)
      have htail : ∀ a ∈ w, a ∈ S :=
        fun a ha => hw a (by simp [ha])
      change
        f (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
          (fun e => (M e).perm) w ((M e).perm x)) =
        EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
          (fun e => (N e).perm) w ((N e).perm (f x))
      calc
        f (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
            (fun e => (M e).perm) w ((M e).perm x)) =
          EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
            (fun e => (N e).perm) w (f ((M e).perm x)) :=
          ih htail ((M e).perm x)
        _ = EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
            (fun e => (N e).perm) w ((N e).perm (f x)) := by
          rw [matchingMap_perm (M e) (N e) f
            (hforward e he) (hlift e he) x]

end GluingEPPA.Steiner.ChainValuation
