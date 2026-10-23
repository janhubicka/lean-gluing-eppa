import GluingEPPA.Steiner.DiagramIntersections

/-!
# The two properties of the recursive valuation diagrams

This is the direct bridge for Lemma 4.1 and Theorem 4.2 in the
*main body* of steiner_recursive_gluing_valuations.tex.

For an allowed word, its vertex in the recursive permutation diagram
is determined by the same word value in the literal recursive family
(theorem diagramAction_eq_iff_value). Hence (a) amounts to
deletion of word letters and faithful inclusion of smaller values,
while (b) is exact endpoint repair with an arbitrary smaller word,
not necessarily a walk.

All three assertions below concern the actual family produced by
strong induction, not an externally assumed group or a substitute
construction.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} (D : EdgeGraph V E)
variable [Finite V] [Fintype E] [DecidableEq E]

/-- Property (a), deletion direction. Equal full word-actions have
equal actions after keeping only the letters from M. -/
theorem diagram_word_deletion (M S : Finset E) (hMS : M ⊆ S)
    (p q : List E)
    (hp : ∀ e ∈ p, e ∈ S) (hq : ∀ e ∈ q, e ∈ S)
    (h : wordValue D S p = wordValue D S q) :
    wordValue D M (DirectRecord.restrictWord (M : Set E) p) =
      wordValue D M (DirectRecord.restrictWord (M : Set E) q) := by
  have h' := congrArg (deletion D M S hMS) h
  rw [wordValue_deletion D M S hMS p hp,
      wordValue_deletion D M S hMS q hq] at h'
  exact h'

/-- Property (a), inclusion direction. Equality of two words over
M cannot be lost on passing to the larger stage S. -/
theorem diagram_word_inclusion (M S : Finset E) (hMS : M ⊆ S)
    (p q : List E)
    (hp : ∀ e ∈ p, e ∈ M) (hq : ∀ e ∈ q, e ∈ M)
    (h : wordValue D M p = wordValue D M q) :
    wordValue D S p = wordValue D S q := by
  calc
    wordValue D S p =
      inclusion D M S hMS (wordValue D M p) :=
        (wordValue_inclusion D M S hMS p hp).symm
    _ = inclusion D M S hMS (wordValue D M q) := by rw [h]
    _ = wordValue D S q :=
      wordValue_inclusion D M S hMS q hq

/-- Property (b), with both base endpoints *and* the full valuation
value fixed: when an actual S-walk has the value of an M-word,
there is an actual M-walk with this same value. Deleting letters from
a word does not itself assert that the result is a walk. -/
theorem diagram_endpoint_repair (M S : Finset E) (hMS : M ⊆ S)
    (u v : V) (p m : List E)
    (hp : D.WordWalk (S : Set E) u p v)
    (hm : ∀ e ∈ m, e ∈ M)
    (hval : wordValue D S p = wordValue D S m) :
    ∃ q : List E, D.WordWalk (M : Set E) u q v ∧
      wordValue D M q = wordValue D M m ∧
      wordValue D S q = wordValue D S p := by
  have hsmall :
      inclusion D M S hMS (wordValue D M m) = wordValue D S m :=
    wordValue_inclusion D M S hMS m hm
  have hwalk :
      D.WalkValue (S : Set E) (family D S).edge u v
        (wordValue D S p) := by
    exact WordWalk.value (D := D) (a := (family D S).edge) hp
  have hincluded :
      D.WalkValue (S : Set E) (family D S).edge u v
        (inclusion D M S hMS (wordValue D M m)) := by
    rw [hsmall, ← hval]
    exact hwalk
  have hreplacement :=
    replacement D M S hMS u v (wordValue D M m) hincluded
  obtain ⟨q, hqwalk, hqval⟩ := hreplacement.exists_word
  have hqsmall : wordValue D M q = wordValue D M m := hqval
  have hqletters : ∀ e ∈ q, e ∈ M := wordWalk_letters D hqwalk
  have hfull : wordValue D S q = wordValue D S p := by
    calc
      wordValue D S q =
        inclusion D M S hMS (wordValue D M q) :=
          (wordValue_inclusion D M S hMS q hqletters).symm
      _ = inclusion D M S hMS (wordValue D M m) := by rw [hqsmall]
      _ = wordValue D S m := hsmall
      _ = wordValue D S p := hval.symm
  exact ⟨q, hqwalk, hqsmall, hfull⟩

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
