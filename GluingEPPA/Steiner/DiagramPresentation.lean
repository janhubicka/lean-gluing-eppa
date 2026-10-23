import GluingEPPA.Steiner.FiniteIntersections

/-!
# Word actions for the diagram presentation of Steiner valuations

The appendix describes a word by its action at every vertex, rather than
by its value in the recursive group. Here the vertex set is the actual
recursive valuation group, acted on by right multiplication. The empty-word
vertex detects equality of the whole actions. Left translations preserve
every named edge, and two steps along the same edge return to the start.

This first bridge uses the already constructed literal group family. It
does not yet identify the appendix's separate auxiliary union
(Q_T disjoint union C_T) with the existing record product.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

universe u
variable {V E : Type u} (D : EdgeGraph V E)
variable [Finite V] [Fintype E] [DecidableEq E]

/-- The word associated with a sequence of edges in the actual recursive group. -/
noncomputable def wordValue (S : Finset E) (w : List E) :
    (family D S).Carrier :=
  (w.map (family D S).edge).prod

theorem wordValue_singleton (S : Finset E) (e : E) :
    wordValue D S [e] = (family D S).edge e := by
  simp [wordValue]

theorem wordValue_append (S : Finset E) (p q : List E) :
    wordValue D S (p ++ q) = wordValue D S p * wordValue D S q := by
  simp [wordValue, List.map_append, List.prod_append]

/-- The action of a word from every possible starting vertex. -/
noncomputable def wordPermutation (S : Finset E) (w : List E) :
    Equiv.Perm (family D S).Carrier where
  toFun g := g * wordValue D S w
  invFun g := g * (wordValue D S w)⁻¹
  left_inv g := by simp [mul_assoc]
  right_inv g := by simp [mul_assoc]

/-- Two words act alike everywhere exactly when their values agree.
    It is essential to test every vertex, not one arbitrary endpoint. -/
theorem wordPermutation_eq_iff (S : Finset E) (p q : List E) :
    wordPermutation D S p = wordPermutation D S q ↔
      wordValue D S p = wordValue D S q := by
  constructor
  · intro h
    have h1 := congrArg
      (fun f : Equiv.Perm (family D S).Carrier => f 1) h
    simpa [wordPermutation] using h1
  · intro h
    apply Equiv.ext
    intro g
    change g * wordValue D S p = g * wordValue D S q
    rw [h]

/-- Reading p and then q gives the action of their concatenation. -/
theorem wordPermutation_append (S : Finset E) (p q : List E)
    (g : (family D S).Carrier) :
    wordPermutation D S (p ++ q) g =
      wordPermutation D S q (wordPermutation D S p g) := by
  change g * wordValue D S (p ++ q) =
    (g * wordValue D S p) * wordValue D S q
  rw [wordValue_append]
  exact (mul_assoc g (wordValue D S p) (wordValue D S q)).symm

/-- Each letter defines an involutive edge, including letters outside S. -/
theorem wordPermutation_singleton_square (S : Finset E) (e : E)
    (g : (family D S).Carrier) :
    wordPermutation D S [e] (wordPermutation D S [e] g) = g := by
  change (g * wordValue D S [e]) * wordValue D S [e] = g
  rw [wordValue_singleton, mul_assoc, family_square D S e, mul_one]

/-- A symmetry of the labelled diagram is multiplication on the left. -/
noncomputable def leftTranslate (S : Finset E) (g : (family D S).Carrier) :
    Equiv.Perm (family D S).Carrier where
  toFun x := g * x
  invFun x := g⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp

theorem leftTranslate_commutes_with_word (S : Finset E)
    (g x : (family D S).Carrier) (w : List E) :
    leftTranslate D S g (wordPermutation D S w x) =
      wordPermutation D S w (leftTranslate D S g x) := by
  change g * (x * wordValue D S w) = (g * x) * wordValue D S w
  exact (mul_assoc g x (wordValue D S w)).symm

theorem leftTranslate_at_one (S : Finset E)
    (g : (family D S).Carrier) :
    leftTranslate D S g 1 = g := by
  simp [leftTranslate]

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
