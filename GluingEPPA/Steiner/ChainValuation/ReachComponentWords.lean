import GluingEPPA.Steiner.ChainValuation.ReachComponentAction

/-!
# Whole-word action transfer along a genuine M-component chart

The Part II chain-restriction lemma compares word actions, not merely
individual labelled edges. Earlier checked lemmas give the exact
edge-reflecting matched-component chart, and ReachComponentAction
transports the completed permutation for each letter of M.

This module iterates that equivariance in the manuscript's written
letter order. It proves a *two-way* equivalence between equality of
any two M-word actions on a normalized component and equality of the
same actions on its whole original M-component.

This is a conditional component-chart theorem, not an assertion
that the normalized finite-history chart has yet been constructed.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {E : Type u} {X : Type v} {U : Type w}

/-- The completed letter action of a written word: the first
letter acts first, and subsequent letters act in sequence. -/
noncomputable def matchingWordApply (P : E → Matching X) :
    List E → X → X
  | [], x => x
  | e :: es, x => matchingWordApply P es ((P e).perm x)

@[simp] theorem matchingWordApply_nil (P : E → Matching X)
    (x : X) : matchingWordApply P [] x = x := rfl

@[simp] theorem matchingWordApply_cons (P : E → Matching X)
    (e : E) (es : List E) (x : X) :
    matchingWordApply P (e :: es) x =
      matchingWordApply P es ((P e).perm x) := rfl

/-- A genuine edge-reflecting M-component chart conjugates the
entire action of each word over M, including every fixed-point
completion encountered along that word. -/
theorem componentChart_word_perm_val
    (P : E → Matching X) (M : Finset E) (q : X)
    (Q : E → Matching U)
    (F : U ≃ MatchingReachComponent P M q)
    (hRel : ∀ e ∈ M, ∀ x y : U,
      (Q e).Rel x y ↔ (P e).Rel (F x).val (F y).val)
    (word : List E) :
    (∀ e ∈ word, e ∈ M) →
      ∀ x : U,
        (F (matchingWordApply Q word x)).val =
          matchingWordApply P word (F x).val := by
  induction word with
  | nil =>
      intro _ x
      rfl
  | cons e es ih =>
      intro hw x
      have he : e ∈ M := hw e (List.mem_cons_self)
      have htail : ∀ t ∈ es, t ∈ M := by
        intro t ht
        exact hw t (List.mem_cons_of_mem e ht)
      calc
        (F (matchingWordApply Q (e :: es) x)).val =
            (F (matchingWordApply Q es ((Q e).perm x))).val := rfl
        _ = matchingWordApply P es (F ((Q e).perm x)).val :=
          ih htail ((Q e).perm x)
        _ = matchingWordApply P es ((P e).perm (F x).val) := by
          rw [componentChart_perm_val_of_edge_iff
            P M q Q F hRel e he x]
        _ = matchingWordApply P (e :: es) (F x).val := rfl

/-- Equality of M-word actions on the smaller normalized component
is equivalent to equality on every vertex of the entire genuine
M-component in the original quotient.

The forward direction uses SURJECTIVITY of the chart; the reverse
uses INJECTIVITY. Replacing the chart by a cover or injection only
would invalidate one of these two implications. -/
theorem componentChart_word_actions_eq_iff
    (P : E → Matching X) (M : Finset E) (q : X)
    (Q : E → Matching U)
    (F : U ≃ MatchingReachComponent P M q)
    (hRel : ∀ e ∈ M, ∀ x y : U,
      (Q e).Rel x y ↔ (P e).Rel (F x).val (F y).val)
    (word₁ word₂ : List E)
    (hw₁ : ∀ e ∈ word₁, e ∈ M)
    (hw₂ : ∀ e ∈ word₂, e ∈ M) :
    (∀ x : U, matchingWordApply Q word₁ x =
      matchingWordApply Q word₂ x) ↔
    (∀ y : MatchingReachComponent P M q,
      matchingWordApply P word₁ y.val =
        matchingWordApply P word₂ y.val) := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := F.surjective y
    calc
      matchingWordApply P word₁ (F x).val =
        (F (matchingWordApply Q word₁ x)).val :=
          (componentChart_word_perm_val
            P M q Q F hRel word₁ hw₁ x).symm
      _ = (F (matchingWordApply Q word₂ x)).val := by rw [h x]
      _ = matchingWordApply P word₂ (F x).val :=
          componentChart_word_perm_val
            P M q Q F hRel word₂ hw₂ x
  · intro h x
    apply F.injective
    apply Subtype.ext
    calc
      (F (matchingWordApply Q word₁ x)).val =
        matchingWordApply P word₁ (F x).val :=
          componentChart_word_perm_val
            P M q Q F hRel word₁ hw₁ x
      _ = matchingWordApply P word₂ (F x).val := h (F x)
      _ = (F (matchingWordApply Q word₂ x)).val :=
          (componentChart_word_perm_val
            P M q Q F hRel word₂ hw₂ x).symm

end GluingEPPA.Steiner.ChainValuation
