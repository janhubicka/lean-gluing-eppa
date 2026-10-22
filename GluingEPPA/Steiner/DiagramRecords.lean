import GluingEPPA.Steiner.DiagramPresentation

/-!
# The auxiliary diagram of the recursive valuation

At stage S the appendix places, for every proper T ⊂ S, the vertices
of Q_T and the components C_T side by side. A word acts on Q_T by the
right transition of its deleted T-word, and on C_T by the component
permutation. These are not the same action: prefix and suffix differ.

Here K i denotes an already constructed earlier valuation group,
corresponding to the vertices of Q_T. We prove that the entire action
on this disjoint union determines exactly the direct record used in
the original manuscript; no independent group existence theorem is
invoked. This theorem is the compatibility dictionary for the appendix.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace DirectRecord

attribute [local instance] Classical.propDecidable

universe u v w z
variable {V : Type u} {E : Type v} {I : Type z}
variable (D : EdgeGraph V E) (T : I → Set E) (K : I → Type w)
variable [∀ i, Group (K i)]
variable (a : ∀ i, E → K i) (ha : ∀ i e, e ∈ T i → a i e * a i e = 1)

/-- Earlier valuation vertices together with earlier lifted components. -/
abbrev diagramVertices :=
  Σ i : I, K i ⊕ D.Component (T i) (a i) (ha i)

/-- A word moves the earlier group vertices by deleted right transitions
    and the component vertices by the earlier component permutations. -/
noncomputable def diagramAction (w : List E) :
    diagramVertices D T K a ha → diagramVertices D T K a ha
  | ⟨i, Sum.inl g⟩ =>
      ⟨i, Sum.inl (g * ((restrictWord (T i) w).map (a i)).prod)⟩
  | ⟨i, Sum.inr c⟩ =>
      ⟨i, Sum.inr (D.componentWordPerm (T i) (a i) (ha i) w c)⟩

/-- Equal actions on every earlier vertex are exactly equal recursive
    record values. Checking only the action on the distinguished
    components would not suffice. -/
theorem diagramAction_eq_iff_value (p q : List E) :
    diagramAction D T K a ha p = diagramAction D T K a ha q ↔
      value D T K a ha p = value D T K a ha q := by
  constructor
  · intro h
    funext i
    apply Prod.ext
    · change ((restrictWord (T i) p).map (a i)).prod =
          ((restrictWord (T i) q).map (a i)).prod
      have h1 := congrFun h ⟨i, Sum.inl (1 : K i)⟩
      simpa [diagramAction] using h1
    · apply MulOpposite.unop_injective
      apply Equiv.ext
      intro c
      change D.componentWordPerm (T i) (a i) (ha i) p c =
        D.componentWordPerm (T i) (a i) (ha i) q c
      have hc := congrFun h ⟨i, Sum.inr c⟩
      simpa [diagramAction] using hc
  · intro h
    funext x
    rcases x with ⟨i, s⟩
    cases s with
    | inl g =>
        have hi := congrFun h i
        have hf := congrArg Prod.fst hi
        change ((restrictWord (T i) p).map (a i)).prod =
          ((restrictWord (T i) q).map (a i)).prod at hf
        simp only [diagramAction]
        rw [hf]
    | inr c =>
        have hi := congrFun h i
        have hp := congrArg Prod.snd hi
        have hperm := congrArg MulOpposite.unop hp
        have hc := congrArg (fun f : Equiv.Perm (D.Component (T i) (a i) (ha i)) =>
          f c) hperm
        change D.componentWordPerm (T i) (a i) (ha i) p c =
          D.componentWordPerm (T i) (a i) (ha i) q c at hc
        simpa only [diagramAction] using congrArg
          (fun y => (⟨i, Sum.inr y⟩ : diagramVertices D T K a ha)) hc

/-- The equality criterion on the recursive group's literal image of
    records, with no new quotient and no reliance on a single endpoint. -/
theorem diagramAction_eq_iff_valuation (S : Set E) (p q : List E)
    (hp : ∀ e ∈ p, e ∈ S) (hq : ∀ e ∈ q, e ∈ S) :
    diagramAction D T K a ha p = diagramAction D T K a ha q ↔
      valuation D T K a ha S p hp = valuation D T K a ha S q hq := by
  rw [diagramAction_eq_iff_value]
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg Subtype.val h

end DirectRecord
end EdgeGraph
end GluingEPPA.Steiner
