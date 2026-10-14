import GluingEPPA.Sparsening.TreeFullA

/-!
# Complete J-roots lie inside one full A-copy in every strict tree

The local-tree induction needs only that every *complete J-clique* in its
target lie inside some building-block A-copy, not the stronger assertion
for every irreducible substructure. This yields a much shorter proof:
a J-edge never crosses a free gluing cut; descend the tree on that side.
No inverse-image irreducibility transport or homomorphism-embedding
factorization is required.

This is the strict unary-language counterpart of the observation in
AllThoseEPPA/TreeLikeTreeIrreducibleExtension.lean, with a simpler hypothesis
tailored to the gluing construction.
-/
namespace GluingEPPA.Sparsening.Tree

universe u v w t
variable {L : Nat → Type u} {F : Type t} {P : Type v}

/-- The one distinguished actual binary symbol in WithJ L. -/
def JPair (x y : P) : Fin 2 → P :=
  fun i => if i.val = 0 then x else y

def IsJClique (R : RelStructure (WithJ L) P) (S : Set P) : Prop :=
  ∀ x, x ∈ S → ∀ y, y ∈ S →
    R.rel (Sum.inr (⟨(), rfl⟩ : JSymbol 2)) (JPair x y)

/-- Any complete J-clique of a concrete strong amalgam lies in one of
the two side images, even when one attachment is degenerate. This uses
only the *actual* contributed J tuples, not an abstract graph separator. -/
theorem jClique_pushout_one_side
    {I : Type v} {X : Type v} {Y : Type v}
    (f : I → X) (g : I → Y)
    (RX : RelStructure (WithJ L) X) (RY : RelStructure (WithJ L) Y)
    (S : Set (PushoutCarrier f g))
    (hS : IsJClique (pushoutRelations f g RX RY) S) :
    S ⊆ Set.range (inclLeft f g) ∨
      S ⊆ Set.range (inclRight f g) := by
  classical
  by_cases hleft : S ⊆ Set.range (inclLeft f g)
  · exact Or.inl hleft
  by_cases hright : S ⊆ Set.range (inclRight f g)
  · exact Or.inr hright
  obtain ⟨p, hpS, hpL⟩ := Set.not_subset.mp hleft
  obtain ⟨q, hqS, hqR⟩ := Set.not_subset.mp hright
  have hJ := hS q hqS p hpS
  change (pushoutRelations f g RX RY).rel
    (Sum.inr (⟨(), rfl⟩ : JSymbol 2)) (JPair q p) at hJ
  change
    (∃ xs : Fin 2 → X,
      (fun i => inclLeft f g (xs i)) = JPair q p ∧ RX.rel _ xs) ∨
    (∃ ys : Fin 2 → Y,
      (fun i => inclRight f g (ys i)) = JPair q p ∧ RY.rel _ ys) at hJ
  rcases hJ with ⟨xs, heq, _⟩ | ⟨ys, heq, _⟩
  · have himage : p ∈ Set.range (inclLeft f g) :=
      ⟨xs 1, by simpa [JPair] using congrFun heq (1 : Fin 2)⟩
    exact False.elim (hpL himage)
  · have himage : q ∈ Set.range (inclRight f g) :=
      ⟨ys 0, by simpa [JPair] using congrFun heq (0 : Fin 2)⟩
    exact False.elim (hqR himage)

/-- The strict target-tree root property: a complete J-clique is contained
in an actual embedded full A-copy, with exact relations and unary fibres.
This is precisely what the separator-root gluing needs. -/
theorem FullATree.JClique_contained_in_A
    {A : Type v}
    (RA : RelStructure (WithJ L) A) (outA : F → A → Set A)
    {V : Type v} (RV : RelStructure (WithJ L) V)
    (outV : F → V → Set V)
    (tree : FullATree RA outA RV outV) :
    ∀ (S : Set V), IsJClique RV S →
      ∃ e : ExactUnaryEmbedding RA outA RV outV,
        S ⊆ Set.range e.toFun := by
  induction tree with
  | copy RV outV e surj =>
      intro S hS
      exact ⟨e, fun x hx => surj x⟩
  | glue RI outI RX outX RY outY hX hY δX δY αX αY ihX ihY =>
      intro S hS
      let f : ExactUnaryEmbedding RI outI RX outX := αX.comp δX
      let g : ExactUnaryEmbedding RI outI RY outY := αY.comp δY
      rcases jClique_pushout_one_side f.toFun g.toFun RX RY S hS with hleft | hright
      · let SX : Set X := {x | inclLeft f.toFun g.toFun x ∈ S}
        have hSX : IsJClique RX SX := by
          intro x hx y hy
          have hh := hS (inclLeft f.toFun g.toFun x) hx
            (inclLeft f.toFun g.toFun y) hy
          have heq :
              (fun i : Fin 2 => inclLeft f.toFun g.toFun (JPair x y i)) =
              JPair (inclLeft f.toFun g.toFun x)
                (inclLeft f.toFun g.toFun y) := by
            funext i
            fin_cases i <;> rfl
          have hJ : (pushoutRelations f.toFun g.toFun RX RY).rel
              (Sum.inr (⟨(), rfl⟩ : JSymbol 2))
              (fun i => inclLeft f.toFun g.toFun (JPair x y i)) := by
            simpa only [heq] using hh
          exact (left_rel_iff RI outI RX outX RY outY f g
            (Sum.inr (⟨(), rfl⟩ : JSymbol 2)) (JPair x y)).mp hJ
        obtain ⟨a, ha⟩ := ihX SX hSX
        let k := leftExactEmbedding RI outI RX outX RY outY f g
        refine ⟨k.comp a, ?_⟩
        intro p hp
        obtain ⟨x, heq⟩ := hleft hp
        have hx : x ∈ SX := by
          change inclLeft f.toFun g.toFun x ∈ S
          rw [heq]
          exact hp
        obtain ⟨z, hz⟩ := ha hx
        refine ⟨z, ?_⟩
        change inclLeft f.toFun g.toFun (a.toFun z) = p
        rw [hz, heq]
      · let SY : Set Y := {y | inclRight f.toFun g.toFun y ∈ S}
        have hSY : IsJClique RY SY := by
          intro x hx y hy
          have hh := hS (inclRight f.toFun g.toFun x) hx
            (inclRight f.toFun g.toFun y) hy
          have heq :
              (fun i : Fin 2 => inclRight f.toFun g.toFun (JPair x y i)) =
              JPair (inclRight f.toFun g.toFun x)
                (inclRight f.toFun g.toFun y) := by
            funext i
            fin_cases i <;> rfl
          have hJ : (pushoutRelations f.toFun g.toFun RX RY).rel
              (Sum.inr (⟨(), rfl⟩ : JSymbol 2))
              (fun i => inclRight f.toFun g.toFun (JPair x y i)) := by
            simpa only [heq] using hh
          exact (right_rel_iff RI outI RX outX RY outY f g
            (Sum.inr (⟨(), rfl⟩ : JSymbol 2)) (JPair x y)).mp hJ
        obtain ⟨a, ha⟩ := ihY SY hSY
        let k := rightExactEmbedding RI outI RX outX RY outY f g
        refine ⟨k.comp a, ?_⟩
        intro p hp
        obtain ⟨y, heq⟩ := hright hp
        have hy : y ∈ SY := by
          change inclRight f.toFun g.toFun y ∈ S
          rw [heq]
          exact hp
        obtain ⟨z, hz⟩ := ha hy
        refine ⟨z, ?_⟩
        change inclRight f.toFun g.toFun (a.toFun z) = p
        rw [hz, heq]

end GluingEPPA.Sparsening.Tree
