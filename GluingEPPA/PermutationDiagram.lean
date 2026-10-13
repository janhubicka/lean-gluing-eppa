import GluingEPPA.AffineLift

/-!
The finite-permutation base diagram, prior to the Boolean cover.

An indexed partial isomorphism is represented by its transport graph.  The
assumptions are elementary finite permutation data, not an EPPA conclusion.
The generated relation has the manuscript's orientation:
  b ∘ sigma_i = a,  and  x --f_i--> y.
-/
namespace GluingEPPA
universe u v w z

structure PermutationDiagramData
    {L : Nat → Type u} {A : Type v}
    (S : RelStructure L A) (U : Type w) (I : Type z) where
  incl : A ↪ U
  sigma : I → (U ≃ U)
  sigma_injective : Function.Injective sigma
  inverse : I → I
  sigma_inverse : ∀ i, sigma (inverse i) = (sigma i).symm
  transport : I → A → A → Prop
  transport_inverse : ∀ i x y, transport i x y ↔ transport (inverse i) y x
  transport_sigma : ∀ i x y, transport i x y → sigma i (incl x) = incl y
  transport_rel : ∀ {n} (r : L n) (i : I) (x y : Fin n → A),
    (∀ j, transport i (x j) (y j)) → (S.rel r x ↔ S.rel r y)

namespace PermutationDiagramData
variable {L : Nat → Type u} {A : Type v} {U : Type w} {I : Type z}
variable {S : RelStructure L A} (D : PermutationDiagramData S U I)

/-- Forward point transport: the new copy b satisfies b(sigma_i(u)) = a(u). -/
def system : System (U ≃ U) A where
  step p q := ∃ i : I, (∀ u, q.1 (D.sigma i u) = p.1 u) ∧ D.transport i p.2 q.2
  reverse := by
    intro p q h
    obtain ⟨i, hb, hxy⟩ := h
    refine ⟨D.inverse i, ?_, (D.transport_inverse i p.2 q.2).mp hxy⟩
    intro u
    rw [D.sigma_inverse i]
    simpa using (hb ((D.sigma i).symm u)).symm

/-- Each generator is uniquely determined by an ordered edge. -/
theorem label_unique (a b : U ≃ U) {i j : I}
    (hi : ∀ u, b (D.sigma i u) = a u)
    (hj : ∀ u, b (D.sigma j u) = a u) : i = j :=
  D.sigma_injective (Equiv.ext (fun u => b.injective ((hi u).trans (hj u).symm)))

/-- No generator is a loop if the auxiliary permutations are nonidentity. -/
theorem loop_free (hne : ∀ i, D.sigma i ≠ Equiv.refl U) (a : U ≃ U) :
    ¬ ∃ x y, D.system.step (a, x) (a, y) := by
  rintro ⟨x, y, i, heq, _⟩
  apply hne i
  apply Equiv.ext
  intro u
  exact a.injective (heq u)

/-- The faithful empty-language realization rho(a)(x)=a(incl x). -/
def frame : D.system.Frame U where
  value := fun a x => a (D.incl x)
  injective := by
    intro a x y h
    exact D.incl.injective (a.injective h)
  commute := by
    intro a b x y h
    obtain ⟨i, hb, hxy⟩ := h
    change a (D.incl x) = b (D.incl y)
    calc
      a (D.incl x) = b (D.sigma i (D.incl x)) := (hb _).symm
      _ = b (D.incl y) := congrArg b (D.transport_sigma i x y hxy)

/-- Edges preserve and reflect relations on whole tuples, as required by replay. -/
theorem respects : D.system.RespectsRelations S := by
  intro n r a b x y hs
  cases n with
  | zero =>
    have hxy : x = y := funext (fun j => Fin.elim0 j)
    rw [hxy]
  | succ k =>
    obtain ⟨i, hi, _⟩ := hs ⟨0, Nat.zero_lt_succ k⟩
    apply D.transport_rel r i x y
    intro j
    obtain ⟨i', hj, hpoint⟩ := hs j
    have hid : i' = i := D.label_unique a b hj hi
    simpa [hid] using hpoint

/-- Left multiplication on the base permutation vertices preserves all labels. -/
def leftShift (g : U ≃ U) : D.system.Symmetry where
  perm :=
    { toFun := fun a => a.trans g
      invFun := fun a => a.trans g.symm
      left_inv := by
        intro a
        apply Equiv.ext
        intro u
        simp
      right_inv := by
        intro a
        apply Equiv.ext
        intro u
        simp }
  step_iff := by
    intro a b x y
    constructor
    · rintro ⟨i, hb, hxy⟩
      refine ⟨i, ?_, hxy⟩
      intro u
      apply g.injective
      exact hb u
    · rintro ⟨i, hb, hxy⟩
      refine ⟨i, ?_, hxy⟩
      intro u
      exact congrArg g (hb u)

/-- The forward edge at the root is labelled by the inverse generator. -/
theorem root_shift (i : I) :
    (D.leftShift (D.sigma i)).perm (Equiv.refl U) = D.sigma i := by
  apply Equiv.ext
  intro u
  rfl

/-- The incoming edge has the original label f_i, as required for EPPA. -/
theorem root_incoming (i : I) {x y : A} (h : D.transport i x y) :
    D.system.step
      ((D.leftShift (D.sigma i)).perm (Equiv.refl U), x)
      (Equiv.refl U, y) := by
  refine ⟨i, ?_, h⟩
  intro u
  rfl

end PermutationDiagramData
end GluingEPPA
