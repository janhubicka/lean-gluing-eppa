import GluingEPPA.Sparsening.OrbitTreeBaseChange
import GluingEPPA.Sparsening.UnaryGeneratedClosure

/-!
# The finite complete-overlap tower

The stages below are the actual canonical refinements, not an abstract
sequence with a postulated local-tree property. The checked bounded step
and exact root transport give the numerical induction for every stage.
We also construct the composite homomorphism-embedding to the initial
stage and the surjective exact identification of every distinguished root.

EPPA extension families and forgetting the auxiliary J are separate
obligations. No claim of their assembly is hidden in this local theorem.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v t
variable {L : Nat → Type u} {F : Type t}
open scoped Classical
noncomputable section
attribute [local instance] chartsFintype edgesFintype

/-- The empty induced test embeds into any induced root of the same
ambient structure. This retains nullary truth values, even for empty roots. -/
def emptyTestExact {B : Type v} (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root S : Set B) [IsEmpty S] :
    Tree.ExactUnaryEmbedding (inducedRelations R S) (inducedUnary out S)
      (inducedRelations R root) (inducedUnary out root) := by
  let j : S → root := fun x => isEmptyElim x
  refine { toFun := j, injective := ?_, rel_iff := ?_, out_eq := ?_ }
  · intro x y h
    exact isEmptyElim x
  · intro n r xs
    change R.rel r (fun i => (j (xs i)).val) ↔ R.rel r (fun i => (xs i).val)
    have ht : (fun i => (j (xs i)).val) = (fun i => (xs i).val) := by
      funext i
      exact isEmptyElim (xs i)
    rw [ht]
  · intro f x
    exact isEmptyElim x

/-- A finite expanded structure with an actual closed complete-J root.
The root can be empty and no EPPA hypothesis is needed for local trees. -/
structure FiniteRooted (L : Nat → Type u) (F : Type t) where
  Carrier : Type v
  finite : Finite Carrier
  rel : RelStructure (WithJ L) Carrier
  out : F → Carrier → Set Carrier
  root : Set Carrier
  root_closed : UnaryClosed out (fun x => x ∈ root)
  root_J : Tree.IsJClique rel root

attribute [instance] FiniteRooted.finite

namespace FiniteRooted

variable (C : FiniteRooted.{u,v,t} L F)

abbrev rootRelations := inducedRelations C.rel C.root
abbrev rootOutputs := inducedUnary C.out C.root

/-- One actual complete-overlap refinement, with its zero-valuation root. -/
def refine : FiniteRooted.{u,v,t} L F where
  Carrier := Vertex C.rel C.out C.root
  finite := inferInstance
  rel := relations C.rel C.out C.root
  out := outputs C.rel C.out C.root
  root := refinedRoot C.rel C.out C.root C.root_closed
  root_closed := refinedRoot_closed C.rel C.out C.root C.root_closed
  root_J := refinedRoot_J_complete C.rel C.out C.root C.root_closed C.root_J

/-- The bounded local-tree invariant, based on the stage's actual root. -/
def LocalTrees (k : Nat) : Prop :=
  ∀ (S : Set C.Carrier), UnaryClosed C.out (fun x => x ∈ S) →
    Nat.card S ≤ k → HasTreeImage C.rootRelations C.rootOutputs
      (inducedRelations C.rel S) (inducedUnary C.out S)

theorem localTrees_zero : C.LocalTrees 0 := by
  intro S hS hSmall
  letI : Fintype S := Fintype.ofFinite S
  have hzero : Fintype.card S = 0 := by
    have h : Fintype.card S ≤ 0 := by
      simpa only [Nat.card_eq_fintype_card] using hSmall
    omega
  letI : IsEmpty S := Fintype.card_eq_zero_iff.mp hzero
  exact ⟨C.root, C.rootRelations, C.rootOutputs,
    Tree.FullATree.singleton C.rootRelations C.rootOutputs,
    ⟨(emptyTestExact C.rel C.out C.root S).toHomEmbedding⟩⟩

/-- The stage's complete J-root discharges the old-chart hypothesis;
the conclusion is based on the new root, not the old root. -/
theorem localTrees_refine (k : Nat) (h : C.LocalTrees k) :
    C.refine.LocalTrees (k + 1) := by
  intro S hS hSmall
  exact localTreeOfBoundedOldTrees_nextRoot C.rel C.out C.root
    C.root_closed (fun x y hx hy => C.root_J x hx y hy) k h S hS hSmall

/-- The actual finite sequence of canonical quotient structures. -/
def tower (C : FiniteRooted.{u,v,t} L F) : Nat → FiniteRooted.{u,v,t} L F
  | 0 => C
  | n + 1 => (tower C n).refine

/-- Every closed test with at most n vertices in stage n has a strict
full-root tree image. The empty base case includes all nullary symbols. -/
theorem tower_localTrees (n : Nat) : (C.tower n).LocalTrees n := by
  induction n with
  | zero => exact C.localTrees_zero
  | succ n ih => exact (C.tower n).localTrees_refine n ih

/-- The one-step projection, without global injectivity or surjectivity. -/
def projection : Tree.UnaryHomEmbedding C.refine.rel C.refine.out C.rel C.out :=
  projectionHomEmbedding C.rel C.out C.root

/-- Composite of the actual canonical projections back to stage zero. -/
def projectToBase (C : FiniteRooted.{u,v,t} L F) : (n : Nat) →
    Tree.UnaryHomEmbedding (C.tower n).rel (C.tower n).out C.rel C.out
  | 0 => (Tree.ExactUnaryEmbedding.refl C.rel C.out).toHomEmbedding
  | n + 1 => (projectToBase C n).comp (C.tower n).projection

/-- Complete unary fibres are preserved by the composite as well as
by each individual projection. -/
theorem projectToBase_fibres (n : Nat) (f : F) (x : (C.tower n).Carrier) :
    (C.projectToBase n).toFun '' (C.tower n).out f x =
      C.out f ((C.projectToBase n).toFun x) :=
  (C.projectToBase n).out_eq f x

/-- Consecutive roots are exactly isomorphic; composing gives the fixed
original root as the base of every stage's tree class. -/
def rootEmbedding (C : FiniteRooted.{u,v,t} L F) : (n : Nat) → Tree.ExactUnaryEmbedding
    C.rootRelations C.rootOutputs (C.tower n).rootRelations (C.tower n).rootOutputs
  | 0 => Tree.ExactUnaryEmbedding.refl C.rootRelations C.rootOutputs
  | n + 1 =>
      (refinedRootExact (C.tower n).rel (C.tower n).out (C.tower n).root
        (C.tower n).root_closed).comp (rootEmbedding C n)

theorem rootEmbedding_surjective (n : Nat) :
    Function.Surjective (C.rootEmbedding n).toFun := by
  induction n with
  | zero => exact fun x => ⟨x, rfl⟩
  | succ n ih =>
      intro y
      obtain ⟨x, hx⟩ := refinedRootExact_surjective (C.tower n).rel
        (C.tower n).out (C.tower n).root (C.tower n).root_closed y
      obtain ⟨a, ha⟩ := ih x
      refine ⟨a, ?_⟩
      change (refinedRootExact (C.tower n).rel (C.tower n).out
        (C.tower n).root (C.tower n).root_closed).toFun
          ((C.rootEmbedding n).toFun a) = y
      rw [ha, hx]

/-- The composite projection is the identity on the distinguished root
under the explicit stage-root identifications. -/
theorem projectToBase_root (n : Nat) (a : C.root) :
    (C.projectToBase n).toFun ((C.rootEmbedding n).toFun a).val = a.val := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- The finite-tower local conclusion with the ORIGINAL root fixed. -/
theorem tower_localTrees_fixedBase (n : Nat) (S : Set (C.tower n).Carrier)
    (hS : UnaryClosed (C.tower n).out (fun x => x ∈ S))
    (hSmall : Nat.card S ≤ n) :
    HasTreeImage C.rootRelations C.rootOutputs
      (inducedRelations (C.tower n).rel S) (inducedUnary (C.tower n).out S) :=
  HasTreeImage.changeBase (C.rootEmbedding n) (C.rootEmbedding_surjective n)
    (C.tower_localTrees n S hS hSmall)

/-- Finiteness of the local target follows from its literal finite-block
tree certificate; it is not another assumption in the iteration. -/
theorem tower_local_finite_target (n : Nat) (S : Set (C.tower n).Carrier)
    (hS : UnaryClosed (C.tower n).out (fun x => x ∈ S))
    (hSmall : Nat.card S ≤ n) :
    ∃ (V : Type v) (RV : RelStructure (WithJ L) V) (outV : F → V → Set V),
      Finite V ∧ Tree.FullATree C.rootRelations C.rootOutputs RV outV ∧
      Nonempty (Tree.UnaryHomEmbedding
        (inducedRelations (C.tower n).rel S) (inducedUnary (C.tower n).out S)
        RV outV) := by
  obtain ⟨V, RV, outV, tree, hmap⟩ := C.tower_localTrees_fixedBase n S hS hSmall
  exact ⟨V, RV, outV,
    Tree.FullATree.carrier_finite C.rootRelations C.rootOutputs RV outV tree,
    tree, hmap⟩

end FiniteRooted
end
end GluingEPPA.Sparsening.OrbitAtlas
