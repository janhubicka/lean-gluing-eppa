import GluingEPPA.Sparsening.CompleteJPartialAut

/-!
# The canonical sparsening witness in the original language

All four conclusions concern the SAME finite stage, with the SAME root
embedding. The stage is max(1,n): the local bound needs n refinements and
faithfulness needs a positive stage. The extension family is transported
from all original partial automorphisms, not just those preserving an
arbitrary auxiliary expansion. Here the auxiliary expansion is complete.
-/
namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v t
variable {L : Nat → Type u} {F : Type t} {B0 : Type v}

/-- The simultaneous conclusions for a distinguished original closed root.
For an irreducible original root, the strict targets are tree amalgams in
the manuscript's convention. All maps refer to the same finite witness. -/
structure SparseningWitness (R0 : RelStructure L B0) (out0 : F → B0 → Set B0)
    (root : Set B0) (n : Nat) where
  Carrier : Type v
  finite : Finite Carrier
  rel : RelStructure L Carrier
  out : F → Carrier → Set Carrier
  rootEmbedding : Tree.ExactUnaryEmbedding
    (inducedRelations R0 root) (inducedUnary out0 root) rel out
  extension : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root) →
    Aut rel out
  extension_spec : ExtendsAlong rootEmbedding.toFun extension
  projection : Tree.UnaryHomEmbedding rel out R0 out0
  projection_root : ∀ a : root, projection.toFun (rootEmbedding.toFun a) = a.val
  faithful : ∀ (S : Set Carrier), UnaryClosed out (fun x => x ∈ S) →
    IsIrreducible (inducedRelations rel S) (inducedUnary out S) →
    ∃ g : Aut rel out, ∀ x, x ∈ S → g.perm x ∈ Set.range rootEmbedding.toFun
  local_trees : ∀ (S : Set Carrier), UnaryClosed out (fun x => x ∈ S) →
    Nat.card S ≤ n →
    ∃ (V : Type v) (RV : RelStructure L V) (outV : F → V → Set V),
      Finite V ∧ Tree.FullATree (inducedRelations R0 root) (inducedUnary out0 root)
        RV outV ∧ Nonempty (Tree.UnaryHomEmbedding
          (inducedRelations rel S) (inducedUnary out S) RV outV)

attribute [instance] SparseningWitness.finite

open scoped Classical
noncomputable section
variable [Finite B0]
variable (R0 : RelStructure L B0) (out0 : F → B0 → Set B0) (root : Set B0)
variable (hr : UnaryClosed out0 (fun x => x ∈ root))

/-- Lift the input extension choices to the complete-J expansion. -/
def initialFamily
    (H0 : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root) →
      Aut R0 out0) :
    ClosedPartialAut (initialRooted R0 out0 root hr).rootRelations
      (initialRooted R0 out0 root hr).rootOutputs →
      Aut (initialRooted R0 out0 root hr).rel (initialRooted R0 out0 root hr).out :=
  fun p => (H0 p.forgetJ).withCompleteJ

theorem initialFamily_extends
    (H0 : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root) →
      Aut R0 out0) (h0 : ExtendsAlong Subtype.val H0) :
    ExtendsAlong Subtype.val (initialFamily R0 out0 root hr H0) := by
  intro p x
  exact h0 p.forgetJ x

theorem initialFamily_coherent
    (H0 : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root) →
      Aut R0 out0) (hc : CoherentFamily H0) :
    CoherentFamily (initialFamily R0 out0 root hr H0) := by
  intro f g h hcomp
  apply Aut.ext_perm
  intro x
  exact congrArg (fun a => a.perm x) (hc f.forgetJ g.forgetJ h.forgetJ hcomp.forgetJ)

/-- Explicit canonical witness from one simultaneous system of input extensions. -/
def sparseningFromExtensions
    (H0 : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root) →
      Aut R0 out0) (h0 : ExtendsAlong Subtype.val H0) (n : Nat) :
    SparseningWitness R0 out0 root n := by
  let C := initialRooted R0 out0 root hr
  let m := max 1 n
  let Hplus := initialFamily R0 out0 root hr H0
  have hplus : ExtendsAlong Subtype.val Hplus :=
    initialFamily_extends R0 out0 root hr H0 h0
  let E := ((C.tower m).rootAmbient (C.rootEmbedding m)).forgetJ
  let H : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root) →
      Aut (forgetJRelations (C.tower m).rel) (C.tower m).out :=
    fun p => (C.towerFamily Hplus m p.withCompleteJ).forgetJ
  refine {
    Carrier := (C.tower m).Carrier
    finite := (C.tower m).finite
    rel := forgetJRelations (C.tower m).rel
    out := (C.tower m).out
    rootEmbedding := E
    extension := H
    extension_spec := ?_
    projection := C.reductProjection m
    projection_root := ?_
    faithful := ?_
    local_trees := ?_ }
  · intro p x
    exact C.towerFamily_extends Hplus hplus m p.withCompleteJ x
  · intro a
    exact C.reductProjection_root m a
  · intro S hS hirr
    have hm : 0 < m := lt_of_lt_of_le (by decide : 0 < (1 : Nat)) (le_max_left 1 n)
    obtain ⟨g, hg⟩ := C.tower_reduct_faithful m hm S hS hirr
    refine ⟨g, ?_⟩
    intro x hx
    obtain ⟨a, ha⟩ := C.rootEmbedding_surjective m ⟨g.perm x, hg x hx⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · intro S hS hSmall
    exact C.tower_reduct_local_finite_target m S hS (le_trans hSmall (le_max_right 1 n))

/-- The very same witness preserves coherence whenever the chosen input family does. -/
theorem sparseningFromExtensions_coherent
    (H0 : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root) →
      Aut R0 out0) (h0 : ExtendsAlong Subtype.val H0) (hc : CoherentFamily H0) (n : Nat) :
    CoherentFamily (sparseningFromExtensions R0 out0 root hr H0 h0 n).extension := by
  let C := initialRooted R0 out0 root hr
  let Hplus := initialFamily R0 out0 root hr H0
  have hp : CoherentFamily Hplus := initialFamily_coherent R0 out0 root hr H0 hc
  have ht := C.towerFamily_coherent Hplus hp (max 1 n)
  intro f g h hcomp
  apply Aut.ext_perm
  intro x
  exact congrArg (fun a => a.perm x)
    (ht f.withCompleteJ g.withCompleteJ h.withCompleteJ hcomp.withCompleteJ)

/-- Ordinary EPPA supplies simultaneous choices by choice; the geometry
comes from the canonical tower, not a different existing EPPA theorem. -/
theorem sparsening_eppa
    (hirr : IsIrreducible (inducedRelations R0 root) (inducedUnary out0 root))
    (eppa : ∀ p : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root),
      ∃ h : Aut R0 out0, ∀ x : p.dom, h.perm x.val.val = (p.map.toFun x).val.val)
    (n : Nat) : Nonempty (SparseningWitness R0 out0 root n) := by
  classical
  choose H0 h0 using eppa
  exact ⟨sparseningFromExtensions R0 out0 root hr H0 h0 n⟩

/-- The coherent version, with the original irreducible A as the distinguished root. -/
theorem coherent_sparsening_eppa
    (hirr : IsIrreducible (inducedRelations R0 root) (inducedUnary out0 root))
    (H0 : ClosedPartialAut (inducedRelations R0 root) (inducedUnary out0 root) → Aut R0 out0)
    (h0 : ExtendsAlong Subtype.val H0) (hc : CoherentFamily H0) (n : Nat) :
    ∃ W : SparseningWitness R0 out0 root n, CoherentFamily W.extension :=
  ⟨sparseningFromExtensions R0 out0 root hr H0 h0 n,
    sparseningFromExtensions_coherent R0 out0 root hr H0 h0 hc n⟩

end
end GluingEPPA.Sparsening.OrbitAtlas
