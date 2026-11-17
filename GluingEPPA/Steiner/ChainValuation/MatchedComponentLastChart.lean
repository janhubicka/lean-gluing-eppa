import GluingEPPA.Steiner.ChainValuation.LinkStepChartEdges
import GluingEPPA.Steiner.ChainValuation.NormalizedTwoBlockComponent
import GluingEPPA.Steiner.ChainValuation.ReachComponentAction
import GluingEPPA.Steiner.ChainValuation.NormalizedChainTrace

/-!
# Preserving the last Cayley chart in a normalized matched extension

The finite component-normalization induction needs more than an abstract
equivalence onto the old component. Its last normalized block must have
specified coordinates in the actual last original block. This module
records that invariant and preserves it through one matched attachment.

The attaching maps are the genuine triple-mask Link inclusions. The
normalized old attachment is translated by the chosen shift, while the
new one is unshifted. The entire original attaching fibre is obtained
from the checked old-component fibre theorem; it is not an extra premise.

The result is an exact component equivalence, genuine-edge reflection,
and the pointwise last-coordinate identity required for the next step.
The separated finite-list induction and its identification with a recorded
smaller chain test remain separate obligations.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The induction invariant retains both genuine edges and the exact
coordinates of the final restricted Cayley block. -/
structure ComponentLastChart (M : Proper S) (R : BuildResult D S old L)
    (q : R.state.Space) where
  source : ChainState.{u,u} E (block S old (Step.meet S M R.current.1))
  trace : NormalizedChainTrace D S old L M R.current.1 source
  base : (old R.current.1).Carrier
  equiv : source.Space ≃ MatchingReachComponent R.state.matching M.val q
  last_val : ∀ t : (old (Step.meet S M R.current.1)).Carrier,
    (equiv (source.lastEmbed t)).val =
      R.state.lastEmbed
        (base * (L (Step.meet S M R.current.1) R.current.1
          Finset.inter_subset_right).incl t)
  entry_mem : ∀ t : (old (Step.meet S M R.current.1)).Carrier,
    t ∈ source.entry →
      base * (L (Step.meet S M R.current.1) R.current.1
        Finset.inter_subset_right).incl t ∈ R.state.entry
  edge_iff : ∀ e ∈ M.val, ∀ x z : source.Space,
    (source.matching e).Rel x z ↔
      (R.state.matching e).Rel (equiv x).val (equiv z).val

/-- The completed actions, including their fixed points, follow from
the exact component chart and genuine-edge reflection. -/
theorem ComponentLastChart.perm_val
    {M : Proper S} {R : BuildResult D S old L} {q : R.state.Space}
    (C : ComponentLastChart D S old L M R q)
    (e : E) (he : e ∈ M.val) (x : C.source.Space) :
    (C.equiv ((C.source.matching e).perm x)).val =
      (R.state.matching e).perm (C.equiv x).val :=
  componentChart_perm_val_of_edge_iff R.state.matching M.val q
    C.source.matching C.equiv C.edge_iff e he x

/-- In one original Cayley block, the invariant is the translated
earlier group with its genuine restricted Cayley edges. -/
noncomputable def ComponentLastChart.initial
    (M : Proper S) (x : Atom S old) (q : (old x.1).Carrier) :
    ComponentLastChart D S old L M (LinkChain.initial D S old L x) q := by
  let F := restrictedBlock_cosetEquiv D S old L M x.1 q
  let f :
      {z : (old x.1).Carrier //
        z ∈ leftCoset (restrictedSubgroup D S old L M x.1) q} →
      MatchingReachComponent (LinkChain.initial D S old L x).state.matching M.val q :=
    fun z => ⟨z.val,
      (restricted_block_reach_iff_coset D S old L M x.1 q z.val).mpr
        z.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z z' h
      have hv : (f z).val = (f z').val := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro z
      refine ⟨⟨z.val,
        (restricted_block_reach_iff_coset D S old L M x.1 q z.val).mp
          z.property⟩, ?_⟩
      exact Subtype.ext rfl
  refine
    { source := ChainState.first (block S old (Step.meet S M x.1))
      trace := NormalizedChainTrace.single x.1
      base := q
      equiv := F.trans (Equiv.ofBijective f hf)
      last_val := ?_
      entry_mem := ?_
      edge_iff := ?_ }
  · intro t
    rfl
  · intro t ht
    exact False.elim ht
  · intro e he a b
    exact restrictedBlock_cosetEquiv_edge_iff D S old L M x.1 q e he a b

/-- The actual triple-mask inclusions identify all shared generators
of the two normalized last blocks. -/
theorem normalizedCommon_shared_edge (M A B : Proper S) (e : E)
    (heA : e ∈ (Step.meet S M A).val)
    (heB : e ∈ (Step.meet S M B).val) :
    ∃ t : (old (Step.meet S M (common S A B))).Carrier,
      normalizedCommonLeft D S old L M A B t =
        (old (Step.meet S M A)).edge e ∧
      normalizedCommonRight D S old L M A B t =
        (old (Step.meet S M B)).edge e := by
  have he : e ∈ (Step.meet S M (common S A B)).val :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp heA).1,
      Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp heA).2, (Finset.mem_inter.mp heB).2⟩⟩
  refine ⟨(old (Step.meet S M (common S A B))).edge e, ?_, ?_⟩
  · exact (L _ _ _).incl_edge e he
  · exact (L _ _ _).incl_edge e he

section Matched

variable (M : Proper S) (R : BuildResult D S old L) (y : Atom S old)
variable (hprev : LastMaskCoset D S old L M R)
variable (q : R.state.Space)
variable (k : (old (common S R.current.1 y.1)).Carrier)
variable (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val
  q (R.state.lastEmbed
    (R.current.2 * left D S old L R.current.1 y.1 k)))

/-- The complete interface of the whole old component is the literal
triple-mask group, with coordinate map `t ↦ k * incl t`. -/
noncomputable def stepMatchedComponent_interfaceEquiv :
    (old (Step.meet S M (common S R.current.1 y.1))).Carrier ≃
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).Interface := by
  let U := matchedLinkCosetRestriction
    D S old L M R.current.1 y.1 R.current.2 k
  let W := stepMatchedOldComponentRestriction
    D S old L M R y hprev q k hq
  let F : U.Interface → W.Interface := fun z =>
    ⟨z.val, (step_oldComponent_attachment_fibre_iff
      D S old L M R y hprev q k hq z.val).mpr
        ((U.agree z.val).mp z.property)⟩
  have hInj : Function.Injective F := by
    intro z z' h
    have hv : (F z).val = (F z').val := congrArg Subtype.val h
    exact Subtype.ext hv
  have hSurj : Function.Surjective F := by
    intro z
    let z' : U.Interface :=
      ⟨z.val, (U.agree z.val).mpr
        ((step_oldComponent_attachment_fibre_iff
          D S old L M R y hprev q k hq z.val).mp z.property)⟩
    exact ⟨z', Subtype.ext rfl⟩
  exact (matchedLinkCoset_interface_equiv
    D S old L M R.current.1 y.1 R.current.2 k).trans
      (Equiv.ofBijective F ⟨hInj, hSurj⟩)

theorem stepMatchedComponent_interfaceEquiv_val
    (t : (old (Step.meet S M (common S R.current.1 y.1))).Carrier) :
    (stepMatchedComponent_interfaceEquiv
      D S old L M R y hprev q k hq t).val =
        k * normalizedCommonInterface D S old L M R.current.1 y.1 t := rfl

/-- The new restricted Cayley chart commutes with the entire actual
right attaching fibre. -/
theorem stepMatchedComponent_right_square
    (t : (old (Step.meet S M (common S R.current.1 y.1))).Carrier) :
    let W := stepMatchedOldComponentRestriction
      D S old L M R y hprev q k hq
    restrictedBlock_cosetEquiv D S old L M y.1
        (right D S old L R.current.1 y.1 k)
        (normalizedCommonRight D S old L M R.current.1 y.1 t) =
      W.rightAttach
        (stepMatchedComponent_interfaceEquiv
          D S old L M R y hprev q k hq t) := by
  apply Subtype.ext
  change
    (right D S old L R.current.1 y.1 k) *
        (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl
          (normalizedCommonRight D S old L M R.current.1 y.1 t) =
      right D S old L R.current.1 y.1
        (k * normalizedCommonInterface D S old L M R.current.1 y.1 t)
  exact normalized_new_boundary
    (right D S old L R.current.1 y.1)
    (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl
    (normalizedCommonInterface D S old L M R.current.1 y.1)
    (normalizedCommonRight D S old L M R.current.1 y.1)
    (normalizedCommon_right_square D S old L M R.current.1 y.1) k t

variable (C : ComponentLastChart D S old L M R q)
variable (shift : (old (Step.meet S M R.current.1)).Carrier)
variable (hbase :
  C.base * (L (Step.meet S M R.current.1) R.current.1
    Finset.inter_subset_right).incl shift =
      R.current.2 * left D S old L R.current.1 y.1 k)

include hbase in
/-- The old chart's last-coordinate invariant and the one chosen
shift equation imply the complete left attaching square. -/
theorem ComponentLastChart.left_square
    (t : (old (Step.meet S M (common S R.current.1 y.1))).Carrier) :
    let W := stepMatchedOldComponentRestriction
      D S old L M R y hprev q k hq
    C.equiv (attachInto C.source.lastEmbed shift
        (normalizedCommonLeft D S old L M R.current.1 y.1) t) =
      W.leftAttach
        (stepMatchedComponent_interfaceEquiv
          D S old L M R y hprev q k hq t) := by
  apply Subtype.ext
  change
    (C.equiv (C.source.lastEmbed
      (shift * normalizedCommonLeft D S old L M R.current.1 y.1 t))).val = _
  rw [C.last_val]
  change R.state.lastEmbed
      (C.base * (L (Step.meet S M R.current.1) R.current.1
        Finset.inter_subset_right).incl
          (shift * normalizedCommonLeft D S old L M R.current.1 y.1 t)) =
    R.state.lastEmbed
      (R.current.2 * left D S old L R.current.1 y.1
        (k * normalizedCommonInterface D S old L M R.current.1 y.1 t))
  apply congrArg R.state.lastEmbed
  exact normalized_old_boundary
    (left D S old L R.current.1 y.1)
    (L (Step.meet S M R.current.1) R.current.1
      Finset.inter_subset_right).incl
    (normalizedCommonInterface D S old L M R.current.1 y.1)
    (normalizedCommonLeft D S old L M R.current.1 y.1)
    (normalizedCommon_left_square D S old L M R.current.1 y.1)
    C.base R.current.2 k shift hbase t

variable (hsep :
  match R.previous with
  | none => True
  | some p => tripleSeparated D S old L p R.current y)

include hbase hsep in
/-- The normalized separation follows from the original separation:
translated entry points lie in the original entry, and translated
exit points lie in the original exit. -/
theorem ComponentLastChart.normalized_attachment_disjoint :
    Disjoint C.source.entry
      (exitSet (block S old (Step.meet S M R.current.1)) shift
        (normalizedCommonLeft D S old L M R.current.1 y.1)) := by
  apply Set.disjoint_left.mpr
  intro z hz hExit
  obtain ⟨t, rfl⟩ := hExit
  have hEntry := C.entry_mem _ hz
  have hOldExit :
      C.base * (L (Step.meet S M R.current.1) R.current.1
        Finset.inter_subset_right).incl
          (shift * normalizedCommonLeft D S old L M R.current.1 y.1 t) ∈
      exitSet (block S old R.current.1) R.current.2
        (left D S old L R.current.1 y.1) := by
    refine ⟨k * normalizedCommonInterface D S old L M R.current.1 y.1 t, ?_⟩
    exact (normalized_old_boundary
      (left D S old L R.current.1 y.1)
      (L (Step.meet S M R.current.1) R.current.1
        Finset.inter_subset_right).incl
      (normalizedCommonInterface D S old L M R.current.1 y.1)
      (normalizedCommonLeft D S old L M R.current.1 y.1)
      (normalizedCommon_left_square D S old L M R.current.1 y.1)
      C.base R.current.2 k shift hbase t).symm
  exact Set.disjoint_left.mp
    (step_attachment_disjoint D S old L R y hsep) hEntry hOldExit

/-- The actual shifted normalized attachment has an exact chart onto
the full component in the original next chain state. -/
noncomputable def ComponentLastChart.extendEquiv :
    ExtendedSpace
      (block S old (Step.meet S M R.current.1))
      (block S old (Step.meet S M y.1)) C.source shift
      (normalizedCommonLeft D S old L M R.current.1 y.1)
      (normalizedCommonRight D S old L M R.current.1 y.1)
      (normalizedCommonLeft_injective D S old L M R.current.1 y.1)
      (normalizedCommonRight_injective D S old L M R.current.1 y.1) ≃
    MatchingReachComponent (step D S old L R y hsep).state.matching M.val
      (oldEmbed (block S old R.current.1) (block S old y.1)
        R.state R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1) q) :=
  stepComponentChart_equivActual
    D S old L M R y hsep hprev q k hq
    (attachInto C.source.lastEmbed shift
      (normalizedCommonLeft D S old L M R.current.1 y.1))
    (normalizedCommonRight D S old L M R.current.1 y.1)
    (attachInto_injective C.source.lastEmbed C.source.lastInjective shift
      (normalizedCommonLeft D S old L M R.current.1 y.1)
      (normalizedCommonLeft_injective D S old L M R.current.1 y.1))
    (normalizedCommonRight_injective D S old L M R.current.1 y.1)
    C.equiv
    (restrictedBlock_cosetEquiv D S old L M y.1
      (right D S old L R.current.1 y.1 k))
    (stepMatchedComponent_interfaceEquiv D S old L M R y hprev q k hq)
    (C.left_square D S old L M R y hprev q k hq shift hbase)
    (stepMatchedComponent_right_square D S old L M R y hprev q k hq)

/-- The new last-block coordinate is exactly the translated original
Cayley coordinate. This is the pointwise invariant needed at the next
attachment, rather than only an equality of chart images. -/
theorem ComponentLastChart.extendEquiv_last_val
    (t : (old (Step.meet S M y.1)).Carrier) :
    (C.extendEquiv D S old L M R y hprev q k hq shift hbase hsep
      (newEmbed
        (block S old (Step.meet S M R.current.1))
        (block S old (Step.meet S M y.1)) C.source shift
        (normalizedCommonLeft D S old L M R.current.1 y.1)
        (normalizedCommonRight D S old L M R.current.1 y.1)
        (normalizedCommonLeft_injective D S old L M R.current.1 y.1)
        (normalizedCommonRight_injective D S old L M R.current.1 y.1) t)).val =
      (step D S old L R y hsep).state.lastEmbed
        (right D S old L R.current.1 y.1 k *
          (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl t) := rfl

/-- Earlier normalized points retain the preceding component chart
under the genuine old-side embedding. -/
theorem ComponentLastChart.extendEquiv_old_val (x : C.source.Space) :
    (C.extendEquiv D S old L M R y hprev q k hq shift hbase hsep
      (oldEmbed
        (block S old (Step.meet S M R.current.1))
        (block S old (Step.meet S M y.1)) C.source shift
        (normalizedCommonLeft D S old L M R.current.1 y.1)
        (normalizedCommonRight D S old L M R.current.1 y.1)
        (normalizedCommonLeft_injective D S old L M R.current.1 y.1)
        (normalizedCommonRight_injective D S old L M R.current.1 y.1) x)).val =
      oldEmbed (block S old R.current.1) (block S old y.1)
        R.state R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1) (C.equiv x).val := rfl

/-- The concrete normalized component chart preserves and reflects
the actual quotient edges; no fixed-point assumption is used. -/
theorem ComponentLastChart.extendEquiv_edge_iff
    (e : E) (he : e ∈ M.val)
    (x z : ExtendedSpace
      (block S old (Step.meet S M R.current.1))
      (block S old (Step.meet S M y.1)) C.source shift
      (normalizedCommonLeft D S old L M R.current.1 y.1)
      (normalizedCommonRight D S old L M R.current.1 y.1)
      (normalizedCommonLeft_injective D S old L M R.current.1 y.1)
      (normalizedCommonRight_injective D S old L M R.current.1 y.1)) :
    pushoutLabelRel
      (fun e => (C.source.matching e).Rel)
      (fun e => ((block S old (Step.meet S M y.1)).matching e).Rel)
      (attachInto C.source.lastEmbed shift
        (normalizedCommonLeft D S old L M R.current.1 y.1))
      (normalizedCommonRight D S old L M R.current.1 y.1)
      (attachInto_injective C.source.lastEmbed C.source.lastInjective shift
        (normalizedCommonLeft D S old L M R.current.1 y.1)
        (normalizedCommonLeft_injective D S old L M R.current.1 y.1))
      (normalizedCommonRight_injective D S old L M R.current.1 y.1)
      e x z ↔
    ((step D S old L R y hsep).state.matching e).Rel
      (C.extendEquiv D S old L M R y hprev q k hq shift hbase hsep x).val
      (C.extendEquiv D S old L M R y hprev q k hq shift hbase hsep z).val := by
  exact stepComponentChart_genuine_edge_iff
    D S old L M R y hsep hprev q k hq
    (attachInto C.source.lastEmbed shift
      (normalizedCommonLeft D S old L M R.current.1 y.1))
    (normalizedCommonRight D S old L M R.current.1 y.1)
    (attachInto_injective C.source.lastEmbed C.source.lastInjective shift
      (normalizedCommonLeft D S old L M R.current.1 y.1)
      (normalizedCommonLeft_injective D S old L M R.current.1 y.1))
    (normalizedCommonRight_injective D S old L M R.current.1 y.1)
    C.equiv
    (restrictedBlock_cosetEquiv D S old L M y.1
      (right D S old L R.current.1 y.1 k))
    (stepMatchedComponent_interfaceEquiv D S old L M R y hprev q k hq)
    (C.left_square D S old L M R y hprev q k hq shift hbase)
    (stepMatchedComponent_right_square D S old L M R y hprev q k hq)
    (fun e => (C.source.matching e).Rel)
    (fun e => ((block S old (Step.meet S M y.1)).matching e).Rel)
    e (C.edge_iff e he)
    (restrictedBlock_cosetEquiv_edge_iff D S old L M y.1
      (right D S old L R.current.1 y.1 k) e he) x z

/-- A matched extension preserves the complete last-chart
invariant. The source is the literal chain-state extension with the
actual normalized Link maps and the chosen noncommutative shift;
its separation is derived from the retained entry-coordinate inclusion. -/
noncomputable def ComponentLastChart.extend :
    ComponentLastChart D S old L M (step D S old L R y hsep)
      (oldEmbed (block S old R.current.1) (block S old y.1)
        R.state R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1) q) := by
  let A := block S old (Step.meet S M R.current.1)
  let B := block S old (Step.meet S M y.1)
  let a := normalizedCommonLeft D S old L M R.current.1 y.1
  let b := normalizedCommonRight D S old L M R.current.1 y.1
  let ha := normalizedCommonLeft_injective D S old L M R.current.1 y.1
  let hb := normalizedCommonRight_injective D S old L M R.current.1 y.1
  have hsmall : Disjoint C.source.entry (exitSet A shift a) :=
    C.normalized_attachment_disjoint D S old L M R y q k shift hbase hsep
  have hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ t, a t = A.edge e ∧ b t = B.edge e := by
    intro e heA heB
    exact normalizedCommon_shared_edge D S old L M R.current.1 y.1 e heA heB
  refine
    { source := GluingEPPA.Steiner.ChainValuation.extend
        A B C.source shift a b ha hb hsmall hshared
      trace := NormalizedChainTrace.attach C.trace y.1 shift hsmall hshared
      base := right D S old L R.current.1 y.1 k
      equiv := C.extendEquiv D S old L M R y hprev q k hq shift hbase hsep
      last_val := ?_
      entry_mem := ?_
      edge_iff := ?_ }
  · intro t
    exact C.extendEquiv_last_val D S old L M R y hprev q k hq
      shift hbase hsep t
  · intro t ht
    change t ∈ Set.range b at ht
    obtain ⟨z, rfl⟩ := ht
    change right D S old L R.current.1 y.1 k *
        (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl
          (normalizedCommonRight D S old L M R.current.1 y.1 z) ∈
      Set.range (right D S old L R.current.1 y.1)
    refine ⟨k * normalizedCommonInterface D S old L M R.current.1 y.1 z, ?_⟩
    exact (normalized_new_boundary
      (right D S old L R.current.1 y.1)
      (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl
      (normalizedCommonInterface D S old L M R.current.1 y.1)
      (normalizedCommonRight D S old L M R.current.1 y.1)
      (normalizedCommon_right_square D S old L M R.current.1 y.1) k z).symm
  · intro e he x z
    exact (chainExtend_edge_iff_pushout
      A B C.source shift a b ha hb hsmall hshared e x z).trans
      (C.extendEquiv_edge_iff D S old L M R y hprev q k hq
        shift hbase hsep e he x z)

/-- Exactly one normalized source block is added at a matched step. -/
theorem ComponentLastChart.extend_trace_length :
    (C.extend D S old L M R y hprev q k hq shift hbase hsep).trace.length =
      C.trace.length + 1 := by
  change (C.trace.masks ++ [y.1]).length = C.trace.masks.length + 1
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add]

end Matched

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
