import GluingEPPA.Steiner.ChainValuation.AdjacentCayleyInterfaceWitness
import GluingEPPA.Steiner.ChainValuation.OldComponentPersistence

/-!
# Persistent historical Link boundary charts

At the moment that two consecutive historical Cayley blocks are
attached, their M-cross-component relation is characterized by
a real parameter of the earlier common group K_(A∩B), and M-paths
contained within each original Cayley block.

Later separated attachments do not merge old M-components. Hence
this exact cross-boundary criterion remains valid throughout the
construction if both historical charts are transported through
the *actual* old embedding of the next injective pushout.

We package each boundary with:
* its literal two source masks A and B;
* embeddings of the two source Cayley groups into the current chain;
* the two parameter maps from the genuine K_(A∩B);
* equality of the two images of each attaching point;
* an iff characterizing actual M-paths across these charts by
  M-paths inside each source Cayley group and one parameter k.

No hypothetical full-stage group K_S is used. The next step
iterates this boundary history along the finite separated list.
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

/-- An exact interface between two genuinely historical Cayley blocks
embedded into one actual LinkChain state. The common interface carrier
is definitionally the earlier group K_(leftMask∩rightMask). -/
structure HistoricalLinkBoundary
    (M : Proper S) (R : BuildResult D S old L) where
  leftMask : Proper S
  rightMask : Proper S
  leftChart : (old leftMask).Carrier → R.state.Space
  rightChart : (old rightMask).Carrier → R.state.Space
  leftParam :
    (old (common S leftMask rightMask)).Carrier →
      (old leftMask).Carrier
  rightParam :
    (old (common S leftMask rightMask)).Carrier →
      (old rightMask).Carrier
  attached : ∀ k, leftChart (leftParam k) = rightChart (rightParam k)
  reach_iff : ∀ x y,
    LabelReach (fun e => (R.state.matching e).Rel) M.val
      (leftChart x) (rightChart y) ↔
    ∃ k : (old (common S leftMask rightMask)).Carrier,
      LabelReach
        (fun e => ((block S old leftMask).matching e).Rel)
        M.val x (leftParam k) ∧
      LabelReach
        (fun e => ((block S old rightMask).matching e).Rel)
        M.val (rightParam k) y

/-- Persist a real historical boundary through a later separated
LinkChain.step. Its source masks and original Cayley-path relations
stay unchanged. Only its embeddings into the current quotient are
composed with the genuine old injection. -/
noncomputable def HistoricalLinkBoundary.transport
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    HistoricalLinkBoundary D S old L M (step D S old L R y hsep) := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi := left_injective D S old L R.current.1 y.1
  have hj := right_injective D S old L R.current.1 y.1
  have hd := step_attachment_disjoint D S old L R y hsep
  have hs : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : (old (common S R.current.1 y.1)).Carrier,
        i k = A.edge e ∧ j k = B.edge e := by
    intro e ha hb
    exact shared_edge D S old L R.current.1 y.1 e ha hb
  have hpull := step_attachment_compatible D S old L M R y hcoset
  let emb := oldEmbed A B R.state R.current.2 i j hi hj
  exact
    { leftMask := T.leftMask
      rightMask := T.rightMask
      leftChart := fun x => emb (T.leftChart x)
      rightChart := fun y => emb (T.rightChart y)
      leftParam := T.leftParam
      rightParam := T.rightParam
      attached := by
        intro k
        exact congrArg emb (T.attached k)
      reach_iff := by
        intro x y
        exact (extended_old_reach_iff_original
          A B R.state R.current.2 i j hi hj hd hs
          M.val hpull (T.leftChart x) (T.rightChart y)).trans
          (T.reach_iff x y) }

/-- The exact new boundary between the previous last block K_A and
the new Cayley block K_B, in the literal extended quotient. The
component criterion uses genuine M-paths in K_A and K_B and the real
earlier attachment parameter group K_(A∩B). -/
noncomputable def historicalLinkBoundary_step
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    HistoricalLinkBoundary D S old L M (step D S old L R y hsep) := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi := left_injective D S old L R.current.1 y.1
  have hj := right_injective D S old L R.current.1 y.1
  let embOld := oldEmbed A B R.state R.current.2 i j hi hj
  let embNew := newEmbed A B R.state R.current.2 i j hi hj
  let f := attachInto R.state.lastEmbed R.current.2 i
  have hf := attachInto_injective
    R.state.lastEmbed R.state.lastInjective R.current.2 i hi
  exact
    { leftMask := R.current.1
      rightMask := y.1
      leftChart := fun g => embOld (R.state.lastEmbed g)
      rightChart := embNew
      leftParam := fun k => R.current.2 * i k
      rightParam := j
      attached := by
        intro k
        change pushoutInl f j hf hj (f k) =
          pushoutInr f j hf hj (j k)
        exact pushout_attachment f j hf hj k
      reach_iff := by
        intro g z
        exact step_adjacentCayley_reach_iff_interface
          D S old L M R y hsep hcoset g z }

/-- Keep all previous witnessed interfaces in order and append the
one real new boundary. -/
noncomputable def historicalBoundaries_step
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (boundaries : List (HistoricalLinkBoundary D S old L M R)) :
    List (HistoricalLinkBoundary D S old L M
      (step D S old L R y hsep)) :=
  boundaries.map (fun T =>
    T.transport D S old L y hsep hcoset) ++
  [historicalLinkBoundary_step D S old L M R y hsep hcoset]

/-- The true pair of source masks of an old historical boundary is
preserved under any subsequent LinkChain attachment. -/
theorem HistoricalLinkBoundary.transport_masks
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    ((T.transport D S old L y hsep hcoset).leftMask,
      (T.transport D S old L y hsep hcoset).rightMask) =
    (T.leftMask, T.rightMask) := rfl

/-- The fresh boundary has exactly the original consecutive
source masks, not anonymous groups with no provenance. -/
theorem historicalLinkBoundary_step_masks
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    ((historicalLinkBoundary_step D S old L M R y hsep hcoset).leftMask,
      (historicalLinkBoundary_step D S old L M R y hsep hcoset).rightMask) =
    (R.current.1, y.1) := rfl

/-- The ordered list of literal adjacent mask pairs grows by
the one expected pair at each genuine separated step. -/
theorem historicalBoundaries_step_masks
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (boundaries : List (HistoricalLinkBoundary D S old L M R)) :
    (historicalBoundaries_step D S old L M R y hsep hcoset boundaries).map
      (fun T => (T.leftMask, T.rightMask)) =
    boundaries.map (fun T => (T.leftMask, T.rightMask)) ++
      [(R.current.1, y.1)] := by
  simp [historicalBoundaries_step, HistoricalLinkBoundary.transport,
    historicalLinkBoundary_step]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
