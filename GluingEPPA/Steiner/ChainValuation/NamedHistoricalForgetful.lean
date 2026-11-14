import GluingEPPA.Steiner.ChainValuation.NamedHistoricalLinkBlocks

/-!
# Forgetting source masks from genuine historical Cayley charts

A named historical block records the actual original alphabet A and the
genuine older group K_A, as well as its embedded restricted-coset chart.
For the finite component-normalization induction we must know that
forgetting these source names recovers the *same* historical charts
used in the checked consecutive-support construction, rather than an
independent list of abstract isomorphic groups.

The proofs below concern one actual LinkChain attachment. They do
not assert the complete finite-history chart or the normalized
proper-M component theorem.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- Forgetting the name of the initial last block produces the
original, literal first historical chart, with identical group and
embedding. -/
theorem namedHistoricalLast_forget
    (M : Proper S) (R : BuildResult D S old L)
    (hcoset : LastMaskCoset D S old L M R) :
    (namedHistoricalLast D S old L M R hcoset).toHistorical D S old L =
      historicalBlock_last
        (block S old R.current.1) R.state M.val
        (restrictedSubgroup D S old L M R.current.1) hcoset := rfl

/-- Transporting a genuine named block and forgetting its name gives
the identical generic historical coset chart transported through
the actual old embedding of the new LinkChain pushout. -/
theorem namedHistoricalTransport_forget
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (T : NamedHistoricalBlock D S old L M R) :
    NamedHistoricalBlock.toHistorical D S old L
      (namedHistoricalTransport D S old L M R y hsep hcoset T) =
      (T.toHistorical D S old L).transport
        (block S old R.current.1) (block S old y.1) R.state
        R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1)
        (step_attachment_disjoint D S old L R y hsep)
        (fun e heA heB =>
          shared_edge D S old L R.current.1 y.1 e heA heB)
        M.val (step_attachment_compatible D S old L M R y hcoset) := by
  rfl

/-- The named list of historical blocks forgets to exactly the same
heterogeneous chart list which the established history-extension
constructor transports. There is no extra quotient, reindexing,
or choice of a universal top-stage group. -/
theorem namedHistoricalStepList_forget
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (hist : List (NamedHistoricalBlock D S old L M R)) :
    (namedHistoricalStepList D S old L M R y hsep hcoset hist).map
      (fun T => T.toHistorical D S old L) =
      historicalBlocks_extend
        (block S old R.current.1) (block S old y.1) R.state
        R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1)
        (step_attachment_disjoint D S old L R y hsep)
        (fun e heA heB =>
          shared_edge D S old L R.current.1 y.1 e heA heB)
        M.val (step_attachment_compatible D S old L M R y hcoset)
        (restrictedSubgroup D S old L M y.1)
        (step_lastMaskCoset D S old L M R y hsep hcoset)
        (hist.map (fun T => T.toHistorical D S old L)) := by
  simp only [namedHistoricalStepList, historicalBlocks_extend,
    List.map_append, List.map_map, List.map_singleton]
  rfl

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
