import GluingEPPA.Steiner.ChainValuation.ActualActiveIntervalInterfaceExistence
import GluingEPPA.Steiner.ChainValuation.ChainTests

/-!
# The active M-component interval fits the original bounded chain test

The proper-mask chain-restriction lemma must produce a test with
at MOST the number N of blocks of the original chain. The finite
active-interval theorem gives actual consecutive source-named
Cayley block OCCURRENCES; source masks may repeat, and counting
distinct masks would give the wrong length.

The original named-history builder preserves every historical
source-mask occurrence, so its block-list length equals the
length of the input atom list. A nonempty active subinterval
therefore gives a positive ChainLength N whenever the original
chain has at most N blocks.

This establishes the exact bounded length input to the existing
real RawChain/SeparatedChains API, without manufacturing a new
group or asserting the still-unproved normalized triple separation.
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

/-- The canonical original covered named+aligned finite history
has EXACTLY one source-named Cayley block per original input atom,
including every repeated source mask occurrence. -/
theorem coveredNamedBuildNonempty_block_count
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coveredNamedAlignedBuildNonempty
      D S old L M atoms hatoms hsep).named.named.length =
      atoms.length := by
  let H := coveredNamedAlignedBuildNonempty
    D S old L M atoms hatoms hsep
  have hMasks : H.named.sourceMasks =
      atoms.map (fun T => T.1) := by
    rw [coveredNamedAlignedBuildNonempty_named_eq
      D S old L M atoms hatoms hsep]
    exact namedHistoryBuildNonempty_sources
      D S old L M atoms hatoms hsep
  have hSrc : H.named.named.map (fun T => T.source) =
      atoms.map (fun T => T.1) :=
    H.named.sources.trans hMasks
  have hLen := congrArg List.length hSrc
  simpa only [List.length_map] using hLen

/-- The selected nonempty active block interval of an original
M-component cannot have more occurrences than the original chain.
This is an occurrence count, not a number of distinct masks. -/
theorem coveredNamedBuildNonempty_active_length_le
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms)
    (front active back :
      List (NamedHistoricalBlock D S old L M
        (coveredNamedAlignedBuildNonempty D S old L M
          atoms hatoms hsep).named.data.chain))
    (hdecomp :
      (coveredNamedAlignedBuildNonempty
        D S old L M atoms hatoms hsep).named.named =
        front ++ active ++ back) :
    active.length ≤ atoms.length := by
  have hAll := coveredNamedBuildNonempty_block_count
    D S old L M atoms hatoms hsep
  have hle : active.length ≤
      (coveredNamedAlignedBuildNonempty
        D S old L M atoms hatoms hsep).named.named.length := by
    rw [hdecomp]
    simp only [List.length_append]
    omega
  rw [hAll] at hle
  exact hle

/-- The actual nonempty active M-component interval determines a
positive length r≤N in the literal bounded-chain index type,
when the original chain is a valid N-block test.

No normalization shift choice or separation assumption is hidden
in this bounded length witness. -/
noncomputable def coveredNamedBuildNonempty_active_ChainLength
    (N : Nat)
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms)
    (hbound : atoms.length ≤ N)
    (front active back :
      List (NamedHistoricalBlock D S old L M
        (coveredNamedAlignedBuildNonempty D S old L M
          atoms hatoms hsep).named.data.chain))
    (hdecomp :
      (coveredNamedAlignedBuildNonempty
        D S old L M atoms hatoms hsep).named.named =
        front ++ active ++ back)
    (hne : active ≠ []) :
    ChainValuation.ChainLength N := by
  have hlength : active.length ≤ N :=
    (coveredNamedBuildNonempty_active_length_le
      D S old L M atoms hatoms hsep
      front active back hdecomp).trans hbound
  have hpos : 0 < active.length := by
    cases active with
    | nil => exact False.elim (hne rfl)
    | cons x xs => simp
  exact ⟨⟨active.length, Nat.lt_succ_of_le hlength⟩, hpos⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
