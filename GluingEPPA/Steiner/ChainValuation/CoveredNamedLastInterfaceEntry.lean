import GluingEPPA.Steiner.ChainValuation.CoveredNamedAlignedHistory
import GluingEPPA.Steiner.ChainValuation.HistoricalEmbeddedInterface

/-!
# The last true historical interface is the old last-block entry

At every genuine separated LinkChain state, the `entry` set
records the incoming interface in its final Cayley block.
To promote the original local separation to a finite-chain
statement, we need to know that the LAST recorded historical
boundary actually maps into this same entry set.

This is established in the SAME covered named+aligned history
used for component coverage and active interval selection.
A singleton chain has no recorded boundary. On every genuine
LinkChain.step the fresh boundary has right parameter map equal
to the original Link inclusion and the new last-block entry is
exactly its range. All older boundaries become irrelevant to
the last-entry certificate.

The finite induction proves the last-interface statement for
every original nonempty separated LinkChain, without replacing
its quotient or identifying repeated source masks.
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

/-- Either the original covered chain has no historical interface,
or its last interface has a genuine old last-Cayley coordinate in
the recorded `ChainState.entry` set, for every original
intersection-group parameter. -/
def CoveredNamedAlignedHistory.LastInterfaceIsEntry
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M) : Prop :=
  H.aligned = [] ∨
    ∃ (pre : List (AlignedNamedBoundary D S old L M H.named.data.chain))
      (P : AlignedNamedBoundary D S old L M H.named.data.chain),
      H.aligned = pre ++ [P] ∧
        ∀ k : (old (common S P.boundary.leftMask
          P.boundary.rightMask)).Carrier,
          ∃ x : (old H.named.data.chain.current.1).Carrier,
            x ∈ H.named.data.chain.state.entry ∧
            P.boundary.interfaceMap D S old L k =
              H.named.data.chain.state.lastEmbed x

/-- The original singleton chain has no boundary and hence
satisfies the last-interface entry certificate. -/
theorem coveredNamedAlignedInitial_lastInterfaceIsEntry
    (M : Proper S) (x : Atom S old) :
    (coveredNamedAlignedInitial D S old L M x).LastInterfaceIsEntry
      D S old L :=
  Or.inl rfl

/-- The newly attached historical interface of an actual separated
LinkChain.step is literally the new last-block entry.
The right-hand historical Cayley parameter and the state entry are
BOTH the original `right D S old L` inclusion, not two unrelated
subgroup embeddings. -/
theorem coveredNamedAlignedStep_lastInterfaceIsEntry
    (M : Proper S)
    (H : CoveredNamedAlignedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.named.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
          H.named.data.chain.current y) :
    (coveredNamedAlignedStep D S old L M H y hsep).LastInterfaceIsEntry
      D S old L := by
  let R := H.named.data.chain
  let hcoset := H.named.data.lastInv
  let fresh := alignedNamedBoundaryFresh D S old L M
    R y hsep hcoset
  let earlier := H.aligned.map (fun P =>
    P.transport D S old L y hsep hcoset)
  right
  refine ⟨earlier, fresh, rfl, ?_⟩
  intro k
  let j := right D S old L R.current.1 y.1
  have hk : j k ∈ (step D S old L R y hsep).state.entry := by
    change j k ∈ Set.range j
    exact ⟨k, rfl⟩
  refine ⟨j k, hk, ?_⟩
  change
    (historicalLinkBoundary_step D S old L M R y hsep
      hcoset).interfaceMap D S old L k =
    (historicalLinkBoundary_step D S old L M R y hsep
      hcoset).rightChart
        ((historicalLinkBoundary_step D S old L M R y hsep
          hcoset).rightParam k)
  exact (historicalLinkBoundary_step D S old L M R y hsep
    hcoset).interfaceMap_eq_right D S old L k

/-- The actual named+aligned finite history carries its last
interface entry certificate through the SAME original
separated-list recursion, without extra geometric hypotheses. -/
theorem coveredNamedAlignedBuildTail_lastInterfaceIsEntry
    (M : Proper S) (p c : Atom S old)
    (H : CoveredNamedAlignedHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    H.LastInterfaceIsEntry D S old L →
    (coveredNamedAlignedBuildTail D S old L M
      p c H hp hc rest hsep).LastInterfaceIsEntry D S old L := by
  induction rest generalizing p c H with
  | nil =>
      intro hOld
      exact hOld
  | cons z zs ih =>
      intro _
      have hstep :
          (match H.named.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coveredNamedAlignedStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2
        (coveredNamedAlignedStep_lastInterfaceIsEntry
          D S old L M H z hstep)

/-- The exact original source-named finite LinkChain has its LAST
recorded boundary equal to the entry of the current last block;
there is no unverified handoff between distinct historical
realizations or between anonymous subgroup copies. -/
theorem coveredNamedAlignedBuildNonempty_lastInterfaceIsEntry
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep).LastInterfaceIsEntry D S old L := by
  cases atoms with
  | nil =>
      exact False.elim (hatoms rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact coveredNamedAlignedInitial_lastInterfaceIsEntry
            D S old L M x
      | cons y ys =>
          let H0 := coveredNamedAlignedInitial D S old L M x
          let H1 := coveredNamedAlignedStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          exact coveredNamedAlignedBuildTail_lastInterfaceIsEntry
            D S old L M x y H1 hp hc ys hsep
            (coveredNamedAlignedStep_lastInterfaceIsEntry
              D S old L M H0 y trivial)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
