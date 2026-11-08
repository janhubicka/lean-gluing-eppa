import GluingEPPA.Steiner.ChainValuation.PersistentHistoricalBoundaries
import GluingEPPA.Steiner.ChainValuation.LinkChain

/-!
# A complete history of real witnessed Link boundaries

The previous construction records one exact M-interface criterion
for every new attachment and transports all older criteria through
subsequent chain steps. Here we iterate it over a *finite separated
list of actual earlier Link atoms*, retaining:
* the literal BuildResult state of the manuscript construction;
* the already proved last-block M-coset invariant;
* an ordered list of historical boundaries, each equipped with its
  genuine source masks, attachment group, and two-way reachability law.

The final theorem extracts a real k∈K_(A∩B) whenever a component
meets both charts of any recorded historical boundary, however far
back in the chain that boundary was created.

The remaining normalization step is to select exactly the boundaries
between the consecutive active historical blocks and compose their
charts, not to manufacture the missing interface witnesses.
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

/-- A real partially built separated Link chain with all its
witnessed historical boundaries. -/
structure BoundaryHistoryBuildResult (M : Proper S) where
  chain : BuildResult D S old L
  lastInv : LastMaskCoset D S old L M chain
  boundaries : List (HistoricalLinkBoundary D S old L M chain)

/-- The original one-block chain has no attachment boundary.
It already satisfies the genuine M-coset invariant. -/
noncomputable def boundaryHistoryInitial
    (M : Proper S) (x : Atom S old) :
    BoundaryHistoryBuildResult D S old L M where
  chain := initial D S old L x
  lastInv := initial_lastMaskCoset D S old L M x
  boundaries := []

/-- Every actual separated step transports all earlier witnessed
interfaces and adds exactly the real new attachment boundary. -/
noncomputable def boundaryHistoryStep
    (M : Proper S) (H : BoundaryHistoryBuildResult D S old L M)
    (y : Atom S old)
    (hsep :
      match H.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.chain.current y) :
    BoundaryHistoryBuildResult D S old L M where
  chain := step D S old L H.chain y hsep
  lastInv := step_lastMaskCoset D S old L M H.chain y hsep H.lastInv
  boundaries := historicalBoundaries_step D S old L M H.chain y hsep
    H.lastInv H.boundaries

/-- Recursively attach all remaining atoms of the original
separated list. The previous/current witnesses certify that each
step uses *the same triple-separated adjacency* as the manuscript. -/
noncomputable def boundaryHistoryBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : BoundaryHistoryBuildResult D S old L M)
    (hprev : H.chain.previous = some p)
    (hcurr : H.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    BoundaryHistoryBuildResult D S old L M :=
  match rest with
  | [] => H
  | z :: zs =>
      let hstep :
          (match H.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous H.chain.current z) := by
        rw [hprev, hcurr]
        exact hsep.1
      let HN := boundaryHistoryStep D S old L M H z hstep
      have hnprev : HN.chain.previous = some c := by
        change some H.chain.current = some c
        rw [hcurr]
      have hncurr : HN.chain.current = z := rfl
      boundaryHistoryBuildTail M c z HN hnprev hncurr zs hsep.2

/-- The entire finite nonempty separated Link chain, equipped with
a complete list of all witnessed true historical interfaces.
The first two blocks and the longer tail are handled by precisely
the original left-to-right LinkChain step construction. -/
noncomputable def boundaryHistoryBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    BoundaryHistoryBuildResult D S old L M := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact boundaryHistoryInitial D S old L M x
      | cons y ys =>
          let H0 := boundaryHistoryInitial D S old L M x
          let H1 := boundaryHistoryStep D S old L M H0 y trivial
          have hp : H1.chain.previous = some x := rfl
          have hc : H1.chain.current = y := rfl
          exact boundaryHistoryBuildTail D S old L M x y H1 hp hc ys hsep

/-- The source pair of masks of every recorded boundary is the
genuine pair of earlier stages; the parameter carrier used below
is definitionally K_(A∩B), as stored in that boundary. -/
theorem boundaryHistory_connected_boundary_has_real_parameter
    (M : Proper S) (H : BoundaryHistoryBuildResult D S old L M)
    (T : HistoricalLinkBoundary D S old L M H.chain)
    (q : H.chain.state.Space)
    (hLeft : ∃ x : (old T.leftMask).Carrier,
      LabelReach (fun e => (H.chain.state.matching e).Rel) M.val
        q (T.leftChart x))
    (hRight : ∃ y : (old T.rightMask).Carrier,
      LabelReach (fun e => (H.chain.state.matching e).Rel) M.val
        q (T.rightChart y)) :
    ∃ k : (old (common S T.leftMask T.rightMask)).Carrier,
      ∃ x : (old T.leftMask).Carrier,
      ∃ y : (old T.rightMask).Carrier,
        LabelReach
          (fun e => ((block S old T.leftMask).matching e).Rel)
          M.val x (T.leftParam k) ∧
        LabelReach
          (fun e => ((block S old T.rightMask).matching e).Rel)
          M.val (T.rightParam k) y := by
  obtain ⟨x, hx⟩ := hLeft
  obtain ⟨y, hy⟩ := hRight
  have hxy :
      LabelReach (fun e => (H.chain.state.matching e).Rel) M.val
        (T.leftChart x) (T.rightChart y) :=
    LabelReach.trans (LabelReach.symm hx) hy
  obtain ⟨k, hA, hB⟩ := (T.reach_iff x y).mp hxy
  exact ⟨k, x, y, hA, hB⟩

/-- The preceding theorem is available for *every* one of the
recorded interfaces of any finite separated chain. It does not
assume a component starts in the first block or remains in the
last one. -/
theorem boundaryHistoryBuildNonempty_all_interfaces_witnessed
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := boundaryHistoryBuildNonempty
      D S old L M atoms hne hsep
    ∀ (T : HistoricalLinkBoundary D S old L M H.chain),
      T ∈ H.boundaries →
      ∀ (q : H.chain.state.Space),
      (∃ x : (old T.leftMask).Carrier,
        LabelReach (fun e => (H.chain.state.matching e).Rel) M.val
          q (T.leftChart x)) →
      (∃ y : (old T.rightMask).Carrier,
        LabelReach (fun e => (H.chain.state.matching e).Rel) M.val
          q (T.rightChart y)) →
      ∃ k : (old (common S T.leftMask T.rightMask)).Carrier,
        ∃ x : (old T.leftMask).Carrier,
        ∃ y : (old T.rightMask).Carrier,
          LabelReach
            (fun e => ((block S old T.leftMask).matching e).Rel)
            M.val x (T.leftParam k) ∧
          LabelReach
            (fun e => ((block S old T.rightMask).matching e).Rel)
            M.val (T.rightParam k) y := by
  intro T _ q hLeft hRight
  exact boundaryHistory_connected_boundary_has_real_parameter
    D S old L M _ T q hLeft hRight

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
