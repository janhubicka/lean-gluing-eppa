import GluingEPPA.Steiner.ChainValuation.ActiveInternalBoundaryPositions
import GluingEPPA.Steiner.ChainValuation.LinkedCoveredNamedHistory
import GluingEPPA.Steiner.ChainValuation.FiniteInterfaceSelection

/-!
# Actual parameters for all internal boundaries of a selected M-interval

All ingredients now refer to one covered source-named original
LinkChain history. An actual M-component meets a nonempty
consecutive interval of its original Cayley block *occurrences*.
The corresponding internal boundary records are obtained by
positional drop/take, without identifying repeated source masks.

The previously proved exact positional theorem identifies every
such boundary's two named endpoints with consecutive blocks of
the selected active interval. It follows that both endpoint
charts meet the same genuine M-component. By the exact
historical interface criterion, there is therefore a real
parameter in the original common earlier group K_(A_i ∩ A_(i+1))
whose actual interface point lies in that component.

We choose these parameters simultaneously, retaining one
dependent pair for each selected historical boundary occurrence,
with no top-stage K_S and no fictitious common parameter group.
This is the boundary-witness part of the proper-mask normalization
lemma. Its normalized triple-separation and final component
equivalence remain to be established separately.
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

/-- Every pair of consecutive original named Cayley blocks belongs
to its underlying block list on BOTH ends. We retain occurrences
rather than replacing the list by a set of source masks. -/
theorem namedAdjacentBlockPairs_endpoints_mem
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (NamedHistoricalBlock D S old L M R)) :
    ∀ (P Q : NamedHistoricalBlock D S old L M R),
      (P, Q) ∈ namedAdjacentBlockPairs D S old L hist →
      P ∈ hist ∧ Q ∈ hist := by
  induction hist with
  | nil =>
      intro P Q h
      simp [namedAdjacentBlockPairs] at h
  | cons a rest ih =>
      cases rest with
      | nil =>
          intro P Q h
          simp [namedAdjacentBlockPairs] at h
      | cons b tail =>
          intro P Q h
          have heither : (P, Q) = (a, b) ∨
              (P, Q) ∈ namedAdjacentBlockPairs D S old L (b :: tail) := by
            simpa only [namedAdjacentBlockPairs, List.mem_cons] using h
          rcases heither with hpair | htail
          · have hP : P = a := congrArg Prod.fst hpair
            have hQ : Q = b := congrArg Prod.snd hpair
            subst P
            subst Q
            constructor <;> simp
          · obtain ⟨hP, hQ⟩ := ih P Q htail
            exact ⟨List.mem_cons_of_mem a hP,
              List.mem_cons_of_mem a hQ⟩

/-- Every actual internal boundary of an active interval is met
by the genuine M-component on BOTH named source-block sides.
No extra hypothesis that the interface itself is met is needed:
the previously checked component/interface equivalence derives it. -/
theorem CoveredNamedAlignedHistory.internal_boundary_both_active
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M)
    (hlinked : AlignedBoundaryList.Linked D S old L H.aligned)
    (q : H.named.data.chain.state.Space)
    (front active back :
      List (NamedHistoricalBlock D S old L M H.named.data.chain))
    (hdecomp : H.named.named = front ++ active ++ back)
    (hne : active ≠ [])
    (hactive : ∀ T ∈ active,
      (T.toHistorical D S old L).Meets
        (block S old H.named.data.chain.current.1)
        H.named.data.chain.state M.val q)
    (P : AlignedNamedBoundary D S old L M H.named.data.chain)
    (hP : P ∈ (H.aligned.drop front.length).take
      (active.length - 1)) :
    P.BothSidesActive D S old L q := by
  have hpairs := H.internal_boundary_pairs
    D S old L hlinked front active back hdecomp hne
  have hp : (P.leftNamed, P.rightNamed) ∈
      namedAdjacentBlockPairs D S old L active := by
    have hmem : (P.leftNamed, P.rightNamed) ∈
        ((H.aligned.drop front.length).take
          (active.length - 1)).map
            (fun B => (B.leftNamed, B.rightNamed)) :=
      List.mem_map.mpr ⟨P, hP, rfl⟩
    rw [hpairs] at hmem
    exact hmem
  obtain ⟨hleft, hright⟩ :=
    namedAdjacentBlockPairs_endpoints_mem D S old L
      active P.leftNamed P.rightNamed hp
  exact ⟨hactive P.leftNamed hleft, hactive P.rightNamed hright⟩

/-- Simultaneously select REAL historical interface parameters
in the varying original K_(A_i ∩ A_(i+1)) group of each internal
boundary occurrence. A single ambient group is neither required
nor introduced, and all repetitions and positions are retained. -/
noncomputable def CoveredNamedAlignedHistory.chosenInternalInterfaces
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M)
    (hlinked : AlignedBoundaryList.Linked D S old L H.aligned)
    (q : H.named.data.chain.state.Space)
    (front active back :
      List (NamedHistoricalBlock D S old L M H.named.data.chain))
    (hdecomp : H.named.named = front ++ active ++ back)
    (hne : active ≠ [])
    (hactive : ∀ T ∈ active,
      (T.toHistorical D S old L).Meets
        (block S old H.named.data.chain.current.1)
        H.named.data.chain.state M.val q) :
    List (Σ P : AlignedNamedBoundary D S old L M H.named.data.chain,
      P.InterfaceChoice D S old L q) :=
  ((H.aligned.drop front.length).take (active.length - 1)).attach.map
    (fun P => ⟨P.val,
      P.val.chooseInterface D S old L q
        (H.internal_boundary_both_active D S old L
          hlinked q front active back hdecomp hne
          hactive P.val P.property)⟩)

/-- The simultaneous dependent choices neither lose nor duplicate
any internal boundary occurrence of the selected component interval. -/
theorem CoveredNamedAlignedHistory.chosenInternalInterfaces_length
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M)
    (hlinked : AlignedBoundaryList.Linked D S old L H.aligned)
    (q : H.named.data.chain.state.Space)
    (front active back :
      List (NamedHistoricalBlock D S old L M H.named.data.chain))
    (hdecomp : H.named.named = front ++ active ++ back)
    (hne : active ≠ [])
    (hactive : ∀ T ∈ active,
      (T.toHistorical D S old L).Meets
        (block S old H.named.data.chain.current.1)
        H.named.data.chain.state M.val q) :
    (H.chosenInternalInterfaces D S old L
      hlinked q front active back hdecomp hne hactive).length =
      ((H.aligned.drop front.length).take
        (active.length - 1)).length := by
  simp only [CoveredNamedAlignedHistory.chosenInternalInterfaces,
    List.length_map, List.length_attach]

/-- On the canonical genuine covered finite LinkChain history
the linkedness hypothesis is DISCHARGED by the verified finite
induction; the remaining parameters are exactly a nonempty
active interval and its support witnesses, already supplied by
the component-interval theorem. -/
noncomputable def coveredBuildNonempty_chosenInternalInterfaces
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms)
    (q : (coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep).named.data.chain.state.Space)
    (front active back :
      List (NamedHistoricalBlock D S old L M
        (coveredNamedAlignedBuildNonempty
          D S old L M atoms hatoms hsep).named.data.chain))
    (hdecomp :
      (coveredNamedAlignedBuildNonempty
        D S old L M atoms hatoms hsep).named.named =
        front ++ active ++ back)
    (hne : active ≠ [])
    (hactive : ∀ T ∈ active,
      (T.toHistorical D S old L).Meets
        (block S old (coveredNamedAlignedBuildNonempty
          D S old L M atoms hatoms hsep).named.data.chain.current.1)
        (coveredNamedAlignedBuildNonempty D S old L M
          atoms hatoms hsep).named.data.chain.state M.val q) :
    List (Σ P : AlignedNamedBoundary D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep).named.data.chain,
      P.InterfaceChoice D S old L q) :=
  let H := coveredNamedAlignedBuildNonempty D S old L M
    atoms hatoms hsep
  H.chosenInternalInterfaces D S old L
    (coveredNamedAlignedBuildNonempty_linked
      D S old L M atoms hatoms hsep)
    q front active back hdecomp hne hactive

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
