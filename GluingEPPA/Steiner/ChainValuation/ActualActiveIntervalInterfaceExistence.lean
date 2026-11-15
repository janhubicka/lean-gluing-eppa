import GluingEPPA.Steiner.ChainValuation.ActiveInternalInterfaceChoices
import GluingEPPA.Steiner.ChainValuation.NamedHistoryActiveInterval

/-!
# Unconditional interface witnesses for every actual M-component

The previous active-interval parameter theorem required the caller to
supply a nonempty consecutive source-named historical block interval
and proofs that every block of it was met by the chosen M-component.
Those facts have ALREADY been proved for the original source-named
historical LinkChain, including coverage, consecutive support and
the preservation of repeated occurrences.

Here we transfer that exact theorem to the SAME covered named+aligned
finite history by its checked dependent record equality, and
discharge all its hypotheses. Thus, for every root q in the literal
original finite chain, there is a nonempty active block interval and
a finite ordered family of ACTUAL original K_(A∩B) parameters, one
for every selected internal boundary. No independent chart
identification, separate abstract history, or common ambient K_S
is assumed.

This is the combined support/geometry/choice result needed by the
proper-mask case of the chain-restriction lemma. The remaining
normalized separation and full smaller-M quotient equivalence
are not claimed here.
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

/-- The canonical covered named+aligned finite history has
a nonempty consecutive interval of all the actual source-named
Cayley blocks met by EVERY possible M-component root.
The proof transports the established interval property across
the literal equality of the same dependent NamedHistoryBuildResult. -/
theorem coveredNamedAlignedBuildNonempty_activeInterval
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep
    ∀ q : H.named.data.chain.state.Space,
      ∃ front active back :
          List (NamedHistoricalBlock D S old L M H.named.data.chain),
        H.named.named = front ++ active ++ back ∧
        active ≠ [] ∧
        (∀ T ∈ front,
          ¬ ((T.toHistorical D S old L).Meets
            (block S old H.named.data.chain.current.1)
            H.named.data.chain.state M.val q)) ∧
        (∀ T ∈ active,
          (T.toHistorical D S old L).Meets
            (block S old H.named.data.chain.current.1)
            H.named.data.chain.state M.val q) ∧
        (∀ T ∈ back,
          ¬ ((T.toHistorical D S old L).Meets
            (block S old H.named.data.chain.current.1)
            H.named.data.chain.state M.val q)) := by
  intro H
  have hNamed : H.named =
      namedHistoryBuildNonempty D S old L M atoms hatoms hsep :=
    coveredNamedAlignedBuildNonempty_named_eq
      D S old L M atoms hatoms hsep
  rw [hNamed]
  exact namedHistoryBuildNonempty_active_interval
    D S old L M atoms hatoms hsep

/-- For EACH actual M-component of the original finite separated
Link chain, there exists a nonempty active historical interval,
with the precise inactive prefix and suffix, together with one
real K_(A_i∩A_(i+1)) attaching parameter at EVERY internal
historical boundary of that interval.

The chosen parameter list has exactly the length of the selected
internal boundary list, retaining all repeated historical positions.
The existence of boundary points is DERIVED from two-sided
component reachability, never postulated. -/
theorem coveredBuildNonempty_has_active_interval_and_interfaces
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep
    ∀ q : H.named.data.chain.state.Space,
      ∃ front active back :
        List (NamedHistoricalBlock D S old L M H.named.data.chain),
      H.named.named = front ++ active ++ back ∧
      active ≠ [] ∧
      (∀ T ∈ front,
        ¬ ((T.toHistorical D S old L).Meets
          (block S old H.named.data.chain.current.1)
          H.named.data.chain.state M.val q)) ∧
      (∀ T ∈ active,
        (T.toHistorical D S old L).Meets
          (block S old H.named.data.chain.current.1)
          H.named.data.chain.state M.val q) ∧
      (∀ T ∈ back,
        ¬ ((T.toHistorical D S old L).Meets
          (block S old H.named.data.chain.current.1)
          H.named.data.chain.state M.val q)) ∧
      ∃ choices : List
          (Σ P : AlignedNamedBoundary D S old L M
            H.named.data.chain, P.InterfaceChoice D S old L q),
        choices.length =
          ((H.aligned.drop front.length).take
            (active.length - 1)).length := by
  intro H q
  obtain ⟨front, active, back, hdecomp, hne,
      hfront, hactive, hback⟩ :=
    coveredNamedAlignedBuildNonempty_activeInterval
      D S old L M atoms hatoms hsep q
  let hlinked : AlignedBoundaryList.Linked D S old L H.aligned :=
    coveredNamedAlignedBuildNonempty_linked
      D S old L M atoms hatoms hsep
  let choices := H.chosenInternalInterfaces D S old L
    hlinked q front active back hdecomp hne hactive
  refine ⟨front, active, back, hdecomp, hne,
    hfront, hactive, hback, choices, ?_⟩
  exact H.chosenInternalInterfaces_length
    D S old L hlinked q front active back hdecomp hne hactive

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
