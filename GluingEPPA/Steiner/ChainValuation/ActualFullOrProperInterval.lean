import GluingEPPA.Steiner.ChainValuation.ActualActiveIntervalInterfaceExistence
import GluingEPPA.Steiner.ChainValuation.FiniteHistoricalComponentDichotomy

/-!
# Exact full-K_M / proper-mask interval dichotomy in one finite chain

The previously checked full-mask alternative gives a *whole* genuine
M-component Cayley coset whenever the component meets an original
historical K_A block with M subset A. The independently checked
active-interval theorem supplies all touched original block
occurrences and their true internal K_(A_i∩A_(i+1)) parameters.

These must refer to the SAME canonical original covered
source-named history. We combine the two now, without an assumed
proper-mask condition or a replacement quotient.

Either one historical full-K_M coset is precisely the component,
or every source mask A_i appearing in its actual active interval
has M∩A_i strictly smaller than M, so it is a legal earlier-stage
block for the normalized chain. In the second case all internal
real attaching parameters are already selected simultaneously.

This completes the geometric CASE SPLIT and the properness
requirement of the chain-restriction lemma. It does not yet
construct the normalized proper-M separated chain or its
edge-reflecting component equivalence.
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

/-- The exact full-coset versus strictly-proper-mask alternative
on the canonical covered named+aligned original chain. The
covered-history forgetful equality is genuine dependent equality,
so it preserves the original point carrier and completed matchings. -/
theorem coveredBuildNonempty_full_or_proper
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep
    ∀ q : H.named.data.chain.state.Space,
      (∃ T : NamedHistoricalBlock D S old L M H.named.data.chain,
        T ∈ H.named.named ∧ M.val ⊆ T.source.val ∧
        T.Meets D S old L q ∧
        ∃ base : (old T.source).Carrier,
          ∀ v : H.named.data.chain.state.Space,
            LabelReach (fun e => (H.named.data.chain.state.matching e).Rel)
              M.val q v ↔
              v ∈ T.restrictedCosetImage D S old L base) ∨
      (∀ T : NamedHistoricalBlock D S old L M H.named.data.chain,
        T ∈ H.named.named → T.Meets D S old L q →
        ¬ M.val ⊆ T.source.val) := by
  intro H
  have hNamed : H.named =
      namedHistoryBuildNonempty D S old L M atoms hatoms hsep :=
    coveredNamedAlignedBuildNonempty_named_eq
      D S old L M atoms hatoms hsep
  rw [hNamed]
  intro q
  rcases namedHistoryBuildNonempty_full_or_proper
    D S old L M atoms hatoms hsep q with hfull | hproper
  · exact Or.inl hfull
  · right
    intro T hT hmeets hsubset
    exact hproper T hT hmeets
      (Finset.inter_eq_left.mpr hsubset)

/-- Geometric restriction dichotomy with the proper-mask active
interval and ALL genuine interface parameters, completely
discharging the assumptions about which source masks are proper
in M and whether the selected component touches its boundaries.

The full alternative identifies the entire original component
with one embedded K_M coset. The second alternative selects a
nonempty consecutive interval of true historical block occurrences;
EVERY source mask on it is proper relative to M, and it gives one
real attaching parameter for every internal original boundary. -/
theorem coveredBuildNonempty_full_or_proper_interval_with_interfaces
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep
    ∀ q : H.named.data.chain.state.Space,
      (∃ T : NamedHistoricalBlock D S old L M H.named.data.chain,
        T ∈ H.named.named ∧ M.val ⊆ T.source.val ∧
        T.Meets D S old L q ∧
        ∃ base : (old T.source).Carrier,
          ∀ v : H.named.data.chain.state.Space,
            LabelReach (fun e => (H.named.data.chain.state.matching e).Rel)
              M.val q v ↔
              v ∈ T.restrictedCosetImage D S old L base) ∨
      (∃ front active back :
          List (NamedHistoricalBlock D S old L M H.named.data.chain),
        H.named.named = front ++ active ++ back ∧
        active ≠ [] ∧
        (∀ T ∈ active, ¬ M.val ⊆ T.source.val) ∧
        (∀ T ∈ active,
          (T.toHistorical D S old L).Meets
            (block S old H.named.data.chain.current.1)
            H.named.data.chain.state M.val q) ∧
        ∃ choices : List
            (Σ P : AlignedNamedBoundary D S old L M
              H.named.data.chain, P.InterfaceChoice D S old L q),
          choices.length =
            ((H.aligned.drop front.length).take
              (active.length - 1)).length) := by
  intro H q
  rcases coveredBuildNonempty_full_or_proper
    D S old L M atoms hatoms hsep q with hfull | hproper
  · exact Or.inl hfull
  · right
    obtain ⟨front, active, back, hdecomp, hne,
        _hfront, hactive, _hback, choices, hlength⟩ :=
      coveredBuildNonempty_has_active_interval_and_interfaces
        D S old L M atoms hatoms hsep q
    have hmask : ∀ T ∈ active, ¬ M.val ⊆ T.source.val := by
      intro T hT
      have hTnamed : T ∈ H.named.named := by
        rw [hdecomp]
        exact List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inr hT)))
      exact hproper T hTnamed (hactive T hT)
    exact ⟨front, active, back, hdecomp, hne,
      hmask, hactive, choices, hlength⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
