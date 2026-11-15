import GluingEPPA.Steiner.ChainValuation.LinkedAlignedBoundaryFinite
import GluingEPPA.Steiner.ChainValuation.PointwiseNamedHistoryFinite

/-!
# One original finite history with both exact middle and pointwise charts

Two distinct refinements of the literal original LinkChain have
been formalized:
* every consecutive historical boundary shares the SAME named
  middle Cayley block chart, and
* every historical boundary point is mapped POINTWISE by the
  original named Cayley chart in its exact group coordinates.

Those properties cannot simply be assumed for two independent
surrogate histories. Each refinement has a checked forgetful
equality with the SAME original alignedNamedBuildNonempty dependent
record. We combine them on that one canonical record.

The resulting finite-history theorem supplies simultaneously
all actual point coordinates required by the normalized
entry/exit shifts and the exact middle-block identification
required to compare consecutive interface parameters. No
fictitious larger K_S, hidden chart isomorphism or additional
alignment axiom is used.
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

/-- The same canonical finite original historical record has BOTH
literal adjacency of every middle named Cayley block and pointwise
coordinate agreement at every true historical boundary. -/
theorem alignedNamedBuildNonempty_pointwise_and_linked
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := alignedNamedBuildNonempty D S old L M atoms hne hsep
    AlignedBoundaryList.Linked D S old L H.aligned ∧
      H.AllPointwise D S old L := by
  intro H
  constructor
  · let T := linkedAlignedBuildNonempty
      D S old L M atoms hne hsep
    have hlink : AlignedBoundaryList.Linked D S old L T.data.aligned :=
      T.linked
    have hsame : T.data = H :=
      linkedAlignedBuildNonempty_data_eq
        D S old L M atoms hne hsep
    rw [hsame] at hlink
    exact hlink
  · let T := pointwiseAlignedBuildNonempty
      D S old L M atoms hne hsep
    have hp : T.data.AllPointwise D S old L := T.pointwise
    have hsame : T.data = H :=
      pointwiseAlignedBuildNonempty_data_eq
        D S old L M atoms hne hsep
    rw [hsame] at hp
    exact hp

/-- The combined pointwise and linked historical charts hold on
the LITERAL original finite separated LinkChain.buildNonempty
point carrier and completed matching families, not an abstract
equivalent quotient. -/
theorem buildNonempty_has_joint_exact_historical_charts
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    ∃ H : AlignedNamedHistory D S old L M,
      (⟨H.boundaryHistory.chain.current,
         H.boundaryHistory.chain.state⟩ : SomeState S old) =
        buildNonempty D S old L atoms hne hsep ∧
      AlignedBoundaryList.Linked D S old L H.aligned ∧
      H.AllPointwise D S old L := by
  let H := alignedNamedBuildNonempty D S old L M atoms hne hsep
  obtain ⟨hlink, hpoint⟩ :=
    alignedNamedBuildNonempty_pointwise_and_linked
      D S old L M atoms hne hsep
  exact ⟨H, alignedNamedBuildNonempty_original
    D S old L M atoms hne hsep, hlink, hpoint⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
