import GluingEPPA.Steiner.ChainValuation.HistoricalExactOverlap

/-!
# Canonical embedded common interfaces for actual historical Link boundaries

The original K_(A ∩ B) parameter group maps to the true quotient by
either attached Cayley chart. These two maps agree pointwise.
Combining chart injectivity with Link-parameter injectivity gives
a genuine embedded interface with no quotienting of its carrier.

This keeps the precise common interface available for the eventual
coordinate-chart pushout induction.
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

/-- The literal earlier intersection group's map to the final
quotient, through the left historical Cayley block. -/
def HistoricalLinkBoundary.interfaceMap
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R) :
    (old (common S T.leftMask T.rightMask)).Carrier → R.state.Space :=
  fun k => T.leftChart (T.leftParam k)

/-- The left and right source Cayley blocks give identical values
for every genuine interface parameter in the final quotient. -/
theorem HistoricalLinkBoundary.interfaceMap_eq_right
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (k : (old (common S T.leftMask T.rightMask)).Carrier) :
    T.interfaceMap D S old L k =
      T.rightChart (T.rightParam k) :=
  T.attached k

/-- The common interface injects into the quotient. Both factors
of the defining composite are genuine injective maps; no additional
pushout or quotient is silently inserted. -/
theorem HistoricalLinkBoundary.interfaceMap_injective
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (hCharts : T.Embeds D S old L)
    (hParams : T.ParametersInjective D S old L) :
    Function.Injective (T.interfaceMap D S old L) := by
  intro k k' h
  exact hParams.1 (hCharts.1 h)

/-- Either side of the historical boundary realizes the same exact
subset of attachment points in the final quotient. -/
theorem HistoricalLinkBoundary.interfaceRange_eq
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R) :
    Set.range (T.interfaceMap D S old L) =
      Set.range (fun k => T.rightChart (T.rightParam k)) := by
  have hfun :
      (T.interfaceMap D S old L) =
        (fun k => T.rightChart (T.rightParam k)) := by
    funext k
    exact T.attached k
  exact congrArg Set.range hfun

/-- Every boundary of the actual finite separated Link construction
has a single common-interface map which is an injection, and both
historic Cayley charts agree with it on the original parameters. -/
theorem boundaryHistoryBuildNonempty_allInterfacesEmbedded
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := boundaryHistoryBuildNonempty D S old L M atoms hne hsep
    ∀ T : HistoricalLinkBoundary D S old L M H.chain,
      T ∈ H.boundaries →
        Function.Injective (T.interfaceMap D S old L) ∧
        (∀ k : (old (common S T.leftMask T.rightMask)).Carrier,
          T.interfaceMap D S old L k =
            T.rightChart (T.rightParam k)) := by
  intro H T hT
  constructor
  · exact T.interfaceMap_injective D S old L
      (boundaryHistoryBuildNonempty_allEmbedded
        D S old L M atoms hne hsep T hT)
      (boundaryHistoryBuildNonempty_allParametersInjective
        D S old L M atoms hne hsep T hT)
  · exact T.interfaceMap_eq_right D S old L

/-- The literal set-theoretic intersection of the two embedded
historic Cayley blocks is exactly their genuine common-interface
image. Unlike an M-component intersection, this concerns equality
of points and uses no reachability assumptions. -/
theorem HistoricalLinkBoundary.exactRangeIntersection
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (hExact : T.ExactOverlap D S old L) :
    Set.range T.leftChart ∩ Set.range T.rightChart =
      Set.range (T.interfaceMap D S old L) := by
  ext q
  constructor
  · intro h
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
    obtain ⟨k, hk, _⟩ := (hExact x y).mp (hx.trans hy.symm)
    refine ⟨k, ?_⟩
    change T.leftChart (T.leftParam k) = q
    rw [hk]
    exact hx
  · rintro ⟨k, hk⟩
    have hleft : T.leftChart (T.leftParam k) = q := hk
    refine ⟨⟨T.leftParam k, hleft⟩, ⟨T.rightParam k, ?_⟩⟩
    exact (T.attached k).symm.trans hleft

/-- Every real historical boundary of the finite original chain
has its exact set intersection described by an injective earlier
intersection-group interface, rather than by a proper superset
created through subsequent gluing. -/
theorem boundaryHistoryBuildNonempty_allExactEmbeddedInterfaces
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := boundaryHistoryBuildNonempty D S old L M atoms hne hsep
    ∀ T : HistoricalLinkBoundary D S old L M H.chain,
      T ∈ H.boundaries →
        (Set.range T.leftChart ∩ Set.range T.rightChart =
          Set.range (T.interfaceMap D S old L)) ∧
        Function.Injective (T.interfaceMap D S old L) := by
  intro H T hT
  constructor
  · exact T.exactRangeIntersection D S old L
      (boundaryHistoryBuildNonempty_allExactOverlap
        D S old L M atoms hne hsep T hT)
  · exact T.interfaceMap_injective D S old L
      (boundaryHistoryBuildNonempty_allEmbedded
        D S old L M atoms hne hsep T hT)
      (boundaryHistoryBuildNonempty_allParametersInjective
        D S old L M atoms hne hsep T hT)


end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
