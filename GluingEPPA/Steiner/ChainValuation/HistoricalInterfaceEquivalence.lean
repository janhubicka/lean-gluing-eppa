import GluingEPPA.Steiner.ChainValuation.HistoricalEmbeddedInterface

/-!
# The genuine intersection group is the actual overlap of two historic blocks

The earlier intersection group K_(A∩B) does not merely map into the
overlap of two historical Cayley charts. When the original boundary is
built by the separated LinkChain and carried through subsequent injective
attachments, the true overlap in the final quotient is exactly that
image. The map is injective, so it gives an equivalence with the
subtype of points belonging to both historical blocks.

The equivalence is a useful interface chart for the eventual
normalization induction. It does not assert the full smaller-mask
M-component theorem, which still needs compatible charts for each
active interval and edge reflection.
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

/-- Every point of the *exact* historical overlap has a unique
parameter in the original K_(A∩B). This concerns equality in the
quotient, not merely connectedness by M-labelled edges. -/
theorem HistoricalLinkBoundary.mem_intersection_iff_unique_parameter
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (hExact : T.ExactOverlap D S old L)
    (hCharts : T.Embeds D S old L)
    (hParams : T.ParametersInjective D S old L)
    (q : R.state.Space) :
    q ∈ Set.range T.leftChart ∩ Set.range T.rightChart ↔
      ∃! k : (old (common S T.leftMask T.rightMask)).Carrier,
        T.interfaceMap D S old L k = q := by
  have hRange := T.exactRangeIntersection D S old L hExact
  have hInj := T.interfaceMap_injective D S old L hCharts hParams
  constructor
  · intro h
    rw [hRange] at h
    have hrange : q ∈ Set.range (T.interfaceMap D S old L) := h
    obtain ⟨k, hk⟩ := hrange
    refine ⟨k, hk, ?_⟩
    intro k' hk'
    exact hInj (hk'.trans hk.symm)
  · rintro ⟨k, hk, _⟩
    rw [hRange]
    exact ⟨k, hk⟩

/-- A concrete equivalence between the earlier genuine intersection
group and the *set-theoretic* overlap of its two original Cayley
blocks inside the final (possibly much longer) chain quotient. -/
noncomputable def HistoricalLinkBoundary.interfaceEquivIntersection
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (hExact : T.ExactOverlap D S old L)
    (hCharts : T.Embeds D S old L)
    (hParams : T.ParametersInjective D S old L) :
    (old (common S T.leftMask T.rightMask)).Carrier ≃
      {q : R.state.Space //
        q ∈ Set.range T.leftChart ∩ Set.range T.rightChart} := by
  let F :
      (old (common S T.leftMask T.rightMask)).Carrier →
        {q : R.state.Space //
          q ∈ Set.range T.leftChart ∩ Set.range T.rightChart} :=
    fun k =>
      ⟨T.interfaceMap D S old L k, by
        constructor
        · exact ⟨T.leftParam k, rfl⟩
        · exact ⟨T.rightParam k, (T.attached k).symm⟩⟩
  have hInj : Function.Injective F := by
    intro k k' h
    exact (T.interfaceMap_injective D S old L hCharts hParams)
      (congrArg Subtype.val h)
  have hSurj : Function.Surjective F := by
    intro q
    have hmem : q.val ∈ Set.range (T.interfaceMap D S old L) := by
      rw [← T.exactRangeIntersection D S old L hExact]
      exact q.property
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hk
  exact Equiv.ofBijective F ⟨hInj, hSurj⟩

/-- On the literal finite separated LinkChain, all recorded
historical boundaries admit the exact interface equivalence.
This does not require choosing a hypothetical top-stage group. -/
theorem boundaryHistoryBuildNonempty_allInterfaceEquivalences
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := boundaryHistoryBuildNonempty D S old L M atoms hne hsep
    ∀ T : HistoricalLinkBoundary D S old L M H.chain,
      T ∈ H.boundaries →
        Nonempty
          ((old (common S T.leftMask T.rightMask)).Carrier ≃
            {q : H.chain.state.Space //
              q ∈ Set.range T.leftChart ∩ Set.range T.rightChart}) := by
  intro T hT
  exact ⟨T.interfaceEquivIntersection D S old L
    (boundaryHistoryBuildNonempty_allExactOverlap
      D S old L M atoms hne hsep T hT)
    (boundaryHistoryBuildNonempty_allEmbedded
      D S old L M atoms hne hsep T hT)
    (boundaryHistoryBuildNonempty_allParametersInjective
      D S old L M atoms hne hsep T hT)⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
