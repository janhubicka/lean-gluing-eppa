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

/-- The interface equivalence commutes *definitionally* with the
historical left Cayley embedding. This is one required normalization
boundary square, with no arbitrary choice of gluing point. -/
theorem HistoricalLinkBoundary.interfaceEquivIntersection_left
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (hExact : T.ExactOverlap D S old L)
    (hCharts : T.Embeds D S old L)
    (hParams : T.ParametersInjective D S old L)
    (k : (old (common S T.leftMask T.rightMask)).Carrier) :
    (T.interfaceEquivIntersection D S old L
      hExact hCharts hParams k).val =
        T.leftChart (T.leftParam k) := rfl

/-- The same exact interface chart also commutes with the right
Cayley embedding, using the genuine Link attachment equation. -/
theorem HistoricalLinkBoundary.interfaceEquivIntersection_right
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (hExact : T.ExactOverlap D S old L)
    (hCharts : T.Embeds D S old L)
    (hParams : T.ParametersInjective D S old L)
    (k : (old (common S T.leftMask T.rightMask)).Carrier) :
    (T.interfaceEquivIntersection D S old L
      hExact hCharts hParams k).val =
        T.rightChart (T.rightParam k) := by
  exact (T.interfaceEquivIntersection_left D S old L
    hExact hCharts hParams k).trans (T.attached k)

/-- On the literal finite separated LinkChain, all recorded
historical boundaries have the exact interface equivalence.
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

/-- If an actual M-component meets both historical sides of a
genuine boundary, it also meets their *literal* common-interface
image. This strengthens the existing two-sided path witness from
the source groups to a point in the final quotient lying on the
original K_(A∩B) interface. -/
theorem HistoricalLinkBoundary.component_meets_interface
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (q : R.state.Space)
    (hLeft : ∃ x : (old T.leftMask).Carrier,
      GluingEPPA.Steiner.ChainValuation.LabelReach
        (fun e => (R.state.matching e).Rel) M.val
        q (T.leftChart x))
    (hRight : ∃ y : (old T.rightMask).Carrier,
      GluingEPPA.Steiner.ChainValuation.LabelReach
        (fun e => (R.state.matching e).Rel) M.val
        q (T.rightChart y)) :
    ∃ k : (old (common S T.leftMask T.rightMask)).Carrier,
      GluingEPPA.Steiner.ChainValuation.LabelReach
        (fun e => (R.state.matching e).Rel) M.val
        q (T.interfaceMap D S old L k) := by
  obtain ⟨x, hx⟩ := hLeft
  obtain ⟨y, hy⟩ := hRight
  have hxy :
      GluingEPPA.Steiner.ChainValuation.LabelReach
        (fun e => (R.state.matching e).Rel) M.val
        (T.leftChart x) (T.rightChart y) :=
    GluingEPPA.Steiner.ChainValuation.LabelReach.trans
      (GluingEPPA.Steiner.ChainValuation.LabelReach.symm hx) hy
  obtain ⟨k, hOld, _⟩ := (T.reach_iff x y).mp hxy
  have hCross :
      GluingEPPA.Steiner.ChainValuation.LabelReach
        (fun e => (R.state.matching e).Rel) M.val
        (T.leftChart x) (T.rightChart (T.rightParam k)) :=
    (T.reach_iff x (T.rightParam k)).mpr
      ⟨k, hOld,
        GluingEPPA.Steiner.ChainValuation.LabelReach.refl _⟩
  refine ⟨k, ?_⟩
  rw [T.interfaceMap_eq_right D S old L k]
  exact GluingEPPA.Steiner.ChainValuation.LabelReach.trans hx hCross

/-- The exact-interface meeting property applies at every
recorded consecutive boundary of the finite true LinkChain. -/
theorem boundaryHistoryBuildNonempty_every_active_boundary_met
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := boundaryHistoryBuildNonempty D S old L M atoms hne hsep
    ∀ T : HistoricalLinkBoundary D S old L M H.chain,
      T ∈ H.boundaries →
        ∀ q : H.chain.state.Space,
          (∃ x : (old T.leftMask).Carrier,
            GluingEPPA.Steiner.ChainValuation.LabelReach
              (fun e => (H.chain.state.matching e).Rel) M.val
              q (T.leftChart x)) →
          (∃ y : (old T.rightMask).Carrier,
            GluingEPPA.Steiner.ChainValuation.LabelReach
              (fun e => (H.chain.state.matching e).Rel) M.val
              q (T.rightChart y)) →
          ∃ k : (old (common S T.leftMask T.rightMask)).Carrier,
            GluingEPPA.Steiner.ChainValuation.LabelReach
              (fun e => (H.chain.state.matching e).Rel) M.val
              q (T.interfaceMap D S old L k) := by
  intro T _ q hLeft hRight
  exact T.component_meets_interface D S old L q hLeft hRight

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
