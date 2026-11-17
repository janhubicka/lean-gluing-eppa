import GluingEPPA.Steiner.ChainValuation.ExactActiveInteriorCoordinates
import GluingEPPA.Steiner.ChainValuation.FiniteHistoricalInterfaceSeparation
import GluingEPPA.Steiner.ChainValuation.HistoricalInterfaceMultiplication

/-!
# Separation of the actual normalized active interfaces

For two consecutive active historical boundaries, their chosen interface
points determine a unique smaller-group displacement.  The multiplication
laws of the original parameter maps identify the whole incoming and
outgoing normalized cosets with points of the two genuine interfaces.
Those interfaces are disjoint in the original finite quotient.  Hence
the normalized cosets are disjoint, with no additional separation premise.

All coordinate transports below are casts along equal source indices.
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

/-- Equality of original source indices transports their group structure. -/
def sourceMaskCastHom {A B : Proper S} (h : A = B) :
    (old A).Carrier →* (old B).Carrier where
  toFun := sourceMaskCast S old h
  map_one' := by cases h; rfl
  map_mul' := by cases h; intros; rfl

theorem sourceMaskCastHom_comp {A B C : Proper S}
    (hAB : A = B) (hBC : B = C) :
    (sourceMaskCastHom S old hBC).comp (sourceMaskCastHom S old hAB) =
      sourceMaskCastHom S old (hAB.trans hBC) := by
  cases hAB
  cases hBC
  rfl

theorem normalizedCommonLeft_range_cast (M A B A' B' : Proper S)
    (hA : A = A') (hB : B = B') :
    ((sourceMaskCastHom S old (congrArg (Step.meet S M) hA)).comp
      (normalizedCommonLeft D S old L M A B)).range =
      (normalizedCommonLeft D S old L M A' B').range := by
  cases hA
  cases hB
  rfl

theorem normalizedCommonRight_range_cast (M A B A' B' : Proper S)
    (hA : A = A') (hB : B = B') :
    ((sourceMaskCastHom S old (congrArg (Step.meet S M) hB)).comp
      (normalizedCommonRight D S old L M A B)).range =
      (normalizedCommonRight D S old L M A' B').range := by
  cases hA
  cases hB
  rfl

@[simp] theorem sourceMaskCast_mul {A B : Proper S} (h : A = B)
    (x y : (old A).Carrier) :
    sourceMaskCast S old h (x * y) =
      sourceMaskCast S old h x * sourceMaskCast S old h y := by
  cases h
  rfl

/-- The restricted inclusion commutes with an equality of source indices. -/
theorem sourceMaskCast_restricted_incl (M : Proper S)
    {A B : Proper S} (h : A = B)
    (x : (old (Step.meet S M A)).Carrier) :
    sourceMaskCast S old h
        ((L (Step.meet S M A) A Finset.inter_subset_right).incl x) =
      (L (Step.meet S M B) B Finset.inter_subset_right).incl
        (sourceMaskCast S old (congrArg (Step.meet S M) h) x) := by
  cases h
  rfl

/-- The actual normalized left interface expressed in its named block. -/
noncomputable def AlignedNamedBoundary.namedNormalizedLeft
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R) :
    (old (Step.meet S M (common S P.boundary.leftMask P.boundary.rightMask))).Carrier →*
      (old (Step.meet S M P.leftNamed.source)).Carrier :=
  (sourceMaskCastHom S old (congrArg (Step.meet S M) P.agree.1)).comp
    (normalizedCommonLeft D S old L M P.boundary.leftMask P.boundary.rightMask)

/-- The actual normalized right interface expressed in its named block. -/
noncomputable def AlignedNamedBoundary.namedNormalizedRight
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R) :
    (old (Step.meet S M (common S P.boundary.leftMask P.boundary.rightMask))).Carrier →*
      (old (Step.meet S M P.rightNamed.source)).Carrier :=
  (sourceMaskCastHom S old (congrArg (Step.meet S M) P.agree.2.1)).comp
    (normalizedCommonRight D S old L M P.boundary.leftMask P.boundary.rightMask)

theorem AlignedNamedBoundary.leftNamedCoordinate_mul
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (hP : P.boundary.ParameterMultiplicative D S old L)
    (k : (old (common S P.boundary.leftMask P.boundary.rightMask)).Carrier)
    (t : (old (Step.meet S M
      (common S P.boundary.leftMask P.boundary.rightMask))).Carrier) :
    P.leftNamedCoordinate D S old L
        (k * normalizedCommonInterface D S old L M
          P.boundary.leftMask P.boundary.rightMask t) =
      P.leftNamedCoordinate D S old L k *
        (L (Step.meet S M P.leftNamed.source) P.leftNamed.source
          Finset.inter_subset_right).incl (P.namedNormalizedLeft D S old L t) := by
  unfold AlignedNamedBoundary.leftNamedCoordinate
  rw [hP.1 k t, sourceMaskCast_mul, sourceMaskCast_restricted_incl]
  rfl

theorem AlignedNamedBoundary.rightNamedCoordinate_mul
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (hP : P.boundary.ParameterMultiplicative D S old L)
    (k : (old (common S P.boundary.leftMask P.boundary.rightMask)).Carrier)
    (t : (old (Step.meet S M
      (common S P.boundary.leftMask P.boundary.rightMask))).Carrier) :
    P.rightNamedCoordinate D S old L
        (k * normalizedCommonInterface D S old L M
          P.boundary.leftMask P.boundary.rightMask t) =
      P.rightNamedCoordinate D S old L k *
        (L (Step.meet S M P.rightNamed.source) P.rightNamed.source
          Finset.inter_subset_right).incl (P.namedNormalizedRight D S old L t) := by
  unfold AlignedNamedBoundary.rightNamedCoordinate
  rw [hP.2 k t, sourceMaskCast_mul, sourceMaskCast_restricted_incl]
  rfl

/-- Every parameter of the whole normalized interface has the same
image under the two translated historical block charts. -/
theorem AlignedNamedBoundary.named_normalized_boundary
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (hpoint : P.boundary.PointwiseNamed D S old L
      P.leftNamed P.rightNamed P.agree)
    (hmul : P.boundary.ParameterMultiplicative D S old L)
    (k : (old (common S P.boundary.leftMask P.boundary.rightMask)).Carrier)
    (g : (old P.leftNamed.source).Carrier)
    (shift : (old (Step.meet S M P.leftNamed.source)).Carrier)
    (hshift : g *
      (L (Step.meet S M P.leftNamed.source) P.leftNamed.source
        Finset.inter_subset_right).incl shift = P.leftNamedCoordinate D S old L k)
    (t : (old (Step.meet S M
      (common S P.boundary.leftMask P.boundary.rightMask))).Carrier) :
    P.leftNamed.chart.embed
      (g * (L (Step.meet S M P.leftNamed.source) P.leftNamed.source
        Finset.inter_subset_right).incl
          (shift * P.namedNormalizedLeft D S old L t)) =
    P.rightNamed.chart.embed
      (P.rightNamedCoordinate D S old L k *
        (L (Step.meet S M P.rightNamed.source) P.rightNamed.source
          Finset.inter_subset_right).incl (P.namedNormalizedRight D S old L t)) := by
  rw [map_mul, ← mul_assoc, hshift]
  rw [← P.leftNamedCoordinate_mul D S old L hmul,
    ← P.rightNamedCoordinate_mul D S old L hmul]
  exact (P.leftCoordinate_image D S old L hpoint _).trans
    (P.rightCoordinate_image D S old L hpoint _).symm

/-- The outgoing normalized interface in the identical middle named group. -/
noncomputable def AlignedNamedBoundary.nextNormalizedLeft
    {M : Proper S} {R : BuildResult D S old L}
    (P Q : AlignedNamedBoundary D S old L M R)
    (hMiddle : P.rightNamed = Q.leftNamed) :
    (old (Step.meet S M (common S Q.boundary.leftMask Q.boundary.rightMask))).Carrier →*
      (old (Step.meet S M P.rightNamed.source)).Carrier :=
  (sourceMaskCastHom S old (congrArg (Step.meet S M)
    (congrArg (fun T : NamedHistoricalBlock D S old L M R => T.source)
      hMiddle).symm)).comp (Q.namedNormalizedLeft D S old L)

/-- Naming the historical blocks leaves the canonical incoming subgroup
unchanged; only its parameter type was transported. -/
theorem AlignedNamedBoundary.namedNormalizedRight_range
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R) :
    (P.namedNormalizedRight D S old L).range =
      (normalizedCommonRight D S old L M
        P.leftNamed.source P.rightNamed.source).range :=
  normalizedCommonRight_range_cast D S old L M
    P.boundary.leftMask P.boundary.rightMask
    P.leftNamed.source P.rightNamed.source P.agree.1 P.agree.2.1

/-- The outgoing subgroup is exactly the canonical normalized subgroup
of the two named source blocks, in the common middle carrier. -/
theorem AlignedNamedBoundary.nextNormalizedLeft_range
    {M : Proper S} {R : BuildResult D S old L}
    (P Q : AlignedNamedBoundary D S old L M R)
    (hMiddle : P.rightNamed = Q.leftNamed) :
    (P.nextNormalizedLeft D S old L Q hMiddle).range =
      (normalizedCommonLeft D S old L M
        P.rightNamed.source Q.rightNamed.source).range := by
  let hsource := (congrArg
    (fun T : NamedHistoricalBlock D S old L M R => T.source) hMiddle).symm
  change ((sourceMaskCastHom S old (congrArg (Step.meet S M) hsource)).comp
    ((sourceMaskCastHom S old (congrArg (Step.meet S M) Q.agree.1)).comp
      (normalizedCommonLeft D S old L M
        Q.boundary.leftMask Q.boundary.rightMask))).range = _
  rw [← MonoidHom.comp_assoc, sourceMaskCastHom_comp]
  exact normalizedCommonLeft_range_cast D S old L M
    Q.boundary.leftMask Q.boundary.rightMask
    P.rightNamed.source Q.rightNamed.source
    (Q.agree.1.trans hsource) Q.agree.2.1

/-- Whole normalized entry and exit cosets are separated whenever the
two actual interface images are disjoint.  The maps are the original
normalized inclusions, with only the required source-index casts. -/
theorem AlignedNamedBoundary.normalized_separation
    {M : Proper S} {R : BuildResult D S old L}
    (P Q : AlignedNamedBoundary D S old L M R)
    (hMiddle : P.rightNamed = Q.leftNamed)
    (hpointP : P.boundary.PointwiseNamed D S old L
      P.leftNamed P.rightNamed P.agree)
    (hpointQ : Q.boundary.PointwiseNamed D S old L
      Q.leftNamed Q.rightNamed Q.agree)
    (hmulP : P.boundary.ParameterMultiplicative D S old L)
    (hmulQ : Q.boundary.ParameterMultiplicative D S old L)
    (hdisjoint : Disjoint (Set.range (P.boundary.interfaceMap D S old L))
      (Set.range (Q.boundary.interfaceMap D S old L)))
    (k : (old (common S P.boundary.leftMask P.boundary.rightMask)).Carrier)
    (l : (old (common S Q.boundary.leftMask Q.boundary.rightMask)).Carrier)
    (shift : (old (Step.meet S M P.rightNamed.source)).Carrier)
    (hshift : P.rightNamedCoordinate D S old L k *
      (L (Step.meet S M P.rightNamed.source) P.rightNamed.source
        Finset.inter_subset_right).incl shift =
      sourceMaskCast S old
        (congrArg (fun T : NamedHistoricalBlock D S old L M R => T.source)
          hMiddle).symm (Q.leftNamedCoordinate D S old L l)) :
    Disjoint
      (leftCoset (P.namedNormalizedRight D S old L).range 1)
      (leftCoset (P.nextNormalizedLeft D S old L Q hMiddle).range shift) := by
  let p := (L (Step.meet S M P.rightNamed.source) P.rightNamed.source
    Finset.inter_subset_right).incl
  let g := P.rightNamedCoordinate D S old L k
  let F := P.rightNamed.chart.embed
  apply Set.disjoint_left.mpr
  intro t htIn htOut
  change 1⁻¹ * t ∈ (P.namedNormalizedRight D S old L).range at htIn
  simp only [inv_one, one_mul] at htIn
  obtain ⟨a, ha⟩ := htIn
  have hIn : F (g * p t) ∈ Set.range (P.boundary.interfaceMap D S old L) := by
    refine ⟨k * normalizedCommonInterface D S old L M
      P.boundary.leftMask P.boundary.rightMask a, ?_⟩
    rw [← P.rightCoordinate_image D S old L hpointP]
    rw [P.rightNamedCoordinate_mul D S old L hmulP, ha]
  change shift⁻¹ * t ∈ (P.nextNormalizedLeft D S old L Q hMiddle).range at htOut
  obtain ⟨b, hb⟩ := htOut
  have ht : t = shift * P.nextNormalizedLeft D S old L Q hMiddle b := by
    calc
      t = shift * (shift⁻¹ * t) := by group
      _ = shift * P.nextNormalizedLeft D S old L Q hMiddle b := by rw [← hb]
  have hOut : F (g * p t) ∈ Set.range (Q.boundary.interfaceMap D S old L) := by
    refine ⟨l * normalizedCommonInterface D S old L M
      Q.boundary.leftMask Q.boundary.rightMask b, ?_⟩
    let hsource := (congrArg
      (fun T : NamedHistoricalBlock D S old L M R => T.source) hMiddle).symm
    have hcoord : g * p t = sourceMaskCast S old hsource
        (Q.leftNamedCoordinate D S old L
          (l * normalizedCommonInterface D S old L M
            Q.boundary.leftMask Q.boundary.rightMask b)) := by
      rw [ht, map_mul, ← mul_assoc]
      change (g * p shift) * p (P.nextNormalizedLeft D S old L Q hMiddle b) = _
      rw [hshift, Q.leftNamedCoordinate_mul D S old L hmulQ,
        sourceMaskCast_mul, sourceMaskCast_restricted_incl]
      rfl
    rw [hcoord]
    exact (Q.leftCoordinate_image D S old L hpointQ _).symm.trans
      (namedChart_apply_cast_of_eq D S old L P.rightNamed Q.leftNamed
        hMiddle _).symm
  exact (Set.disjoint_left.mp hdisjoint) hIn hOut

theorem historicalBoundaryList_adjacentDisjoint_tail
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (rest : List (AlignedNamedBoundary D S old L M R))
    (h : HistoricalBoundaryList.AdjacentInterfacesDisjoint
      D S old L (P :: rest)) :
    HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L rest := by
  cases rest with
  | nil => trivial
  | cons Q tail => exact h.2

theorem historicalBoundaryList_adjacentDisjoint_drop
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R))
    (n : Nat)
    (h : HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L hist) :
    HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L (hist.drop n) := by
  induction n generalizing hist with
  | zero => exact h
  | succ n ih =>
      cases hist with
      | nil => trivial
      | cons P rest =>
          exact ih rest (historicalBoundaryList_adjacentDisjoint_tail D S old L P rest h)

theorem historicalBoundaryList_adjacentDisjoint_take
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R))
    (n : Nat)
    (h : HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L hist) :
    HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L (hist.take n) := by
  induction n generalizing hist with
  | zero => trivial
  | succ n ih =>
      cases hist with
      | nil => trivial
      | cons P rest =>
          cases n with
          | zero => trivial
          | succ m =>
              cases rest with
              | nil => trivial
              | cons Q tail =>
                  exact ⟨h.1, ih (Q :: tail) h.2⟩

theorem historicalBoundaryList_adjacent_interface_disjoint
    {M : Proper S} {R : BuildResult D S old L}
    (pref : List (AlignedNamedBoundary D S old L M R))
    (P Q : AlignedNamedBoundary D S old L M R)
    (suffix : List (AlignedNamedBoundary D S old L M R))
    (h : HistoricalBoundaryList.AdjacentInterfacesDisjoint
      D S old L (pref ++ P :: Q :: suffix)) :
    Disjoint (Set.range (P.boundary.interfaceMap D S old L))
      (Set.range (Q.boundary.interfaceMap D S old L)) := by
  induction pref with
  | nil => exact h.1
  | cons A rest ih =>
      exact ih (historicalBoundaryList_adjacentDisjoint_tail
        D S old L A (rest ++ P :: Q :: suffix) h)

/-- In the actual finite construction, every consecutive active pair
has its unique normalized shift and disjoint normalized interface cosets.
Pointwise coordinates, multiplication laws, linkedness, and separation
are all supplied by the original construction. -/
theorem coveredBuildNonempty_internal_pair_shift_and_separation
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ []) (hsep : separatedList D S old L atoms)
    (q : (coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep).named.data.chain.state.Space)
    (front active : List (NamedHistoricalBlock D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain))
    (P Q : AlignedNamedBoundary D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain)
    (pref suffix : List (AlignedNamedBoundary D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain))
    (hpair : ((coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep).aligned.drop front.length).take
        (active.length - 1) = pref ++ P :: Q :: suffix)
    (cP : P.InterfaceChoice D S old L q)
    (cQ : Q.InterfaceChoice D S old L q) :
    let H := coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep
    let hMiddle : P.rightNamed = Q.leftNamed :=
      alignedBoundaryList_adjacent_middle_eq D S old L
        ((H.aligned.drop front.length).take (active.length - 1))
        (H.internal_boundaries_linked D S old L
          (coveredNamedAlignedBuildNonempty_linked D S old L M atoms hatoms hsep)
          front active) pref P Q suffix hpair
    let x := P.rightNamedCoordinate D S old L cP.parameter
    let y := sourceMaskCast S old
      (congrArg (fun T : NamedHistoricalBlock D S old L M H.named.data.chain =>
        T.source) hMiddle).symm (Q.leftNamedCoordinate D S old L cQ.parameter)
    ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
      x * (L (Step.meet S M P.rightNamed.source) P.rightNamed.source
        Finset.inter_subset_right).incl shift = y ∧
      Disjoint
        (leftCoset (normalizedCommonRight D S old L M
          P.leftNamed.source P.rightNamed.source).range 1)
        (leftCoset (normalizedCommonLeft D S old L M
          P.rightNamed.source Q.rightNamed.source).range shift) := by
  let H := coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep
  let hMiddle : P.rightNamed = Q.leftNamed :=
    alignedBoundaryList_adjacent_middle_eq D S old L
      ((H.aligned.drop front.length).take (active.length - 1))
      (H.internal_boundaries_linked D S old L
        (coveredNamedAlignedBuildNonempty_linked D S old L M atoms hatoms hsep)
        front active) pref P Q suffix hpair
  have hpSel : P ∈ (H.aligned.drop front.length).take (active.length - 1) := by
    rw [hpair]
    simp
  have hqSel : Q ∈ (H.aligned.drop front.length).take (active.length - 1) := by
    rw [hpair]
    simp
  have hP : P ∈ H.aligned := List.mem_of_mem_drop (List.mem_of_mem_take hpSel)
  have hQ : Q ∈ H.aligned := List.mem_of_mem_drop (List.mem_of_mem_take hqSel)
  have hselected : HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L
      ((H.aligned.drop front.length).take (active.length - 1)) :=
    historicalBoundaryList_adjacentDisjoint_take D S old L _ _
      (historicalBoundaryList_adjacentDisjoint_drop D S old L _ _
        (coveredNamedAlignedBuildNonempty_adjacentInterfacesDisjoint
          D S old L M atoms hatoms hsep))
  rw [hpair] at hselected
  have hdisj := historicalBoundaryList_adjacent_interface_disjoint
    D S old L pref P Q suffix hselected
  obtain ⟨shift, hshift, hunique⟩ :=
    coveredBuildNonempty_internal_pair_exact_shift
      D S old L M atoms hatoms hsep q front active P Q pref suffix hpair cP cQ
  refine ⟨shift, ⟨hshift, ?_⟩, ?_⟩
  · have hnorm := P.normalized_separation D S old L Q hMiddle
      (coveredNamedAlignedBuildNonempty_allPointwise D S old L M atoms hatoms hsep P hP)
      (coveredNamedAlignedBuildNonempty_allPointwise D S old L M atoms hatoms hsep Q hQ)
      (coveredNamedAlignedBuildNonempty_allParameterMultiplicative
        D S old L M atoms hatoms hsep P hP)
      (coveredNamedAlignedBuildNonempty_allParameterMultiplicative
        D S old L M atoms hatoms hsep Q hQ)
      hdisj cP.parameter cQ.parameter shift hshift
    simpa only [P.namedNormalizedRight_range D S old L,
      P.nextNormalizedLeft_range D S old L Q hMiddle] using hnorm
  · intro shift' hshift'
    exact hunique shift' hshift'.1

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
