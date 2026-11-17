import GluingEPPA.Steiner.ChainValuation.ActualActiveNormalizedSeparation
import GluingEPPA.Steiner.ChainValuation.NormalizedBoundaryAssembly
import GluingEPPA.Steiner.ChainValuation.BoundedActiveIntervalLength

/-!
# The actual proper active interval gives an earlier separated test

Choose one reached point on each genuine internal interface of the
active interval.  Consecutive choices determine unique shifts in the
restricted middle block.  Their normalized entry and exit cosets are
disjoint by separation in the original finite chain.

The resulting ordered list contains exactly the active source masks,
with repetitions retained.  It therefore has the active interval's
length and belongs to the original bounded `SeparatedChains` family
at the smaller mask.  The chosen shifts retain their exact equations
in the original historical coordinates for the subsequent component
map construction.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u v
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

omit [Finite V] [Fintype E] in
theorem namedAdjacentBlockPairs_snd_cons
    {M : Proper S} {R : BuildResult D S old L}
    (first : NamedHistoricalBlock D S old L M R)
    (rest : List (NamedHistoricalBlock D S old L M R)) :
    (namedAdjacentBlockPairs D S old L (first :: rest)).map Prod.snd = rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      change next :: (namedAdjacentBlockPairs D S old L (next :: rest)).map Prod.snd =
        next :: rest
      rw [ih]

/-- A nonempty boundary list recovers its ordered blocks from the
actual adjacent-pair identity, including repeated source occurrences. -/
theorem namedAdjacentBlockPairs_reconstruct
    {M : Proper S} {R : BuildResult D S old L} {B : Type v}
    (left right : B → NamedHistoricalBlock D S old L M R)
    (P : B) (rest : List B)
    (active : List (NamedHistoricalBlock D S old L M R))
    (hpairs : (P :: rest).map (fun Q => (left Q, right Q)) =
      namedAdjacentBlockPairs D S old L active) :
    left P :: (P :: rest).map right = active := by
  cases active with
  | nil => simp [namedAdjacentBlockPairs] at hpairs
  | cons first tail =>
      cases tail with
      | nil => simp [namedAdjacentBlockPairs] at hpairs
      | cons next tail =>
          have hfirst : left P = first :=
            congrArg Prod.fst (List.cons.inj hpairs).1
          have hright := congrArg (List.map Prod.snd) hpairs
          rw [namedAdjacentBlockPairs_snd_cons] at hright
          simp only [List.map_map, Function.comp_def] at hright
          rw [hfirst, hright]

theorem namedAdjacentBlockPairs_nil_singleton
    {M : Proper S} {R : BuildResult D S old L}
    (active : List (NamedHistoricalBlock D S old L M R)) (hne : active ≠ [])
    (hpairs : namedAdjacentBlockPairs D S old L active = []) :
    [active.head hne] = active := by
  cases active with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
      have hrest := congrArg (List.map Prod.snd) hpairs
      rw [namedAdjacentBlockPairs_snd_cons] at hrest
      simp only [List.map_nil] at hrest
      subst rest
      rfl

/-- An actual nonempty active interval whose source masks restrict
properly to M.  Every field concerns the canonical original builder. -/
structure ProperActiveInterval (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ []) (hsep : separatedList D S old L atoms)
    (q : (coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep).named.data.chain.state.Space) where
  front : List (NamedHistoricalBlock D S old L M
    (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain)
  active : List (NamedHistoricalBlock D S old L M
    (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain)
  back : List (NamedHistoricalBlock D S old L M
    (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain)
  decomposition :
    (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.named =
      front ++ active ++ back
  nonempty : active ≠ []
  proper : ∀ T ∈ active, ¬ M.val ⊆ T.source.val
  meets : ∀ T ∈ active,
    (T.toHistorical D S old L).Meets
      (block S old (coveredNamedAlignedBuildNonempty
        D S old L M atoms hatoms hsep).named.data.chain.current.1)
      (coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep).named.data.chain.state M.val q

namespace ProperActiveInterval

variable {M : Proper S} {atoms : List (Atom S old)}
variable {hatoms : atoms ≠ []} {hsep : separatedList D S old L atoms}
variable {q : (coveredNamedAlignedBuildNonempty D S old L M
  atoms hatoms hsep).named.data.chain.state.Space}
variable (I : ProperActiveInterval D S old L M atoms hatoms hsep q)

/-- The internal boundaries selected by their positions in the original history. -/
noncomputable def selected : List (AlignedNamedBoundary D S old L M
    (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain) :=
  ((coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).aligned.drop
    I.front.length).take (I.active.length - 1)

abbrev Boundary := {P // P ∈ I.selected D S old L}

theorem selected_linked :
    AlignedBoundaryList.Linked D S old L (I.selected D S old L) :=
  (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).internal_boundaries_linked
    D S old L (coveredNamedAlignedBuildNonempty_linked D S old L M atoms hatoms hsep)
    I.front I.active

theorem selected_pairs :
    (I.selected D S old L).map (fun P => (P.leftNamed, P.rightNamed)) =
      namedAdjacentBlockPairs D S old L I.active :=
  (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).internal_boundary_pairs
    D S old L (coveredNamedAlignedBuildNonempty_linked D S old L M atoms hatoms hsep)
    I.front I.active I.back I.decomposition I.nonempty

theorem endpoints_mem (P : I.Boundary D S old L) :
    P.val.leftNamed ∈ I.active ∧ P.val.rightNamed ∈ I.active := by
  apply namedAdjacentBlockPairs_endpoints_mem D S old L I.active
  rw [← I.selected_pairs D S old L]
  exact List.mem_map.mpr ⟨P.val, P.property, rfl⟩

theorem left_proper (P : I.Boundary D S old L) :
    ¬ M.val ⊆ P.val.leftNamed.source.val :=
  I.proper _ (I.endpoints_mem D S old L P).1

theorem right_proper (P : I.Boundary D S old L) :
    ¬ M.val ⊆ P.val.rightNamed.source.val :=
  I.proper _ (I.endpoints_mem D S old L P).2

/-- One genuine reached parameter for each selected historical boundary. -/
noncomputable def choice (P : I.Boundary D S old L) :
    P.val.InterfaceChoice D S old L q :=
  P.val.chooseInterface D S old L q
    ((coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).internal_boundary_both_active
      D S old L (coveredNamedAlignedBuildNonempty_linked D S old L M atoms hatoms hsep)
      q I.front I.active I.back I.decomposition I.nonempty I.meets P.val P.property)

/-- Adjacency means occurrence in the selected list, preserving its order. -/
def Adjacent (P Q : I.Boundary D S old L) : Prop :=
  ∃ pref suffix, I.selected D S old L = pref ++ P.val :: Q.val :: suffix

theorem middle_eq (P Q : I.Boundary D S old L)
    (h : I.Adjacent D S old L P Q) : P.val.rightNamed = Q.val.leftNamed := by
  obtain ⟨pref, suffix, hpair⟩ := h
  exact alignedBoundaryList_adjacent_middle_eq D S old L
    (I.selected D S old L) (I.selected_linked D S old L) pref P.val Q.val suffix hpair

/-- Both the coordinate equation and separation hold for the unique
actual displacement between the two chosen historical interface points. -/
theorem exists_unique_shift (P Q : I.Boundary D S old L)
    (h : I.Adjacent D S old L P Q) :
    ∃! shift : (old (Step.meet S M P.val.rightNamed.source)).Carrier,
      P.val.rightNamedCoordinate D S old L (I.choice D S old L P).parameter *
          (L (Step.meet S M P.val.rightNamed.source) P.val.rightNamed.source
            Finset.inter_subset_right).incl shift =
        sourceMaskCast S old
          (congrArg (fun T : NamedHistoricalBlock D S old L M
              (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain =>
            T.source) (I.middle_eq D S old L P Q h)).symm
          (Q.val.leftNamedCoordinate D S old L (I.choice D S old L Q).parameter) ∧
      Disjoint
        (leftCoset (normalizedCommonRight D S old L M
          P.val.leftNamed.source P.val.rightNamed.source).range 1)
        (leftCoset (normalizedCommonLeft D S old L M
          P.val.rightNamed.source Q.val.rightNamed.source).range shift) := by
  obtain ⟨pref, suffix, hpair⟩ := h
  exact coveredBuildNonempty_internal_pair_shift_and_separation
    D S old L M atoms hatoms hsep q I.front I.active P.val Q.val pref suffix hpair
    (I.choice D S old L P) (I.choice D S old L Q)

/-- Actual adjacent pairs use their unique coordinate displacement.
The unused values on nonadjacent pairs are set to one. -/
noncomputable def shift (P Q : I.Boundary D S old L) :
    (old (Step.meet S M P.val.rightNamed.source)).Carrier :=
  if h : I.Adjacent D S old L P Q then
    Classical.choose (I.exists_unique_shift D S old L P Q h).exists
  else 1

theorem shift_spec (P Q : I.Boundary D S old L)
    (h : I.Adjacent D S old L P Q) :
    P.val.rightNamedCoordinate D S old L (I.choice D S old L P).parameter *
        (L (Step.meet S M P.val.rightNamed.source) P.val.rightNamed.source
          Finset.inter_subset_right).incl (I.shift D S old L P Q) =
      sourceMaskCast S old
        (congrArg (fun T : NamedHistoricalBlock D S old L M
            (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain =>
          T.source) (I.middle_eq D S old L P Q h)).symm
        (Q.val.leftNamedCoordinate D S old L (I.choice D S old L Q).parameter) ∧
    Disjoint
      (leftCoset (normalizedCommonRight D S old L M
        P.val.leftNamed.source P.val.rightNamed.source).range 1)
      (leftCoset (normalizedCommonLeft D S old L M
        P.val.rightNamed.source Q.val.rightNamed.source).range (I.shift D S old L P Q)) := by
  simpa only [shift, dite_eq_left h] using
    Classical.choose_spec (I.exists_unique_shift D S old L P Q h).exists

theorem attached_isChain :
    (I.selected D S old L).attach.IsChain
      (NormalizationAdjacent D S old L M
        (fun P : I.Boundary D S old L => P.val.leftNamed.source)
        (fun P : I.Boundary D S old L => P.val.rightNamed.source)
        (I.shift D S old L)) := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro P Q pref suffix hpair
  have h : I.Adjacent D S old L P Q := by
    refine ⟨pref.map Subtype.val, suffix.map Subtype.val, ?_⟩
    have hval := congrArg (List.map Subtype.val) hpair
    simpa only [List.attach_map_subtype_val, List.map_append, List.map_cons] using hval
  exact ⟨congrArg (fun T => T.source) (I.middle_eq D S old L P Q h),
    (I.shift_spec D S old L P Q h).2⟩

/-- The singleton case uses the first active mask with shift one. -/
def firstSource : NormalizedProperSource S old M :=
  ⟨(I.active.head I.nonempty).source, I.proper _ (List.head_mem I.nonempty), 1⟩

/-- One normalized source per actual active block.  Internal shifts are
the displacements fixed by `choice` and `shift`; endpoint shifts are one. -/
noncomputable def sources : List (NormalizedProperSource S old M) :=
  match (I.selected D S old L).attach with
  | [] => [I.firstSource D S old L]
  | P :: rest => normalizedBoundarySources S old M
      (fun P : I.Boundary D S old L => P.val.leftNamed.source)
      (fun P : I.Boundary D S old L => P.val.rightNamed.source)
      (I.left_proper D S old L) (I.right_proper D S old L)
      (I.shift D S old L) P rest

/-- The source-mask list is exactly the original active list in order.
This is stronger than equality of lengths or equality of mask sets. -/
theorem sources_masks :
    (I.sources D S old L).map NormalizedProperSource.mask =
      I.active.map (fun T => T.source) := by
  cases hselected : (I.selected D S old L).attach with
  | nil =>
      have hempty : I.selected D S old L = [] := by
        have h := List.attach_map_subtype_val (I.selected D S old L)
        rw [hselected] at h
        exact h.symm
      have hpairs : namedAdjacentBlockPairs D S old L I.active = [] := by
        rw [← I.selected_pairs D S old L, hempty]
        rfl
      have hblocks := namedAdjacentBlockPairs_nil_singleton
        D S old L I.active I.nonempty hpairs
      simpa only [sources, hselected, firstSource, List.map_cons, List.map_nil] using
        congrArg (List.map (fun T => T.source)) hblocks
  | cons P rest =>
      have hpairs : (P :: rest).map (fun Q => (Q.val.leftNamed, Q.val.rightNamed)) =
          namedAdjacentBlockPairs D S old L I.active := by
        rw [← hselected, List.attach_map_val
          (l := I.selected D S old L)
          (f := fun Q : AlignedNamedBoundary D S old L M
            (coveredNamedAlignedBuildNonempty D S old L M atoms hatoms hsep).named.data.chain =>
              (Q.leftNamed, Q.rightNamed))]
        exact I.selected_pairs D S old L
      have hblocks := namedAdjacentBlockPairs_reconstruct D S old L
        (fun P : I.Boundary D S old L => P.val.leftNamed)
        (fun P : I.Boundary D S old L => P.val.rightNamed)
        P rest I.active hpairs
      have hmasks := congrArg (List.map (fun T => T.source)) hblocks
      simpa only [sources, hselected, normalizedBoundarySources_masks,
        List.map_cons, List.map_map, Function.comp_def] using hmasks

theorem sources_length : (I.sources D S old L).length = I.active.length := by
  have h := congrArg List.length (I.sources_masks D S old L)
  simpa only [List.length_map] using h

theorem sources_nonempty : I.sources D S old L ≠ [] := by
  intro h
  have hlen := I.sources_length D S old L
  rw [h, List.length_nil] at hlen
  exact I.nonempty (List.length_eq_zero_iff.mp hlen.symm)

/-- Normalized separation is proved from the actual original interfaces,
without a new assumption on the selected source list or its shifts. -/
theorem sources_separated : NormalizedSeparated D S old L M (I.sources D S old L) := by
  cases hselected : (I.selected D S old L).attach with
  | nil => simp only [sources, hselected, NormalizedSeparated]
  | cons P rest =>
      have hchain := I.attached_isChain D S old L
      rw [hselected] at hchain
      simp only [sources, hselected, normalizedBoundarySources]
      exact normalizedBoundaryTail_separated D S old L M
        (fun P : I.Boundary D S old L => P.val.leftNamed.source)
        (fun P : I.Boundary D S old L => P.val.rightNamed.source)
        (I.right_proper D S old L) (I.shift D S old L) P rest hchain
        ⟨P.val.leftNamed.source, I.left_proper D S old L P, 1⟩ rfl

theorem sources_length_le : (I.sources D S old L).length ≤ atoms.length := by
  rw [I.sources_length D S old L]
  exact coveredNamedBuildNonempty_active_length_le D S old L M atoms hatoms hsep
    I.front I.active I.back I.decomposition

/-- The actual proper active interval is a member of the genuine
bounded earlier test family at M. -/
noncomputable def test (N : Nat) (hbound : atoms.length ≤ N) :
    SeparatedChains D N M.val (smallerOld S old M) (smallerLinks D S old L M) :=
  normalizedProperSeparatedChain D S old L M N (I.sources D S old L)
    (I.sources_nonempty D S old L) ((I.sources_length_le D S old L).trans hbound)
    (I.sources_separated D S old L)

theorem test_length (N : Nat) (hbound : atoms.length ≤ N) :
    ((I.test D S old L N hbound).val.1.val : Nat) = I.active.length :=
  I.sources_length D S old L

end ProperActiveInterval

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
