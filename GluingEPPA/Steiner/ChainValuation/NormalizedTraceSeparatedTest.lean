import GluingEPPA.Steiner.ChainValuation.NormalizedChainTrace
import GluingEPPA.Steiner.ChainValuation.NormalizedProperAttachmentEquiv
import GluingEPPA.Steiner.ChainValuation.OrderedBuildTrace
import GluingEPPA.Steiner.ChainValuation.MatchingActionEquiv

/-!
# An exact normalized source trace is a genuine earlier chain test

A proper normalized trace can be reconstructed using the actual
smaller-stage `initial` and `step` constructors.  The reconstruction
retains the ordered source list, last-block coordinates, entry subset,
and every labelled edge.  Its ordered construction certificate identifies
the result with the literal `buildNonempty` used by `SeparatedChains`.

Thus a bounded proper source trace gives an earlier test together with
an equivalence of its exact source state and that test's actual space.
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

/-- The separation condition checked by `step` follows from separation
of the actual entry and outgoing attachment in its existing state. -/
theorem stepCondition_of_disjoint (R : BuildResult D S old L) (y : Atom S old)
    (hdisj : Disjoint R.state.entry
      (exitSet (block S old R.current.1) R.current.2
        (left D S old L R.current.1 y.1))) :
    match R.previous with
    | none => True
    | some p => tripleSeparated D S old L p R.current y := by
  cases hp : R.previous with
  | none => trivial
  | some p =>
      have he : R.state.entry = Set.range (right D S old L p.1 R.current.1) := by
        simpa only [hp] using R.entry_spec
      have hentry : Set.range (right D S old L p.1 R.current.1) =
          leftCoset (right D S old L p.1 R.current.1).range 1 :=
        range_eq_leftCoset_one _
      have hexit : exitSet (block S old R.current.1) R.current.2
          (left D S old L R.current.1 y.1) =
          leftCoset (left D S old L R.current.1 y.1).range R.current.2 :=
        translated_range_eq_leftCoset _ _
      rw [he, hentry, hexit] at hdisj
      exact hdisj

theorem buildNonempty_eq_of_list_eq
    (xs ys : List (Atom S old)) (hxy : xs = ys)
    (hx : xs ≠ []) (hy : ys ≠ [])
    (hsx : separatedList D S old L xs) (hsy : separatedList D S old L ys) :
    buildNonempty D S old L xs hx hsx = buildNonempty D S old L ys hy hsy := by
  cases hxy
  rfl

omit [Finite V] [Fintype E] [DecidableEq E] in
def someStateSpaceEquiv {X Y : SomeState S old} (h : X = Y) :
    X.state.Space ≃ Y.state.Space := by
  cases h
  exact Equiv.refl _

omit [Finite V] [Fintype E] [DecidableEq E] in
theorem someStateSpaceEquiv_edge_iff {X Y : SomeState S old} (h : X = Y)
    (e : E) (x y : X.state.Space) :
    (X.state.matching e).Rel x y ↔
      (Y.state.matching e).Rel (someStateSpaceEquiv S old h x) (someStateSpaceEquiv S old h y) := by
  cases h
  rfl

omit [Finite V] [Fintype E] [DecidableEq E] in
theorem someStateSpaceEquiv_last {X Y : SomeState S old} (h : X = Y)
    (t : (old X.current.1).Carrier) :
    someStateSpaceEquiv S old h (X.state.lastEmbed t) =
      Y.state.lastEmbed
        (properIndexMulEquiv S old (congrArg (fun Z : SomeState S old => Z.current.1) h) t) := by
  cases h
  rfl

namespace NormalizedChainTrace

variable {D S old L}
variable {M A : Proper S}
variable {C : ChainState.{u,u} E (block S old (Step.meet S M A))}

/-- A concrete smaller-stage realization with its exact ordered build
history and its coordinate-preserving equivalence from the traced state. -/
structure Realization (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (terminalShift : (old (Step.meet S M A)).Carrier) where
  previous : Option (Atom M.val (smallerOld S old M))
  state : ChainState.{u,u} E (block S old (Step.meet S M A))
  entry_spec :
    match previous with
    | none => state.entry = ∅
    | some p => state.entry = Set.range
        (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
          p.1 (normalizedProperAtom S old M
            ⟨A, hproper A T.last_mem_masks, terminalShift⟩).1)
  ordered : OrderedBuildTrace D M.val (smallerOld S old M) (smallerLinks D S old L M)
    ((T.sources hproper terminalShift).map (normalizedProperAtom S old M))
    { previous := previous
      current := normalizedProperAtom S old M
        ⟨A, hproper A T.last_mem_masks, terminalShift⟩
      state := state
      entry_spec := by cases previous <;> exact entry_spec }
  equiv : C.Space ≃ state.Space
  last : ∀ t, equiv (C.lastEmbed t) = state.lastEmbed t
  edge : ∀ e x y, (C.matching e).Rel x y ↔ (state.matching e).Rel (equiv x) (equiv y)
  entry : state.entry = C.entry

def Realization.toBuildResult
    {T : NormalizedChainTrace D S old L M A C}
    {hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val}
    {terminalShift : (old (Step.meet S M A)).Carrier}
    (R : T.Realization hproper terminalShift) :
    BuildResult D M.val (smallerOld S old M) (smallerLinks D S old L M) where
  previous := R.previous
  current := normalizedProperAtom S old M ⟨A, hproper A T.last_mem_masks, terminalShift⟩
  state := R.state
  entry_spec := by
    have he := R.entry_spec
    cases hp : R.previous <;> simp only [hp] at he <;> exact he

/-- Reconstruct the exact trace using the actual smaller `initial` and
`step`.  Every attachment equation is the checked canonical interface
reparametrization, and every new separation obligation is discharged. -/
noncomputable def realize (T : NormalizedChainTrace D S old L M A C) :
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val) →
    (terminalShift : (old (Step.meet S M A)).Carrier) →
    T.Realization hproper terminalShift := by
  induction T with
  | single A =>
      intro hproper terminalShift
      refine
        { previous := none
          state := ChainState.first (block S old (Step.meet S M A))
          entry_spec := rfl
          ordered := ?_
          equiv := Equiv.refl _
          last := fun _ => rfl
          edge := fun _ _ _ => Iff.rfl
          entry := rfl }
      exact OrderedBuildTrace.single (D := D) (S := M.val)
        (old := smallerOld S old M) (L := smallerLinks D S old L M)
        (normalizedProperAtom S old M ⟨A, hproper A (by simp [masks]), terminalShift⟩)
  | @attach A C previous B shift hsep hshared ih =>
      intro hproper terminalShift
      let hprev : ∀ X ∈ previous.masks, ¬ M.val ⊆ X.val :=
        fun X hX => hproper X (by simp [masks, hX])
      let hA : ¬ M.val ⊆ A.val := hprev A previous.last_mem_masks
      let hB : ¬ M.val ⊆ B.val := hproper B (by simp [masks])
      let R := ih hprev shift
      let RP := R.toBuildResult
      let y : Atom M.val (smallerOld S old M) :=
        normalizedProperAtom S old M ⟨B, hB, terminalShift⟩
      have hdisj : Disjoint RP.state.entry
          (exitSet (block M.val (smallerOld S old M) RP.current.1) RP.current.2
            (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
              RP.current.1 y.1)) :=
        normalizedProper_target_separated D S old L M A B hA hB C R.state
          shift R.entry hsep
      let hstep := stepCondition_of_disjoint
        D M.val (smallerOld S old M) (smallerLinks D S old L M) RP y hdisj
      let RN := step D M.val (smallerOld S old M) (smallerLinks D S old L M) RP y hstep
      let F := normalizedProperAttachmentEquiv D S old L M A B hA hB
        C R.state R.equiv R.last shift
      refine
        { previous := some RP.current
          state := RN.state
          entry_spec := rfl
          ordered := ?_
          equiv := F
          last := ?_
          edge := ?_
          entry := ?_ }
      · change OrderedBuildTrace D M.val (smallerOld S old M) (smallerLinks D S old L M)
          ((previous.sources hprev shift ++
            [(⟨B, hB, terminalShift⟩ : NormalizedProperSource S old M)]).map
            (normalizedProperAtom S old M)) RN
        rw [List.map_append, List.map_cons, List.map_nil]
        exact OrderedBuildTrace.attach R.ordered y hstep
      · exact normalizedProperAttachmentEquiv_new D S old L M A B hA hB
          C R.state R.equiv R.last shift
      · intro e x y
        exact normalizedProperAttachmentEquiv_edge_iff D S old L M A B hA hB
          C R.state R.equiv R.last shift e (R.edge e) x y
      · exact normalizedProper_entrySet D S old L M A B hA hB

theorem sources_nonempty (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (terminalShift : (old (Step.meet S M A)).Carrier) :
    T.sources hproper terminalShift ≠ [] := by
  intro h
  have hmasks := T.sources_masks hproper terminalShift
  rw [h, List.map_nil] at hmasks
  exact T.masks_ne_nil hmasks.symm

/-- Separation is supplied by the actual normalized construction trace. -/
theorem sources_separated (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (terminalShift : (old (Step.meet S M A)).Carrier) :
    NormalizedSeparated D S old L M (T.sources hproper terminalShift) :=
  (normalizedProperList_separated_iff D S old L M (T.sources hproper terminalShift)).mp
    ((T.realize hproper terminalShift).ordered.separated
      D M.val (smallerOld S old M) (smallerLinks D S old L M))

/-- The exact normalized source belongs to the literal bounded earlier
test family.  Its unused terminal shift is chosen to be one. -/
noncomputable def toSeparatedTest (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (N : Nat) (hbound : T.length ≤ N) :
    SeparatedChains D N M.val (smallerOld S old M) (smallerLinks D S old L M) :=
  normalizedProperSeparatedChain D S old L M N (T.sources hproper 1)
    (T.sources_nonempty hproper 1)
    (by rw [T.sources_length hproper 1]; exact hbound)
    (T.sources_separated hproper 1)

theorem toSeparatedTest_length (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (N : Nat) (hbound : T.length ≤ N) :
    ((T.toSeparatedTest hproper N hbound).val.1.val : Nat) = T.length :=
  T.sources_length hproper 1

theorem toSeparatedTest_atoms (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (N : Nat) (hbound : T.length ≤ N) :
    List.ofFn (T.toSeparatedTest hproper N hbound).val.2 =
      (T.sources hproper 1).map (normalizedProperAtom S old M) :=
  List.ofFn_getElem_eq_map (T.sources hproper 1) (normalizedProperAtom S old M)

/-- The reconstructed initial/step state is exactly the state used by
the genuine earlier test, including its dependent final atom. -/
theorem test_state_eq (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (N : Nat) (hbound : T.length ≤ N) :
    let R := T.realize hproper 1
    (⟨R.toBuildResult.current, R.state⟩ : SomeState M.val (smallerOld S old M)) =
      chainState D N M.val (smallerOld S old M) (smallerLinks D S old L M)
        (T.toSeparatedTest hproper N hbound) := by
  intro R
  exact (R.ordered.state_eq D M.val (smallerOld S old M) (smallerLinks D S old L M)).trans
    (buildNonempty_eq_of_list_eq D M.val (smallerOld S old M) (smallerLinks D S old L M)
      _ _ (T.toSeparatedTest_atoms hproper N hbound).symm _ _ _ _)

/-- An equivalence from the exact normalized trace state to the actual
space of the earlier bounded separated-chain test. -/
noncomputable def testEquiv (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (N : Nat) (hbound : T.length ≤ N) :
    C.Space ≃ chainSpace D N M.val (smallerOld S old M) (smallerLinks D S old L M)
      (T.toSeparatedTest hproper N hbound) :=
  (T.realize hproper 1).equiv.trans
    (someStateSpaceEquiv M.val (smallerOld S old M) (T.test_state_eq hproper N hbound))

theorem testEquiv_edge_iff (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (N : Nat) (hbound : T.length ≤ N) (e : E) (x y : C.Space) :
    (C.matching e).Rel x y ↔
      ((chainState D N M.val (smallerOld S old M) (smallerLinks D S old L M)
        (T.toSeparatedTest hproper N hbound)).state.matching e).Rel
        (T.testEquiv hproper N hbound x) (T.testEquiv hproper N hbound y) :=
  ((T.realize hproper 1).edge e x y).trans
    (someStateSpaceEquiv_edge_iff M.val (smallerOld S old M)
      (T.test_state_eq hproper N hbound) e _ _)

theorem testEquiv_last (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (N : Nat) (hbound : T.length ≤ N) (t : (old (Step.meet S M A)).Carrier) :
    T.testEquiv hproper N hbound (C.lastEmbed t) =
      (chainState D N M.val (smallerOld S old M) (smallerLinks D S old L M)
        (T.toSeparatedTest hproper N hbound)).state.lastEmbed
        (properIndexMulEquiv M.val (smallerOld S old M)
          (congrArg (fun Z : SomeState M.val (smallerOld S old M) => Z.current.1)
            (T.test_state_eq hproper N hbound)) t) := by
  exact (congrArg
    (someStateSpaceEquiv M.val (smallerOld S old M) (T.test_state_eq hproper N hbound))
    ((T.realize hproper 1).last t)).trans
      (someStateSpaceEquiv_last M.val (smallerOld S old M)
        (T.test_state_eq hproper N hbound) t)

/-- The equivalence conjugates every completed letter permutation,
including vertices where the partial matching has no genuine edge. -/
theorem testEquiv_perm (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (N : Nat) (hbound : T.length ≤ N) (e : E) (x : C.Space) :
    T.testEquiv hproper N hbound ((C.matching e).perm x) =
      chainPerm D N M.val (smallerOld S old M) (smallerLinks D S old L M)
        (T.toSeparatedTest hproper N hbound) e (T.testEquiv hproper N hbound x) :=
  matching_perm_conjugate_of_rel_iff (T.testEquiv hproper N hbound) (C.matching e)
    ((chainState D N M.val (smallerOld S old M) (smallerLinks D S old L M)
      (T.toSeparatedTest hproper N hbound)).state.matching e)
    (T.testEquiv_edge_iff hproper N hbound e) x

end NormalizedChainTrace

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
