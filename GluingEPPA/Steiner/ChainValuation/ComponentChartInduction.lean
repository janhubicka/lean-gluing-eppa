import GluingEPPA.Steiner.ChainValuation.MatchedComponentLastChart
import GluingEPPA.Steiner.ChainValuation.UnmatchedComponentCharts
import GluingEPPA.Steiner.ChainValuation.CoveredNamedAlignedHistory

/-!
# Component charts which remain valid when the active interval ends

A last-block chart can be extended through a matched attachment. If a
component misses the new block, however, its normalized last mask stays
unchanged while the original chain's last mask changes. This requires a
plain component chart whose source mask is independent of the current
original mask, together with the stronger last-block chart for components
which still meet that last block.

The unmatched old case uses the exact full-component equivalence and its
genuine-edge reflection. The unmatched new case starts a translated
one-block chart. In the matched case the next shift is derived from the
actual last-block coset invariant, not assumed as a compatibility axiom.

These charts retain literal normalized chain-state constructions. Their
identification with bounded proper-mask `SeparatedChains` indices is a
separate integration obligation.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {X : Type v}

/-- Changing the root within one component changes only its membership
proofs, not any vertex coordinate. -/
def matchingComponentRebase
    (P : E → Matching X) (M : Finset E) (q r : X)
    (h : LabelReach (fun e => (P e).Rel) M q r) :
    MatchingReachComponent P M q ≃ MatchingReachComponent P M r where
  toFun x := ⟨x.val, LabelReach.trans (LabelReach.symm h) x.property⟩
  invFun x := ⟨x.val, LabelReach.trans h x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pointwise equivalent edge relations have identical component
carriers, with an equivalence whose underlying map is the identity. -/
def labelComponentEquivOfRelIff
    (P Q : E → X → X → Prop) (M : Finset E) (q : X)
    (h : ∀ e x y, P e x y ↔ Q e x y) :
    {x : X // LabelReach P M q x} ≃ {x : X // LabelReach Q M q x} where
  toFun x := ⟨x.val, (LabelReach.congr P Q M h q x.val).mp x.property⟩
  invFun x := ⟨x.val, (LabelReach.congr P Q M h q x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GluingEPPA.Steiner.ChainValuation

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

/-- A component chart remains meaningful after the component's final
active block is no longer the last block of the original chain. -/
structure ComponentChart (M : Proper S) (R : BuildResult D S old L)
    (q : R.state.Space) where
  sourceMask : Proper S
  source : ChainState.{u,u} E (block S old (Step.meet S M sourceMask))
  trace : NormalizedChainTrace D S old L M sourceMask source
  equiv : source.Space ≃ MatchingReachComponent R.state.matching M.val q
  edge_iff : ∀ e ∈ M.val, ∀ x z : source.Space,
    (source.matching e).Rel x z ↔
      (R.state.matching e).Rel (equiv x).val (equiv z).val

def ComponentLastChart.toComponentChart
    {M : Proper S} {R : BuildResult D S old L} {q : R.state.Space}
    (C : ComponentLastChart D S old L M R q) :
    ComponentChart D S old L M R q where
  sourceMask := R.current.1
  source := C.source
  trace := C.trace
  equiv := C.equiv
  edge_iff := C.edge_iff

def ComponentChart.rebase
    {M : Proper S} {R : BuildResult D S old L} {q r : R.state.Space}
    (C : ComponentChart D S old L M R q)
    (h : LabelReach (fun e => (R.state.matching e).Rel) M.val q r) :
    ComponentChart D S old L M R r where
  sourceMask := C.sourceMask
  source := C.source
  trace := C.trace
  equiv := C.equiv.trans (matchingComponentRebase R.state.matching M.val q r h)
  edge_iff := C.edge_iff

def ComponentLastChart.rebase
    {M : Proper S} {R : BuildResult D S old L} {q r : R.state.Space}
    (C : ComponentLastChart D S old L M R q)
    (h : LabelReach (fun e => (R.state.matching e).Rel) M.val q r) :
    ComponentLastChart D S old L M R r where
  source := C.source
  trace := C.trace
  base := C.base
  equiv := C.equiv.trans (matchingComponentRebase R.state.matching M.val q r h)
  last_val := C.last_val
  entry_mem := C.entry_mem
  edge_iff := C.edge_iff

/-- The matching completion, including absence of an edge, is preserved
by a plain component chart as well as by a last-block chart. -/
theorem ComponentChart.perm_val
    {M : Proper S} {R : BuildResult D S old L} {q : R.state.Space}
    (C : ComponentChart D S old L M R q)
    (e : E) (he : e ∈ M.val) (x : C.source.Space) :
    (C.equiv ((C.source.matching e).perm x)).val =
      (R.state.matching e).perm (C.equiv x).val :=
  componentChart_perm_val_of_edge_iff R.state.matching M.val q
    C.source.matching C.equiv C.edge_iff e he x

def AllComponentsCharted (M : Proper S) (R : BuildResult D S old L)
    (bound : Nat) : Prop :=
  ∀ q : R.state.Space, ∃ C : ComponentChart D S old L M R q,
    C.trace.length ≤ bound

def LastComponentsCharted (M : Proper S) (R : BuildResult D S old L)
    (bound : Nat) : Prop :=
  ∀ g : (old R.current.1).Carrier,
    ∃ C : ComponentLastChart D S old L M R (R.state.lastEmbed g),
      C.trace.length ≤ bound

def ComponentChartsInvariant (M : Proper S) (R : BuildResult D S old L)
    (bound : Nat) : Prop :=
  AllComponentsCharted D S old L M R bound ∧
    LastComponentsCharted D S old L M R bound

theorem componentChartsInvariant_initial (M : Proper S) (x : Atom S old) :
    ComponentChartsInvariant D S old L M (initial D S old L x) 1 := by
  constructor
  · intro q
    exact ⟨(ComponentLastChart.initial D S old L M x q).toComponentChart D S old L,
      Nat.le_refl 1⟩
  · intro q
    exact ⟨ComponentLastChart.initial D S old L M x q, Nat.le_refl 1⟩

section Step

variable (M : Proper S) (R : BuildResult D S old L) (y : Atom S old)
variable (hsep :
  match R.previous with
  | none => True
  | some p => tripleSeparated D S old L p R.current y)

noncomputable abbrev stepOldEmbedding : R.state.Space → (step D S old L R y hsep).state.Space :=
  oldEmbed (block S old R.current.1) (block S old y.1)
    R.state R.current.2
    (left D S old L R.current.1 y.1)
    (right D S old L R.current.1 y.1)
    (left_injective D S old L R.current.1 y.1)
    (right_injective D S old L R.current.1 y.1)

abbrev stepPushoutRelation :
    E → (step D S old L R y hsep).state.Space →
      (step D S old L R y hsep).state.Space → Prop :=
  pushoutLabelRel
    (fun e => (R.state.matching e).Rel)
    (fun e => ((block S old y.1).matching e).Rel)
    (attachInto R.state.lastEmbed R.current.2
      (left D S old L R.current.1 y.1))
    (right D S old L R.current.1 y.1)
    (attachInto_injective R.state.lastEmbed R.state.lastInjective R.current.2
      (left D S old L R.current.1 y.1)
      (left_injective D S old L R.current.1 y.1))
    (right_injective D S old L R.current.1 y.1)

theorem step_matching_iff_pushout (e : E)
    (x z : (step D S old L R y hsep).state.Space) :
    ((step D S old L R y hsep).state.matching e).Rel x z ↔
      stepPushoutRelation D S old L R y hsep e x z := by
  exact chainExtend_edge_iff_pushout
    (block S old R.current.1) (block S old y.1) R.state R.current.2
    (left D S old L R.current.1 y.1)
    (right D S old L R.current.1 y.1)
    (left_injective D S old L R.current.1 y.1)
    (right_injective D S old L R.current.1 y.1)
    (step_attachment_disjoint D S old L R y hsep)
    (fun e heA heB => shared_edge D S old L R.current.1 y.1 e heA heB)
    e x z

def stepPushoutComponentEquiv
    (q : (step D S old L R y hsep).state.Space) :
    {x : (step D S old L R y hsep).state.Space //
      LabelReach (stepPushoutRelation D S old L R y hsep) M.val q x} ≃
    MatchingReachComponent (step D S old L R y hsep).state.matching M.val q :=
  labelComponentEquivOfRelIff _ _ M.val q
    (fun e x z => (step_matching_iff_pushout D S old L R y hsep e x z).symm)

theorem step_old_reach_map {q x : R.state.Space}
    (h : LabelReach (fun e => (R.state.matching e).Rel) M.val q x) :
    LabelReach
      (fun e => ((step D S old L R y hsep).state.matching e).Rel) M.val
      (stepOldEmbedding D S old L R y hsep q)
      (stepOldEmbedding D S old L R y hsep x) := by
  apply LabelReach.map _ _ M.val (stepOldEmbedding D S old L R y hsep) _ h
  intro e a b hab
  exact Or.inl ⟨a, b, hab, rfl, rfl⟩

theorem step_new_reach_map {q x : (old y.1).Carrier}
    (h : LabelReach (fun e => ((block S old y.1).matching e).Rel) M.val q x) :
    LabelReach
      (fun e => ((step D S old L R y hsep).state.matching e).Rel) M.val
      ((step D S old L R y hsep).state.lastEmbed q)
      ((step D S old L R y hsep).state.lastEmbed x) := by
  apply LabelReach.map _ _ M.val (step D S old L R y hsep).state.lastEmbed _ h
  intro e a b hab
  rcases hab with ⟨he, rfl⟩
  exact (step D S old L R y hsep).state.last_active e he a

theorem step_attachment_point
    (k : (old (common S R.current.1 y.1)).Carrier) :
    stepOldEmbedding D S old L R y hsep
      (R.state.lastEmbed (R.current.2 * left D S old L R.current.1 y.1 k)) =
    (step D S old L R y hsep).state.lastEmbed
      (right D S old L R.current.1 y.1 k) :=
  pushout_attachment
    (attachInto R.state.lastEmbed R.current.2
      (left D S old L R.current.1 y.1))
    (right D S old L R.current.1 y.1)
    (attachInto_injective R.state.lastEmbed R.state.lastInjective R.current.2
      (left D S old L R.current.1 y.1)
      (left_injective D S old L R.current.1 y.1))
    (right_injective D S old L R.current.1 y.1) k

/-- An unmatched old component keeps its source state and exact labelled
chart, even though its last source mask is no longer the original last mask. -/
noncomputable def ComponentChart.persist
    (q : R.state.Space) (C : ComponentChart D S old L M R q)
    (hnomeet : ∀ k : (old (common S R.current.1 y.1)).Carrier,
      ¬ LabelReach (fun e => (R.state.matching e).Rel) M.val q
        (R.state.lastEmbed (R.current.2 * left D S old L R.current.1 y.1 k))) :
    ComponentChart D S old L M (step D S old L R y hsep)
      (stepOldEmbedding D S old L R y hsep q) := by
  let F := unmatchedOldComponentEquiv
    (fun e => (R.state.matching e).Rel)
    (fun e => ((block S old y.1).matching e).Rel) M.val
    (attachInto R.state.lastEmbed R.current.2
      (left D S old L R.current.1 y.1))
    (right D S old L R.current.1 y.1)
    (attachInto_injective R.state.lastEmbed R.state.lastInjective R.current.2
      (left D S old L R.current.1 y.1)
      (left_injective D S old L R.current.1 y.1))
    (right_injective D S old L R.current.1 y.1) q hnomeet
  refine
    { sourceMask := C.sourceMask
      source := C.source
      trace := C.trace
      equiv := C.equiv.trans (F.trans
        (stepPushoutComponentEquiv D S old L M R y hsep _))
      edge_iff := ?_ }
  intro e he x z
  exact (C.edge_iff e he x z).trans
    ((unmatchedOldComponentEquiv_edge_iff
      (fun e => (R.state.matching e).Rel)
      (fun e => ((block S old y.1).matching e).Rel) M.val
      (attachInto R.state.lastEmbed R.current.2
        (left D S old L R.current.1 y.1))
      (right D S old L R.current.1 y.1)
      (attachInto_injective R.state.lastEmbed R.state.lastInjective R.current.2
        (left D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1))
      (right_injective D S old L R.current.1 y.1) q hnomeet e
      (C.equiv x) (C.equiv z)).trans
      (step_matching_iff_pushout D S old L R y hsep e _ _).symm)

/-- A new coset missing the original attachment starts an exact
single-block last chart in the actual extended chain. -/
noncomputable def ComponentLastChart.unmatchedNew
    (q : (old y.1).Carrier)
    (hnomeet : ∀ k : (old (common S R.current.1 y.1)).Carrier,
      ¬ LabelReach (fun e => ((block S old y.1).matching e).Rel) M.val
        q (right D S old L R.current.1 y.1 k)) :
    ComponentLastChart D S old L M (step D S old L R y hsep)
      ((step D S old L R y hsep).state.lastEmbed q) := by
  let C := ComponentLastChart.initial D S old L M y q
  let F := unmatchedNewComponentEquiv
    (fun e => (R.state.matching e).Rel)
    (fun e => ((block S old y.1).matching e).Rel) M.val
    (attachInto R.state.lastEmbed R.current.2
      (left D S old L R.current.1 y.1))
    (right D S old L R.current.1 y.1)
    (attachInto_injective R.state.lastEmbed R.state.lastInjective R.current.2
      (left D S old L R.current.1 y.1)
      (left_injective D S old L R.current.1 y.1))
    (right_injective D S old L R.current.1 y.1) q hnomeet
  refine
    { source := C.source
      trace := C.trace
      base := q
      equiv := C.equiv.trans (F.trans
        (stepPushoutComponentEquiv D S old L M R y hsep _))
      last_val := ?_
      entry_mem := ?_
      edge_iff := ?_ }
  · intro t
    rfl
  · intro t ht
    exact False.elim ht
  · intro e he x z
    exact (C.edge_iff e he x z).trans
      ((unmatchedNewComponentEquiv_edge_iff
        (fun e => (R.state.matching e).Rel)
        (fun e => ((block S old y.1).matching e).Rel) M.val
        (attachInto R.state.lastEmbed R.current.2
          (left D S old L R.current.1 y.1))
        (right D S old L R.current.1 y.1)
        (attachInto_injective R.state.lastEmbed R.state.lastInjective R.current.2
          (left D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1))
        (right_injective D S old L R.current.1 y.1) q hnomeet e
        (C.equiv x) (C.equiv z)).trans
        (step_matching_iff_pushout D S old L R y hsep e _ _).symm)

/-- The next normalized shift exists by the checked last-block coset
invariant and the current chart. No new coordinate-surjectivity premise
is needed. -/
theorem ComponentLastChart.exists_shift
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space) (C : ComponentLastChart D S old L M R q)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val q
      (R.state.lastEmbed (R.current.2 * left D S old L R.current.1 y.1 k))) :
    ∃ shift : (old (Step.meet S M R.current.1)).Carrier,
      C.base * (L (Step.meet S M R.current.1) R.current.1
        Finset.inter_subset_right).incl shift =
        R.current.2 * left D S old L R.current.1 y.1 k := by
  have hBase : LabelReach (fun e => (R.state.matching e).Rel) M.val q
      (R.state.lastEmbed C.base) := by
    let t : (old (Step.meet S M R.current.1)).Carrier := 1
    have h := (C.equiv (C.source.lastEmbed t)).property
    have h' : LabelReach (fun e => (R.state.matching e).Rel) M.val q
        (R.state.lastEmbed (C.base *
          (L (Step.meet S M R.current.1) R.current.1 Finset.inter_subset_right).incl t)) :=
      C.last_val t ▸ h
    simpa only [t, map_one, mul_one] using h'
  have hmem := (hprev C.base
    (R.current.2 * left D S old L R.current.1 y.1 k)).mp
      (LabelReach.trans (LabelReach.symm hBase) hq)
  change C.base⁻¹ * (R.current.2 * left D S old L R.current.1 y.1 k) ∈
    (L (Step.meet S M R.current.1) R.current.1
      Finset.inter_subset_right).incl.range at hmem
  obtain ⟨shift, hshift⟩ := hmem
  refine ⟨shift, ?_⟩
  rw [hshift]
  exact mul_inv_cancel_left _ _

/-- Every component meeting the next original last block gets a last
chart. It either starts at an unmatched new coset or extends the previous
last chart through the complete matched interface. -/
theorem lastComponentsCharted_step
    (bound : Nat)
    (hprev : LastMaskCoset D S old L M R)
    (hcharts : LastComponentsCharted D S old L M R bound) :
    LastComponentsCharted D S old L M (step D S old L R y hsep) (bound + 1) := by
  intro q
  by_cases hmeet : ∃ k : (old (common S R.current.1 y.1)).Carrier,
      LabelReach (fun e => ((block S old y.1).matching e).Rel) M.val
        q (right D S old L R.current.1 y.1 k)
  · obtain ⟨k, hk⟩ := hmeet
    obtain ⟨C, hC⟩ := hcharts (R.current.2 * left D S old L R.current.1 y.1 k)
    obtain ⟨shift, hshift⟩ := C.exists_shift
      D S old L M R y hprev _ k (LabelReach.refl _)
    let C' := C.extend D S old L M R y hprev _ k (LabelReach.refl _)
      shift hshift hsep
    have hPath := step_new_reach_map D S old L M R y hsep (LabelReach.symm hk)
    rw [← step_attachment_point D S old L R y hsep k] at hPath
    refine ⟨C'.rebase D S old L hPath, ?_⟩
    change (C.extend D S old L M R y hprev _ k (LabelReach.refl _)
      shift hshift hsep).trace.length ≤ bound + 1
    rw [C.extend_trace_length D S old L M R y hprev _ k (LabelReach.refl _)
      shift hshift hsep]
    exact Nat.add_le_add_right hC 1
  · refine ⟨ComponentLastChart.unmatchedNew D S old L M R y hsep q
      (fun k hk => hmeet ⟨k, hk⟩), ?_⟩
    change 1 ≤ bound + 1
    exact Nat.succ_le_succ (Nat.zero_le bound)

/-- Plain charts cover every component of the next quotient. Old
components which miss the attachment persist; matched components can
be rooted in the new block, where the live last-chart invariant applies. -/
theorem allComponentsCharted_step
    (bound : Nat)
    (hcharts : AllComponentsCharted D S old L M R bound)
    (hlast : LastComponentsCharted D S old L M (step D S old L R y hsep) (bound + 1)) :
    AllComponentsCharted D S old L M (step D S old L R y hsep) (bound + 1) := by
  intro v
  refine Quotient.inductionOn v ?_
  intro s
  cases s with
  | inl q =>
      by_cases hmeet : ∃ k : (old (common S R.current.1 y.1)).Carrier,
          LabelReach (fun e => (R.state.matching e).Rel) M.val q
            (R.state.lastEmbed (R.current.2 * left D S old L R.current.1 y.1 k))
      · obtain ⟨k, hk⟩ := hmeet
        obtain ⟨C, hC⟩ := hlast (right D S old L R.current.1 y.1 k)
        have hPath := step_old_reach_map D S old L M R y hsep hk
        rw [step_attachment_point D S old L R y hsep k] at hPath
        exact ⟨(C.toComponentChart D S old L).rebase D S old L
          (LabelReach.symm hPath), hC⟩
      · obtain ⟨C, hC⟩ := hcharts q
        refine ⟨C.persist D S old L M R y hsep q
          (fun k hk => hmeet ⟨k, hk⟩), ?_⟩
        exact Nat.le_trans hC (Nat.le_succ bound)
  | inr q =>
      obtain ⟨C, hC⟩ := hlast q
      exact ⟨C.toComponentChart D S old L, hC⟩

theorem componentChartsInvariant_step
    (bound : Nat)
    (hprev : LastMaskCoset D S old L M R)
    (hcharts : ComponentChartsInvariant D S old L M R bound) :
    ComponentChartsInvariant D S old L M (step D S old L R y hsep) (bound + 1) := by
  have hlast := lastComponentsCharted_step D S old L M R y hsep bound hprev hcharts.2
  exact ⟨allComponentsCharted_step D S old L M R y hsep bound hcharts.1 hlast, hlast⟩

end Step

/-- Both chart invariants survive the literal finite tail recursion of
the canonical covered history. No component chart is assumed for a
later prefix. -/
theorem componentChartsInvariant_buildTail
    (M : Proper S) (p c : Atom S old)
    (H : CoveredNamedAlignedHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest))
    (bound : Nat)
    (hcharts : ComponentChartsInvariant D S old L M H.named.data.chain bound) :
    ComponentChartsInvariant D S old L M
      (coveredNamedAlignedBuildTail D S old L M p c H hp hc rest hsep).named.data.chain
      (bound + rest.length) := by
  induction rest generalizing p c H bound with
  | nil => exact hcharts
  | cons z zs ih =>
      have hstep :
          (match H.named.data.chain.previous with
          | none => True
          | some previous => tripleSeparated D S old L previous
              H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coveredNamedAlignedStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      have hnew : ComponentChartsInvariant D S old L M HN.named.data.chain (bound + 1) :=
        componentChartsInvariant_step D S old L M H.named.data.chain z hstep
          bound H.named.data.lastInv hcharts
      change ComponentChartsInvariant D S old L M
        (coveredNamedAlignedBuildTail D S old L M c z HN hnp hnc zs hsep.2).named.data.chain
        (bound + (z :: zs).length)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using
        ih c z HN hnp hnc hsep.2 (bound + 1) hnew

/-- Every component of every nonempty finite separated original chain
has an exact labelled chart; components meeting its last block retain
the stronger pointwise last-coordinate and entry-containment invariants.

The remaining normal-form obligation is to identify the source states
with bounded proper-mask recorded test indices. -/
theorem coveredBuildNonempty_componentsCharted
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ []) (hsep : separatedList D S old L atoms) :
    ComponentChartsInvariant D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M atoms hne hsep).named.data.chain
      atoms.length := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => exact componentChartsInvariant_initial D S old L M x
      | cons y ys =>
          let H0 := coveredNamedAlignedInitial D S old L M x
          let H1 := coveredNamedAlignedStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          have hbase : ComponentChartsInvariant D S old L M H1.named.data.chain 2 :=
            componentChartsInvariant_step D S old L M H0.named.data.chain y trivial
              1 H0.named.data.lastInv (componentChartsInvariant_initial D S old L M x)
          change ComponentChartsInvariant D S old L M
            (coveredNamedAlignedBuildTail D S old L M x y H1 hp hc ys hsep).named.data.chain
            (x :: y :: ys).length
          simpa only [List.length_cons, Nat.add_comm 2, Nat.add_assoc] using
            componentChartsInvariant_buildTail
              D S old L M x y H1 hp hc ys hsep 2 hbase

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
