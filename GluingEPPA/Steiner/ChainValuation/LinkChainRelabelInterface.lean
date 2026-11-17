import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelAugmentedStep

/-!
# Interface compatibility forced by previous-stage generator isomorphisms

The prior naturality modules assumed a RelabelData including two interface
squares. This file derives both squares from the actual Link generator laws,
so that the next induction only needs old-stage group isomorphisms.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain

universe u
variable {V E V' E' : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']
variable (S : Finset E) (T : Finset E')
variable (old : ∀ i : Proper S, Data E i.val)
variable (old' : ∀ i : Proper T, Data E' i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))
variable (L' : ∀ m t : Proper T, m.val ⊆ t.val → Link D' (old' m) (old' t))

/-- Only the old-stage group equivalences and their generator equations. -/
structure ProperStageRelabel (p : E ≃ E') where
  proper : Proper S ≃ Proper T
  stage : ∀ i : Proper S, (old i).Carrier ≃* (old' (proper i)).Carrier
  active : ∀ i e, e ∈ i.val ↔ p e ∈ (proper i).val
  edge : ∀ i e, e ∈ i.val →
    stage i ((old i).edge e) = (old' (proper i)).edge (p e)

namespace ProperStageRelabel

variable {p : E ≃ E'}

/-- Intersections of actual proper stages commute with edge renaming. -/
theorem common_reindex
    (R : ProperStageRelabel D D' S T old old' L L' p)
    (i j : Proper S) :
    R.proper (common S i j) = common T (R.proper i) (R.proper j) := by
  apply Subtype.ext
  ext e'
  obtain ⟨e, rfl⟩ := p.surjective e'
  change p e ∈ (R.proper (common S i j)).val ↔
    p e ∈ (common T (R.proper i) (R.proper j)).val
  rw [← R.active (common S i j) e]
  change e ∈ i.val ∩ j.val ↔
    p e ∈ (R.proper i).val ∩ (R.proper j).val
  simp only [Finset.mem_inter]
  exact and_congr (R.active i e) (R.active j e)

/-- The actual intersection-stage equivalence from the prior-stage data. -/
noncomputable def common_stage_equiv
    (R : ProperStageRelabel D D' S T old old' L L' p)
    (i j : Proper S) :
    (old (common S i j)).Carrier ≃*
      (old' (common T (R.proper i) (R.proper j))).Carrier := by
  have h := common_reindex D D' S T old old' L L' R i j
  cases h
  exact R.stage (common S i j)

theorem common_stage_edge
    (R : ProperStageRelabel D D' S T old old' L L' p)
    (i j : Proper S) (e : E)
    (he : e ∈ (common S i j).val) :
    common_stage_equiv D D' S T old old' L L' R i j
        ((old (common S i j)).edge e) =
      (old' (common T (R.proper i) (R.proper j))).edge (p e) := by
  have h := common_reindex D D' S T old old' L L' R i j
  cases h
  exact R.edge (common S i j) e he

/-- The left Link square is determined on the named generators. -/
theorem left_comm
    (R : ProperStageRelabel D D' S T old old' L L' p)
    (i j : Proper S)
    (k : (old (common S i j)).Carrier) :
    R.stage i (left D S old L i j k) =
      left D' T old' L' (R.proper i) (R.proper j)
        (common_stage_equiv D D' S T old old' L L' R i j k) := by
  have hhom :
      (R.stage i).toMonoidHom.comp (left D S old L i j) =
        (left D' T old' L' (R.proper i) (R.proper j)).comp
          (common_stage_equiv D D' S T old old' L L' R i j).toMonoidHom := by
    apply (old (common S i j)).hom_ext
    intro e he
    have hei : e ∈ i.val := Finset.inter_subset_left he
    have htarget : p e ∈ (common T (R.proper i) (R.proper j)).val := by
      rw [← common_reindex D D' S T old old' L L' R i j]
      exact (R.active (common S i j) e).mp he
    have ha := (L (common S i j) i Finset.inter_subset_left).incl_edge e he
    have hb := (L' (common T (R.proper i) (R.proper j))
        (R.proper i) Finset.inter_subset_left).incl_edge (p e) htarget
    change R.stage i (left D S old L i j ((old (common S i j)).edge e)) =
      left D' T old' L' (R.proper i) (R.proper j)
        (common_stage_equiv D D' S T old old' L L' R i j
          ((old (common S i j)).edge e))
    rw [ha, common_stage_edge D D' S T old old' L L' R i j e he, hb]
    exact R.edge i e hei
  exact DFunLike.congr_fun hhom k

/-- The right Link square is also forced by the named generators. -/
theorem right_comm
    (R : ProperStageRelabel D D' S T old old' L L' p)
    (i j : Proper S)
    (k : (old (common S i j)).Carrier) :
    R.stage j (right D S old L i j k) =
      right D' T old' L' (R.proper i) (R.proper j)
        (common_stage_equiv D D' S T old old' L L' R i j k) := by
  have hhom :
      (R.stage j).toMonoidHom.comp (right D S old L i j) =
        (right D' T old' L' (R.proper i) (R.proper j)).comp
          (common_stage_equiv D D' S T old old' L L' R i j).toMonoidHom := by
    apply (old (common S i j)).hom_ext
    intro e he
    have hej : e ∈ j.val := Finset.inter_subset_right he
    have htarget : p e ∈ (common T (R.proper i) (R.proper j)).val := by
      rw [← common_reindex D D' S T old old' L L' R i j]
      exact (R.active (common S i j) e).mp he
    have ha := (L (common S i j) j Finset.inter_subset_right).incl_edge e he
    have hb := (L' (common T (R.proper i) (R.proper j))
        (R.proper j) Finset.inter_subset_right).incl_edge (p e) htarget
    change R.stage j (right D S old L i j ((old (common S i j)).edge e)) =
      right D' T old' L' (R.proper i) (R.proper j)
        (common_stage_equiv D D' S T old old' L L' R i j
          ((old (common S i j)).edge e))
    rw [ha, common_stage_edge D D' S T old old' L L' R i j e he, hb]
    exact R.edge j e hej
  exact DFunLike.congr_fun hhom k

/-- Package the automatically generated interface squares as the exact
RelabelData used by the actual bounded-chain naturality theorem. -/
noncomputable def toRelabelData
    (R : ProperStageRelabel D D' S T old old' L L' p) :
    RelabelData D D' S T old old' L L' p where
  proper := R.proper
  stage := R.stage
  active := R.active
  edge := R.edge
  interface := common_stage_equiv D D' S T old old' L L' R
  leftComm := left_comm D D' S T old old' L L' R
  rightComm := right_comm D D' S T old old' L L' R

end ProperStageRelabel
end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain
