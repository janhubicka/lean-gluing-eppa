import GluingEPPA.Steiner.RecordIsomorphism

/-!
# Naturality of the current recursively constructed record family

The induction compares every coordinate of the literal records. At the new
stage only proper-subset isomorphisms are supplied; preservation of new word
equalities is proved by `Step.preserves_word_equalities`. The resulting group
isomorphism is uniquely determined by its named generators. This proves
identity, composition, and compatibility with inclusion and deletion.
Graph isomorphisms are allowed to reverse undirected edges independently.
-/

namespace GluingEPPA.Steiner.EdgeGraph

universe u
variable {V E V' E' V'' E'' : Type u}
attribute [local instance] Classical.propDecidable

namespace RecursiveRecord

/-- Pull a finite set of edge names back along a bijection. -/
def pullbackSubset (p : E ≃ E') (T : Finset E') : Finset E :=
  T.map p.symm.toEmbedding

theorem pullback_mem (p : E ≃ E') (T : Finset E') (e : E) :
    e ∈ pullbackSubset p T ↔ p e ∈ T := by
  constructor
  · intro he
    obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp he
    change p.symm d = e at hde
    rw [← hde]
    simpa using hd
  · intro he
    exact Finset.mem_map.mpr ⟨p e, he, p.symm_apply_apply e⟩

/-- Proper subsets pull back to proper subsets, with no orientation choice. -/
def properPullback (p : E ≃ E') (S : Finset E) (T : Finset E')
    (hST : ∀ e, p e ∈ T ↔ e ∈ S) (j : Proper T) : Proper S :=
  ⟨pullbackSubset p j.val, by
    have hle : pullbackSubset p j.val ⊆ S := by
      intro e he
      exact (hST e).1 (j.property.1 ((pullback_mem p j.val e).1 he))
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hTj : T ⊆ j.val := by
      intro e he
      have hs : p.symm e ∈ S := (hST (p.symm e)).1 (by simpa using he)
      have hi : p.symm e ∈ pullbackSubset p j.val := by rw [heq]; exact hs
      simpa using (pullback_mem p j.val (p.symm e)).1 hi
    exact (not_le_of_gt j.property) hTj⟩

theorem properPullback_membership (p : E ≃ E') (S : Finset E) (T : Finset E')
    (hST : ∀ e, p e ∈ T ↔ e ∈ S) (j : Proper T) (e : E) :
    p e ∈ j.val ↔ e ∈ (properPullback p S T hST j).val :=
  (pullback_mem p j.val e).symm

variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']
variable (f : Iso D D')

/-- Isomorphisms exist for the particular family defined by the record recursion. -/
theorem family_iso_exists (S : Finset E) :
    ∀ T : Finset E', (∀ e, f.edge e ∈ T ↔ e ∈ S) →
      ∃ F : (family D S).Carrier ≃* (family D' T).Carrier,
        ∀ e ∈ S, F ((family D S).edge e) = (family D' T).edge (f.edge e) := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih T hST
  let old : ∀ i : Proper S, Data E i.val := fun i => family D i.val
  let old' : ∀ j : Proper T, Data E' j.val := fun j => family D' j.val
  have hTS : ∀ e, f.edge.symm e ∈ S ↔ e ∈ T := by
    intro e
    simpa using (hST (f.edge.symm e)).symm
  have forward : ∀ j : Proper T, ∃ i : Proper S,
      ∃ F : (old i).Carrier ≃* (old' j).Carrier,
        (∀ e, f.edge e ∈ j.val ↔ e ∈ i.val) ∧
        (∀ e ∈ i.val, F ((old i).edge e) = (old' j).edge (f.edge e)) := by
    intro j
    let i := properPullback f.edge S T hST j
    have hm : ∀ e, f.edge e ∈ j.val ↔ e ∈ i.val :=
      properPullback_membership f.edge S T hST j
    obtain ⟨F, hF⟩ := ih i.val i.property j.val hm
    exact ⟨i, F, hm, hF⟩
  have backward : ∀ i : Proper S, ∃ j : Proper T,
      ∃ F : (old' j).Carrier ≃* (old i).Carrier,
        (∀ e, f.edge.symm e ∈ i.val ↔ e ∈ j.val) ∧
        (∀ e ∈ j.val, F ((old' j).edge e) = (old i).edge (f.edge.symm e)) := by
    intro i
    let j := properPullback f.edge.symm T S hTS i
    have hm : ∀ e, f.edge.symm e ∈ i.val ↔ e ∈ j.val :=
      properPullback_membership f.edge.symm T S hTS i
    have hfwd : ∀ e, f.edge e ∈ j.val ↔ e ∈ i.val := by
      intro e
      simpa using (hm (f.edge e)).symm
    obtain ⟨F, hF⟩ := ih i.val i.property j.val hfwd
    refine ⟨j, F.symm, hm, ?_⟩
    intro e he
    apply F.injective
    have hh := hF (f.edge.symm e) ((hm e).2 he)
    simpa using hh.symm
  have hstep := Data.exists_equiv_of_word_equalities
    (Step.data D S old) (Step.data D' T old') f.edge hST
    (Step.preserves_word_equalities D S old D' f T old' hST forward)
    (Step.preserves_word_equalities D' T old' D f.symm S old hTS backward)
  rw [family_step D S, family_step D' T]
  exact hstep

/-- The named-generator rule uniquely determines the induced isomorphism. -/
noncomputable def naturalIso (S : Finset E) (T : Finset E')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S) :
    (family D S).Carrier ≃* (family D' T).Carrier :=
  Classical.choose (family_iso_exists D D' f S T hST)

theorem naturalIso_edge (S : Finset E) (T : Finset E')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S) (e : E) (he : e ∈ S) :
    naturalIso D D' f S T hST ((family D S).edge e) =
      (family D' T).edge (f.edge e) :=
  Classical.choose_spec (family_iso_exists D D' f S T hST) e he

/-- The extended generator functions also agree outside the indexing subset. -/
theorem naturalIso_all_edges (S : Finset E) (T : Finset E')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S) (e : E) :
    naturalIso D D' f S T hST ((family D S).edge e) =
      (family D' T).edge (f.edge e) := by
  by_cases he : e ∈ S
  · exact naturalIso_edge D D' f S T hST e he
  · have he' : f.edge e ∉ T := fun h => he ((hST e).1 h)
    rw [(family D S).outside e he, map_one, (family D' T).outside (f.edge e) he']

theorem naturalIso_word (S : Finset E) (T : Finset E')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S) (w : List E) :
    naturalIso D D' f S T hST ((w.map (family D S).edge).prod) =
      (w.map (fun e => (family D' T).edge (f.edge e))).prod := by
  induction w with
  | nil => simp
  | cons e w ih =>
      simp only [List.map_cons, List.prod_cons, map_mul]
      rw [naturalIso_all_edges D D' f S T hST e, ih]

end RecursiveRecord

namespace RecursiveRecord.Data
variable {H : Type u} {S : Finset E} [Group H]

theorem equiv_ext (A : Data E S) (F G : A.Carrier ≃* H)
    (h : ∀ e ∈ S, F (A.edge e) = G (A.edge e)) : F = G := by
  have hh : F.toMonoidHom = G.toMonoidHom := A.hom_ext _ _ h
  ext x
  exact DFunLike.congr_fun hh x

end RecursiveRecord.Data

namespace RecursiveRecord
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']
variable (D'' : EdgeGraph V'' E'') [Finite V''] [Fintype E''] [DecidableEq E'']

/-- Choosing representatives in the elementary word map does not affect identities. -/
theorem naturalIso_refl (S : Finset E) :
    naturalIso D D (Iso.refl D) S S (fun _ => Iff.rfl) =
      MulEquiv.refl (family D S).Carrier := by
  apply (family D S).equiv_ext
  intro e he
  exact naturalIso_edge D D (Iso.refl D) S S (fun _ => Iff.rfl) e he

/-- The isomorphisms compose exactly, not merely up to an unspecified automorphism. -/
theorem naturalIso_comp (f : Iso D D') (g : Iso D' D'')
    (S : Finset E) (T : Finset E') (U : Finset E'')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S)
    (hTU : ∀ e, g.edge e ∈ U ↔ e ∈ T) :
    (naturalIso D D' f S T hST).trans (naturalIso D' D'' g T U hTU) =
      naturalIso D D'' (f.trans g) S U (fun e => (hTU (f.edge e)).trans (hST e)) := by
  apply (family D S).equiv_ext
  intro e he
  change naturalIso D' D'' g T U hTU
      (naturalIso D D' f S T hST ((family D S).edge e)) = _
  rw [naturalIso_edge D D' f S T hST e he,
    naturalIso_edge D' D'' g T U hTU (f.edge e) ((hST e).2 he),
    naturalIso_edge D D'' (f.trans g) S U _ e he]
  rfl

/-- Inclusion commutes with relabelling, by its generator rule. -/
theorem naturalIso_inclusion (f : Iso D D') (M S : Finset E) (N T : Finset E')
    (hMS : M ⊆ S) (hNT : N ⊆ T)
    (hMN : ∀ e, f.edge e ∈ N ↔ e ∈ M)
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S) :
    (naturalIso D D' f S T hST).toMonoidHom.comp (inclusion D M S hMS) =
      (inclusion D' N T hNT).comp (naturalIso D D' f M N hMN).toMonoidHom := by
  apply (family D M).hom_ext
  intro e he
  change naturalIso D D' f S T hST (inclusion D M S hMS ((family D M).edge e)) =
    inclusion D' N T hNT (naturalIso D D' f M N hMN ((family D M).edge e))
  rw [inclusion_edge D M S hMS e he,
    naturalIso_edge D D' f S T hST e (hMS he),
    naturalIso_edge D D' f M N hMN e he,
    inclusion_edge D' N T hNT (f.edge e) ((hMN e).2 he)]

/-- Deletion commutes with relabelling, including letters that are deleted. -/
theorem naturalIso_deletion (f : Iso D D') (M S : Finset E) (N T : Finset E')
    (hMS : M ⊆ S) (hNT : N ⊆ T)
    (hMN : ∀ e, f.edge e ∈ N ↔ e ∈ M)
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S) :
    (naturalIso D D' f M N hMN).toMonoidHom.comp (deletion D M S hMS) =
      (deletion D' N T hNT).comp (naturalIso D D' f S T hST).toMonoidHom := by
  apply (family D S).hom_ext
  intro e he
  change naturalIso D D' f M N hMN (deletion D M S hMS ((family D S).edge e)) =
    deletion D' N T hNT (naturalIso D D' f S T hST ((family D S).edge e))
  rw [deletion_edge D M S hMS e he,
    naturalIso_edge D D' f S T hST e he,
    deletion_edge D' N T hNT (f.edge e) ((hST e).2 he)]
  by_cases hm : e ∈ M
  · rw [if_pos hm, if_pos ((hMN e).2 hm), naturalIso_edge D D' f M N hMN e hm]
  · have hn : f.edge e ∉ N := fun h => hm ((hMN e).1 h)
    rw [if_neg hm, if_neg hn, map_one]

/-- Naturality preserves actual restricted lift walks at their exact endpoints. -/
theorem naturalIso_cayleyWalk_iff (f : Iso D D') (S : Finset E) (T : Finset E')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S)
    (M : Set E) (N : Set E') (hMN : ∀ e, f.edge e ∈ N ↔ e ∈ M)
    (u v : V) (g h : (family D S).Carrier) :
    D'.CayleyWalk N (family D' T).edge (f.vertex u)
        (naturalIso D D' f S T hST g) (f.vertex v) (naturalIso D D' f S T hST h) ↔
      D.CayleyWalk M (family D S).edge u g v h :=
  Iso.cayleyWalk_iff f M N (family D S).edge (family D' T).edge
    (naturalIso D D' f S T hST) hMN
    (fun e _ => naturalIso_all_edges D D' f S T hST e) u v g h

end RecursiveRecord
end GluingEPPA.Steiner.EdgeGraph
