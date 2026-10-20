import GluingEPPA.Steiner.RecursiveRecord

/-!
# Inclusion, deletion, and exact replacement for the actual recursive family

This file supplies the earlier-stage inputs of the compatibility lemma by
strong induction on the edge set. All carriers are `RecursiveRecord.family`;
no existential substitute group and no older finite-family theorem is used.
The smaller component action comes from that family's literal record equation.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} (D : EdgeGraph V E)

/-- Properties (I) and (II) for a particular inclusion of two constructed stages. -/
structure Link {M S : Finset E} (A : Data E M) (B : Data E S) where
  incl : A.Carrier →* B.Carrier
  incl_edge : ∀ e ∈ M, incl (A.edge e) = B.edge e
  delete : B.Carrier →* A.Carrier
  delete_edge : ∀ e ∈ S, delete (B.edge e) = if e ∈ M then A.edge e else 1
  replace : ∀ u v g, D.WalkValue (S : Set E) B.edge u v (incl g) →
    D.WalkValue (M : Set E) A.edge u v g

namespace Data

/-- Homomorphisms out of a stage agree if they agree on its named generators. -/
theorem hom_ext {S : Finset E} (A : Data E S) {H : Type u} [Group H]
    (f g : A.Carrier →* H) (h : ∀ e ∈ S, f (A.edge e) = g (A.edge e)) : f = g := by
  ext x
  obtain ⟨w, hw, rfl⟩ := A.generated x
  induction w with
  | nil => simp
  | cons e w ih =>
      have he := hw e (by simp)
      have hw' : ∀ k ∈ w, k ∈ S := fun k hk => hw k (by simp [hk])
      simp only [List.map_cons, List.prod_cons, map_mul]
      rw [h e he, ih hw']

end Data

namespace Link

noncomputable def refl (S : Finset E) (A : Data E S) : Link D A A where
  incl := MonoidHom.id _
  incl_edge _ _ := rfl
  delete := MonoidHom.id _
  delete_edge e he := by simp [he]
  replace _ _ _ p := p

theorem left_inverse {M S : Finset E} (A : Data E M) (B : Data E S)
    (hMS : M ⊆ S) (L : Link D A B) : L.delete.comp L.incl = MonoidHom.id _ := by
  apply A.hom_ext
  intro e he
  change L.delete (L.incl (A.edge e)) = A.edge e
  rw [L.incl_edge e he, L.delete_edge e (hMS he), if_pos he]

theorem injective {M S : Finset E} (A : Data E M) (B : Data E S)
    (hMS : M ⊆ S) (L : Link D A B) : Function.Injective L.incl := by
  intro g h hgh
  have hleft := left_inverse D A B hMS L
  have hg : L.delete (L.incl g) = g := DFunLike.congr_fun hleft g
  have hh : L.delete (L.incl h) = h := DFunLike.congr_fun hleft h
  exact hg.symm.trans ((congrArg L.delete hgh).trans hh)

end Link

/-- A word of an actual walk uses only its allowed edges. -/
theorem wordWalk_letters {S : Set E} {u v : V} {w : List E}
    (p : D.WordWalk S u w v) : ∀ e ∈ w, e ∈ S := by
  induction p with
  | nil => simp
  | @cons u v z e w he hj p ih =>
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he
      · exact ih f hf

variable [Finite V] [Fintype E] [DecidableEq E]

namespace Step

variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)

/-- Intersections of earlier subsets are themselves earlier subsets. -/
def meet (k i : Proper S) : Proper S :=
  ⟨k.val ∩ i.val, lt_of_le_of_lt Finset.inter_subset_left k.property⟩

theorem meet_lt_left {k i : Proper S} (h : ¬ k.val ⊆ i.val) :
    (meet S k i).val ⊂ k.val := by
  refine lt_of_le_of_ne Finset.inter_subset_left ?_
  intro heq
  apply h
  intro e he
  have : e ∈ (meet S k i).val := by rw [heq]; exact he
  exact (Finset.mem_inter.mp this).2

abbrev components (i : Proper S) :=
  D.Component (sets S i) (edges S old i) (involutions S old i)

variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))
variable (A : ∀ n m : Proper S, n.val ⊂ m.val →
  RightAction (old m).Carrier (components D S old n))
variable (hA : ∀ (n m : Proper S) (h : n.val ⊂ m.val) e, e ∈ m.val → ∀ c,
  (A n m h).act c ((old m).edge e) =
    D.componentEdgePerm (sets S n) (edges S old n) (involutions S old n) e c)

/-- The K_T coordinate of i_M^S factors through K_(M intersection T). -/
def groupHom (k i : Proper S) : (old k).Carrier →* (old i).Carrier :=
  (L (meet S k i) i Finset.inter_subset_right).incl.comp
    (L (meet S k i) k Finset.inter_subset_left).delete

theorem groupHom_edge (k i : Proper S) (e : E) (he : e ∈ k.val) :
    groupHom D S old L k i ((old k).edge e) =
      if e ∈ i.val then (old i).edge e else 1 := by
  change (L (meet S k i) i Finset.inter_subset_right).incl
    ((L (meet S k i) k Finset.inter_subset_left).delete ((old k).edge e)) = _
  rw [(L (meet S k i) k Finset.inter_subset_left).delete_edge e he]
  by_cases hi : e ∈ i.val
  · have hn : e ∈ (meet S k i).val := Finset.mem_inter.mpr ⟨he, hi⟩
    rw [if_pos hn, if_pos hi,
      (L (meet S k i) i Finset.inter_subset_right).incl_edge e hn]
  · have hn : e ∉ (meet S k i).val := fun h => hi (Finset.mem_inter.mp h).2
    rw [if_neg hn, if_neg hi, map_one]

/-- Lemma 4.1, using only links and coordinate actions of proper subsets. -/
noncomputable def compatibleAction (k i : Proper S) :
    RightAction (old k).Carrier (components D S old i) :=
  if h : k.val ⊆ i.val then
    (D.componentGroupAction (sets S i) (edges S old i) (involutions S old i)).comap
      (L k i h).incl
  else
    D.componentCompatibilityAction
      (sets S (meet S k i)) (sets S i)
      (edges S old (meet S k i)) (edges S old i)
      (involutions S old (meet S k i)) (involutions S old i)
      Finset.inter_subset_right
      (L (meet S k i) i Finset.inter_subset_right).incl
      (L (meet S k i) i Finset.inter_subset_right).incl_edge
      (L (meet S k i) i Finset.inter_subset_right).replace
      (L (meet S k i) k Finset.inter_subset_left).delete
      (A (meet S k i) k (meet_lt_left S h))

include hA in
theorem compatibleAction_edge (k i : Proper S) (e : E) (he : e ∈ k.val)
    (c : components D S old i) :
    (compatibleAction D S old L A k i).act c ((old k).edge e) =
      D.componentEdgePerm (sets S i) (edges S old i) (involutions S old i) e c := by
  unfold compatibleAction
  split
  next h =>
    exact D.componentGroupAction_comap_edge (sets S k) (sets S i) h
      (edges S old k) (edges S old i) (involutions S old i)
      (L k i h).incl (L k i h).incl_edge he c
  next h =>
    apply D.componentCompatibilityAction_edge
      (sets S (meet S k i)) (sets S i)
      (edges S old (meet S k i)) (edges S old i)
      (involutions S old (meet S k i)) (involutions S old i)
      Finset.inter_subset_right
      (L (meet S k i) i Finset.inter_subset_right).incl
      (L (meet S k i) i Finset.inter_subset_right).incl_edge
      (L (meet S k i) i Finset.inter_subset_right).replace
      (L (meet S k i) k Finset.inter_subset_left).delete
      (A (meet S k i) k (meet_lt_left S h))
      (sets S k) (by ext f; simp [sets, meet]) (edges S old k)
      (by
        intro f hf
        by_cases hn : f ∈ (meet S k i).val <;>
          simpa [sets, edges, hn] using
            (L (meet S k i) k Finset.inter_subset_left).delete_edge f hf)
      (hA (meet S k i) k (meet_lt_left S h)) he c

/-- The full product homomorphism is assembled in the manuscript's order. -/
noncomputable def hom (k : Proper S) : (old k).Carrier →*
    DirectRecord.Product D (sets S) (groups S old) (edges S old) (involutions S old) :=
  DirectRecord.coordinateHom D (sets S) (groups S old) (edges S old)
    (involutions S old) k (groupHom D S old L k) (compatibleAction D S old L A k)

include hA in
theorem hom_edge (k : Proper S) (e : E) (he : e ∈ k.val) :
    hom D S old L A k ((old k).edge e) =
      DirectRecord.letter D (sets S) (groups S old) (edges S old) (involutions S old) e :=
  DirectRecord.coordinateHom_generator D (sets S) (groups S old) (edges S old)
    (involutions S old) k (groupHom D S old L k) (compatibleAction D S old L A k)
    (by
      intro i f hf
      by_cases hi : f ∈ i.val <;>
        simpa [sets, edges, hi] using groupHom_edge D S old L k i f hf)
    (compatibleAction_edge D S old L A hA k) e he

noncomputable def inclusion (k : Proper S) : (old k).Carrier →* (data D S old).Carrier :=
  DirectRecord.inclusion D (sets S) (groups S old) (edges S old) (involutions S old)
    k (hom D S old L A k) (hom_edge D S old L A hA k)
    (S : Set E) k.property.1 (old k).generated

theorem inclusion_edge (k : Proper S) (e : E) (he : e ∈ k.val) :
    inclusion D S old L A hA k ((old k).edge e) = (data D S old).edge e := by
  apply Subtype.ext
  change hom D S old L A k ((old k).edge e) =
    (DirectRecord.totalGenerator D (sets S) (groups S old)
      (edges S old) (involutions S old) (S : Set E) e).val
  rw [hom_edge D S old L A hA k e he,
    DirectRecord.totalGenerator_mem _ _ _ _ _ _ e (k.property.1 he)]
  rfl

/-- Property (II) for the new stage, with earlier premises supplied by L and A. -/
theorem inclusion_replace (k : Proper S) (u v : V) (g : (old k).Carrier)
    (p : D.WalkValue (S : Set E) (data D S old).edge u v
      (inclusion D S old L A hA k g)) :
    D.WalkValue (sets S k) (edges S old k) u v g := by
  obtain ⟨w, pw, hv⟩ := p.exists_word
  have hw := wordWalk_letters D pw
  have hval : DirectRecord.valuation D (sets S) (groups S old) (edges S old)
      (involutions S old) (S : Set E) w hw = inclusion D S old L A hA k g := by
    rw [DirectRecord.valuation_eq_product]
    exact hv
  exact DirectRecord.inclusion_replacement D (sets S) (groups S old)
    (edges S old) (involutions S old) k (hom D S old L A k)
    (hom_edge D S old L A hA k) (S : Set E) k.property.1 (old k).generated
    w hw pw g hval

/-- The complete new link; its deletion remains the literal first coordinate. -/
noncomputable def link (k : Proper S) : Link D (old k) (data D S old) where
  incl := inclusion D S old L A hA k
  incl_edge := inclusion_edge D S old L A hA k
  delete := projection D S old k
  delete_edge e he := by
    by_cases hm : e ∈ k.val <;> simpa [hm] using projection_edge D S old k e he
  replace := inclusion_replace D S old L A hA k

end Step

/-- An earlier component action exists because it is a coordinate of the actual record. -/
theorem family_coordinate_action (N M : Finset E) (hNM : N ⊂ M) :
    ∃ A : RightAction (family D M).Carrier
        (D.Component (N : Set E) (family D N).edge (fun e _ => (family D N).square e)),
      ∀ e ∈ M, ∀ c, A.act c ((family D M).edge e) =
        D.componentEdgePerm (N : Set E) (family D N).edge
          (fun e _ => (family D N).square e) e c := by
  rw [family_step D M]
  exact ⟨Step.action D M (fun i => family D i.val) ⟨N, hNM⟩,
    Step.action_edge D M (fun i => family D i.val) ⟨N, hNM⟩⟩

/-- Simultaneous existence of the manuscript's links for this particular family. -/
theorem family_links (S : Finset E) :
    ∀ M : Finset E, M ⊆ S → Nonempty (Link D (family D M) (family D S)) := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih M hMS
  by_cases heq : M = S
  · subst M
    exact ⟨Link.refl D S (family D S)⟩
  · have hM : M ⊂ S := lt_of_le_of_ne hMS heq
    let old : ∀ i : Proper S, Data E i.val := fun i => family D i.val
    let L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t) :=
      fun m t h => Classical.choice (ih t.val t.property m.val h)
    let A : ∀ n m : Proper S, n.val ⊂ m.val →
        RightAction (old m).Carrier (Step.components D S old n) :=
      fun n m h => Classical.choose (family_coordinate_action D n.val m.val h)
    have hA : ∀ (n m : Proper S) (h : n.val ⊂ m.val) e, e ∈ m.val → ∀ c,
        (A n m h).act c ((old m).edge e) =
          D.componentEdgePerm (Step.sets S n) (Step.edges S old n)
            (Step.involutions S old n) e c := by
      intro n m h
      exact Classical.choose_spec (family_coordinate_action D n.val m.val h)
    have hlink : Nonempty (Link D (family D M)
        (Step.data D S (fun i => family D i.val))) :=
      ⟨Step.link D S old L A hA ⟨M, hM⟩⟩
    rw [← family_step D S] at hlink
    exact hlink

end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
