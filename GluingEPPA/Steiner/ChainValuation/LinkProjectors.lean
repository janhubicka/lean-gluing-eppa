import GluingEPPA.Steiner.RecursiveLinks

/-!
# Commuting deletion/inclusion projectors in an earlier finite family

The masks in one chain block come from previously constructed stages. The
already available Link interface implies that their subgroup projections
commute and intersect exactly on the common mask. This is independent of
the chain-augmented stage currently being constructed.
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

/-- The canonical inclusion maps of the earlier stages compose, by
uniqueness on their named generators. -/
theorem inclusion_comp (a b c : Proper S)
    (hab : a.val ⊆ b.val) (hbc : b.val ⊆ c.val) :
    (L b c hbc).incl.comp (L a b hab).incl =
      (L a c (fun e he => hbc (hab he))).incl := by
  apply (old a).hom_ext
  intro e he
  change (L b c hbc).incl ((L a b hab).incl ((old a).edge e)) =
    (L a c _).incl ((old a).edge e)
  rw [(L a b hab).incl_edge e he,
    (L b c hbc).incl_edge e (hab he),
    (L a c _).incl_edge e he]

/-- The split idempotent projector on a smaller-mask subgroup. -/
def projector (m t : Proper S) (hmt : m.val ⊆ t.val) :
    (old t).Carrier →* (old t).Carrier :=
  (L m t hmt).incl.comp (L m t hmt).delete

theorem projector_edge (m t : Proper S) (hmt : m.val ⊆ t.val)
    (e : E) (he : e ∈ t.val) :
    projector D S old L m t hmt ((old t).edge e) =
      if e ∈ m.val then (old t).edge e else 1 := by
  change (L m t hmt).incl ((L m t hmt).delete ((old t).edge e)) = _
  rw [(L m t hmt).delete_edge e he]
  by_cases hm : e ∈ m.val
  · rw [if_pos hm, (L m t hmt).incl_edge e hm]
  · simp only [if_neg hm, map_one]

/-- The image of inclusion is precisely the fixed-point subgroup of the
corresponding deletion/inclusion projector. -/
theorem mem_range_iff_projector (m t : Proper S)
    (hmt : m.val ⊆ t.val) (g : (old t).Carrier) :
    g ∈ (L m t hmt).incl.range ↔
      projector D S old L m t hmt g = g := by
  constructor
  · rintro ⟨x, rfl⟩
    have h := DFunLike.congr_fun
      (Link.left_inverse D (old m) (old t) hmt (L m t hmt)) x
    change (L m t hmt).delete ((L m t hmt).incl x) = x at h
    change (L m t hmt).incl ((L m t hmt).delete ((L m t hmt).incl x)) =
      (L m t hmt).incl x
    rw [h]
  · intro h
    refine ⟨(L m t hmt).delete g, ?_⟩
    exact h

/-- These projectors commute; their product is the projector onto the
intersection mask. -/
theorem projector_inter (n m t : Proper S)
    (hnt : n.val ⊆ t.val) (hmt : m.val ⊆ t.val) :
    (projector D S old L n t hnt).comp
        (projector D S old L m t hmt) =
      projector D S old L (Step.meet S n m) t
        (fun e he => hnt (Finset.mem_inter.mp he).1) := by
  apply (old t).hom_ext
  intro e he
  change projector D S old L n t hnt
      (projector D S old L m t hmt ((old t).edge e)) =
    projector D S old L (Step.meet S n m) t _
      ((old t).edge e)
  rw [projector_edge D S old L m t hmt e he,
      projector_edge D S old L (Step.meet S n m) t _ e he]
  by_cases hm : e ∈ m.val
  · rw [if_pos hm, projector_edge D S old L n t hnt e he]
    by_cases hn : e ∈ n.val
    · simp [hn, hm, Step.meet]
    · simp [hn, hm, Step.meet]
  · rw [if_neg hm, map_one]
    simp [hm, Step.meet]

/-- A smaller subgroup's range is contained in a larger one's range. -/
theorem range_mono (a b t : Proper S)
    (hab : a.val ⊆ b.val) (hbt : b.val ⊆ t.val) :
    (L a t (fun e he => hbt (hab he))).incl.range ≤
      (L b t hbt).incl.range := by
  rintro g ⟨x, rfl⟩
  refine ⟨(L a b hab).incl x, ?_⟩
  exact DFunLike.congr_fun
    (inclusion_comp D S old L a b t hab hbt) x

/-- The earlier stage's subgroup intersections are exactly intersections of
their allowed edge sets; this is derived from the links, not postulated. -/
theorem range_inter (n m t : Proper S)
    (hnt : n.val ⊆ t.val) (hmt : m.val ⊆ t.val) :
    (L n t hnt).incl.range ⊓ (L m t hmt).incl.range =
      (L (Step.meet S n m) t
        (fun e he => hnt (Finset.mem_inter.mp he).1)).incl.range := by
  let hmeet : (Step.meet S n m).val ⊆ t.val :=
    fun e he => hnt (Finset.mem_inter.mp he).1
  ext g
  constructor
  · rintro ⟨hn, hm⟩
    have hnfix := (mem_range_iff_projector D S old L n t hnt g).mp hn
    have hmfix := (mem_range_iff_projector D S old L m t hmt g).mp hm
    have hcomp := DFunLike.congr_fun
      (projector_inter D S old L n m t hnt hmt) g
    change projector D S old L n t hnt
      (projector D S old L m t hmt g) =
      projector D S old L (Step.meet S n m) t hmeet g at hcomp
    rw [hmfix, hnfix] at hcomp
    exact (mem_range_iff_projector D S old L
      (Step.meet S n m) t hmeet g).mpr hcomp.symm
  · intro h
    constructor
    · exact (range_mono D S old L
        (Step.meet S n m) n t Finset.inter_subset_left hnt) h
    · exact (range_mono D S old L
        (Step.meet S n m) m t Finset.inter_subset_right hmt) h

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
