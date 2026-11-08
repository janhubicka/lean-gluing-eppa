import GluingEPPA.Steiner.DiagramRecords

/-!
# Direct intersection proof by deleting letters

This follows the diagram appendix rather than the projection-intersection
calculation in RecursiveTransport. Deleting letters gives an arbitrary word,
not necessarily an actual walk. The already established endpoint-replacement
property supplies the missing walk, with its original lifted endpoints.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} (D : EdgeGraph V E)
variable [Finite V] [Fintype E] [DecidableEq E]

/-- Inclusion preserves the value of each smaller word, not just single edges. -/
theorem wordValue_inclusion (M S : Finset E) (hMS : M ⊆ S)
    (w : List E) (hw : ∀ e ∈ w, e ∈ M) :
    inclusion D M S hMS (wordValue D M w) = wordValue D S w := by
  induction w with
  | nil => simp [wordValue]
  | cons e w ih =>
      have heM : e ∈ M := hw e (by simp)
      have hw' : ∀ f ∈ w, f ∈ M :=
        fun f hf => hw f (by simp [hf])
      change inclusion D M S hMS ((family D M).edge e * wordValue D M w) =
        (family D S).edge e * wordValue D S w
      rw [map_mul, inclusion_edge D M S hMS e heM, ih hw']

/-- Deleting letters and applying the deletion homomorphism agree. -/
theorem wordValue_deletion (M S : Finset E) (hMS : M ⊆ S)
    (w : List E) (hw : ∀ e ∈ w, e ∈ S) :
    deletion D M S hMS (wordValue D S w) =
      wordValue D M (DirectRecord.restrictWord (M : Set E) w) := by
  induction w with
  | nil => simp [wordValue, DirectRecord.restrictWord]
  | cons e w ih =>
      have heS : e ∈ S := hw e (by simp)
      have hw' : ∀ f ∈ w, f ∈ S :=
        fun f hf => hw f (by simp [hf])
      change deletion D M S hMS ((family D S).edge e * wordValue D S w) =
        wordValue D M (DirectRecord.restrictWord (M : Set E) (e :: w))
      rw [map_mul, deletion_edge D M S hMS e heS, ih hw']
      by_cases hm : e ∈ M
      · simp [DirectRecord.restrictWord, hm, wordValue]
      · simp [DirectRecord.restrictWord, hm, wordValue]

/-- Keeping only M-letters in an N-word yields an (M ∩ N)-word. -/
theorem restrictWord_mem_inter (M N : Finset E)
    (w : List E) (hw : ∀ e ∈ w, e ∈ N) :
    ∀ e ∈ DirectRecord.restrictWord (M : Set E) w, e ∈ M ∩ N := by
  intro e he
  have h : e ∈ w ∧ e ∈ M := by
    simpa [DirectRecord.restrictWord] using he
  exact Finset.mem_inter.mpr ⟨h.2, hw e h.1⟩

/-- Two words with a common full value admit an intersection word
    preserving that full value and the M-value of the first word. -/
theorem intersection_word (M N S : Finset E)
    (hMS : M ⊆ S) (hNS : N ⊆ S)
    (p q : List E) (hp : ∀ e ∈ p, e ∈ M)
    (hq : ∀ e ∈ q, e ∈ N)
    (hv : wordValue D S p = wordValue D S q) :
    ∃ w : List E,
      (∀ e ∈ w, e ∈ M ∩ N) ∧
      inclusion D (M ∩ N) M Finset.inter_subset_left
        (wordValue D (M ∩ N) w) = wordValue D M p ∧
      wordValue D S w = wordValue D S p := by
  let w := DirectRecord.restrictWord (M : Set E) q
  have hw : ∀ e ∈ w, e ∈ M ∩ N :=
    restrictWord_mem_inter M N q hq
  have hwM : ∀ e ∈ w, e ∈ M :=
    fun e he => (Finset.mem_inter.mp (hw e he)).1
  have hwS : ∀ e ∈ w, e ∈ S :=
    fun e he => hMS (hwM e he)
  have hpS : ∀ e ∈ p, e ∈ S :=
    fun e he => hMS (hp e he)
  have hqS : ∀ e ∈ q, e ∈ S :=
    fun e he => hNS (hq e he)
  have hd : wordValue D M p = wordValue D M w := by
    have ht := congrArg (deletion D M S hMS) hv
    rw [wordValue_deletion D M S hMS p hpS,
      DirectRecord.restrictWord_eq_of_letters (M : Set E) p hp,
      wordValue_deletion D M S hMS q hqS] at ht
    exact ht
  have hi : inclusion D (M ∩ N) M Finset.inter_subset_left
      (wordValue D (M ∩ N) w) = wordValue D M w :=
    wordValue_inclusion D (M ∩ N) M Finset.inter_subset_left w hw
  have hf : wordValue D S w = wordValue D S p := by
    calc
      wordValue D S w =
          inclusion D M S hMS (wordValue D M w) :=
        (wordValue_inclusion D M S hMS w hwM).symm
      _ = inclusion D M S hMS (wordValue D M p) := by rw [← hd]
      _ = wordValue D S p := wordValue_inclusion D M S hMS p hp
  exact ⟨w, hw, hi.trans hd.symm, hf⟩

/-- Exact lifted endpoints by direct word deletion and earlier repair,
    without commuting projectors or subgroup intersections. -/
theorem exact_intersection_walk_by_words (M N : Finset E)
    (u v : V) (g h : (family D Finset.univ).Carrier)
    (p : D.CayleyWalk (M : Set E) (family D Finset.univ).edge u g v h)
    (q : D.CayleyWalk (N : Set E) (family D Finset.univ).edge u g v h) :
    D.CayleyWalk ((M ∩ N : Finset E) : Set E)
      (family D Finset.univ).edge u g v h := by
  obtain ⟨wp, pWalk, hpVal⟩ := p.value.exists_word
  obtain ⟨wq, qWalk, hqVal⟩ := q.value.exists_word
  have hp := wordWalk_letters D pWalk
  have hq := wordWalk_letters D qWalk
  have hv : wordValue D Finset.univ wp = wordValue D Finset.univ wq :=
    hpVal.trans hqVal.symm
  obtain ⟨w, hw, hM, hS⟩ :=
    intersection_word D M N Finset.univ
      (Finset.subset_univ M) (Finset.subset_univ N) wp wq hp hq hv
  have pM : D.WalkValue (M : Set E) (family D M).edge u v
      (wordValue D M wp) :=
    WordWalk.value (D := D) (a := (family D M).edge) pWalk
  have pM' : D.WalkValue (M : Set E) (family D M).edge u v
      (inclusion D (M ∩ N) M Finset.inter_subset_left
        (wordValue D (M ∩ N) w)) := by
    rw [hM]
    exact pM
  have small := replacement D (M ∩ N) M Finset.inter_subset_left
    u v (wordValue D (M ∩ N) w) pM'
  have full := map_walk D (M ∩ N) Finset.univ (Finset.subset_univ _) small
  have hwFull : ∀ e ∈ w, e ∈ Finset.univ :=
    fun e _ => Finset.mem_univ e
  have hval : inclusion D (M ∩ N) Finset.univ (Finset.subset_univ _)
      (wordValue D (M ∩ N) w) = g⁻¹ * h := by
    calc
      inclusion D (M ∩ N) Finset.univ (Finset.subset_univ _)
          (wordValue D (M ∩ N) w) = wordValue D Finset.univ w :=
        wordValue_inclusion D (M ∩ N) Finset.univ
          (Finset.subset_univ _) w hw
      _ = wordValue D Finset.univ wp := hS
      _ = g⁻¹ * h := hpVal
  rw [hval] at full
  exact (D.cayleyWalk_iff_value _ _ u v g h).2 full

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
