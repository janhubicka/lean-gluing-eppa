import GluingEPPA.Steiner.WordHomomorphism

/-!
# Relabelling the literal direct record, one stage at a time

Every old-group coordinate and every old-component permutation coordinate
is compared explicitly. Component conjugacy applies to arbitrary words.
Thus equality of source records implies equality of renamed target records;
no equality-preservation premise about the new stage is assumed.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

attribute [local instance] Classical.propDecidable

universe u
variable {V E V' E' G H : Type u}

theorem restricted_value_map [Group G] [Group H] (p : E ≃ E')
    (M : Set E) (N : Set E') (a : E → G) (b : E' → H) (F : G ≃* H)
    (hMN : ∀ e, p e ∈ N ↔ e ∈ M)
    (hF : ∀ e ∈ M, F (a e) = b (p e)) (w : List E) :
    F (((DirectRecord.restrictWord M w).map a).prod) =
      ((DirectRecord.restrictWord N (w.map p)).map b).prod := by
  induction w with
  | nil => simp [DirectRecord.restrictWord]
  | cons e w ih =>
      by_cases he : e ∈ M
      · have he' := (hMN e).2 he
        simpa [DirectRecord.restrictWord, he, he', hF e he] using
          congrArg (fun z => b (p e) * z) ih
      · have he' : p e ∉ N := fun h => he ((hMN e).1 h)
        simpa [DirectRecord.restrictWord, he, he'] using ih

namespace RecursiveRecord.Step

variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)

/-- Equality in the actual image group is equality of its defining word records. -/
theorem word_values_eq_iff (p q : List E)
    (hp : ∀ e ∈ p, e ∈ S) (hq : ∀ e ∈ q, e ∈ S) :
    (p.map (data D S old).edge).prod = (q.map (data D S old).edge).prod ↔
      DirectRecord.value D (sets S) (groups S old) (edges S old) (involutions S old) p =
        DirectRecord.value D (sets S) (groups S old) (edges S old) (involutions S old) q := by
  have hP := DirectRecord.totalGenerator_product D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E) p hp
  have hQ := DirectRecord.totalGenerator_product D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E) q hq
  constructor
  · intro h
    have hv := congrArg (fun g : (data D S old).Carrier => g.val) h
    exact hP.symm.trans (hv.trans hQ)
  · intro h
    apply Subtype.ext
    exact hP.trans (h.trans hQ.symm)

variable (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']
variable (f : Iso D D') (S' : Finset E') (old' : ∀ j : Proper S', Data E' j.val)
variable (hSS : ∀ e, f.edge e ∈ S' ↔ e ∈ S)

/-- Each target coordinate is the relabelling of an actual source coordinate.
The only supplied isomorphisms are for proper subsets. -/
include hSS in
theorem preserves_word_equalities
    (earlier : ∀ j : Proper S', ∃ i : Proper S,
      ∃ F : (old i).Carrier ≃* (old' j).Carrier,
        (∀ e, f.edge e ∈ j.val ↔ e ∈ i.val) ∧
        (∀ e ∈ i.val, F ((old i).edge e) = (old' j).edge (f.edge e)))
    (p q : List E) (hp : ∀ e ∈ p, e ∈ S) (hq : ∀ e ∈ q, e ∈ S)
    (hpq : (p.map (data D S old).edge).prod = (q.map (data D S old).edge).prod) :
    (p.map (fun e => (data D' S' old').edge (f.edge e))).prod =
      (q.map (fun e => (data D' S' old').edge (f.edge e))).prod := by
  have hval := (word_values_eq_iff D S old p q hp hq).1 hpq
  have hp' : ∀ e ∈ p.map f.edge, e ∈ S' := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact (hSS d).2 (hp d hd)
  have hq' : ∀ e ∈ q.map f.edge, e ∈ S' := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact (hSS d).2 (hq d hd)
  have htarget : ((p.map f.edge).map (data D' S' old').edge).prod =
      ((q.map f.edge).map (data D' S' old').edge).prod := by
    apply (word_values_eq_iff D' S' old' (p.map f.edge) (q.map f.edge) hp' hq').2
    funext j
    obtain ⟨i, F, hmem, hgen⟩ := earlier j
    apply Prod.ext
    · have hg := congrArg (fun r => (r i).1) hval
      change ((DirectRecord.restrictWord (i.val : Set E) p).map (old i).edge).prod =
        ((DirectRecord.restrictWord (i.val : Set E) q).map (old i).edge).prod at hg
      change ((DirectRecord.restrictWord (j.val : Set E') (p.map f.edge)).map
          (old' j).edge).prod =
        ((DirectRecord.restrictWord (j.val : Set E') (q.map f.edge)).map
          (old' j).edge).prod
      rw [← restricted_value_map f.edge (i.val : Set E) (j.val : Set E')
        (old i).edge (old' j).edge F hmem hgen p,
        ← restricted_value_map f.edge (i.val : Set E) (j.val : Set E')
        (old i).edge (old' j).edge F hmem hgen q, hg]
    · apply MulOpposite.unop_injective
      change D'.componentWordPerm (sets S' j) (edges S' old' j)
          (involutions S' old' j) (p.map f.edge) =
        D'.componentWordPerm (sets S' j) (edges S' old' j)
          (involutions S' old' j) (q.map f.edge)
      ext c'
      let Q := Iso.componentEquiv f (sets S i) (sets S' j)
        (edges S old i) (edges S' old' j) F hmem hgen
        (involutions S old i) (involutions S' old' j)
      obtain ⟨c, rfl⟩ := Q.surjective c'
      have htau : D.componentWordPerm (sets S i) (edges S old i)
          (involutions S old i) p =
        D.componentWordPerm (sets S i) (edges S old i) (involutions S old i) q :=
          congrArg (fun r => MulOpposite.unop ((r i).2)) hval
      calc
        D'.componentWordPerm (sets S' j) (edges S' old' j)
            (involutions S' old' j) (p.map f.edge) (Q c) =
          Q (D.componentWordPerm (sets S i) (edges S old i) (involutions S old i) p c) :=
            (Iso.componentEquiv_wordPerm f (sets S i) (sets S' j)
              (edges S old i) (edges S' old' j) F hmem hgen
              (involutions S old i) (involutions S' old' j) p c).symm
        _ = Q (D.componentWordPerm (sets S i) (edges S old i)
            (involutions S old i) q c) := congrArg (fun r => Q (r c)) htau
        _ = D'.componentWordPerm (sets S' j) (edges S' old' j)
            (involutions S' old' j) (q.map f.edge) (Q c) :=
          Iso.componentEquiv_wordPerm f (sets S i) (sets S' j)
            (edges S old i) (edges S' old' j) F hmem hgen
            (involutions S old i) (involutions S' old' j) q c
  simpa only [List.map_map, Function.comp_def] using htarget

end RecursiveRecord.Step
end EdgeGraph
end GluingEPPA.Steiner
