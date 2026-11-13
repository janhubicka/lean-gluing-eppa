import GluingEPPA.Steiner.RecursiveLinks

/-!
# Coherent subset maps and exact intersections for the literal record family

The maps below come from the current manuscript's recursive family, not an
abstract group-existence premise. Their generator rules force the coherence
of successive inclusions/deletions. The final corollary concerns actual
Cayley-lift endpoints and retains the ambient group when restricting edges.
Naturality under graph isomorphisms and the Steiner realization are separate.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} (D : EdgeGraph V E)
variable [Finite V] [Fintype E] [DecidableEq E]

noncomputable def familyLink (M S : Finset E) (hMS : M ⊆ S) :
    Link D (family D M) (family D S) := Classical.choice (family_links D S M hMS)

noncomputable def inclusion (M S : Finset E) (hMS : M ⊆ S) :
    (family D M).Carrier →* (family D S).Carrier := (familyLink D M S hMS).incl

noncomputable def deletion (M S : Finset E) (hMS : M ⊆ S) :
    (family D S).Carrier →* (family D M).Carrier := (familyLink D M S hMS).delete

theorem inclusion_edge (M S : Finset E) (hMS : M ⊆ S) (e : E) (he : e ∈ M) :
    inclusion D M S hMS ((family D M).edge e) = (family D S).edge e :=
  (familyLink D M S hMS).incl_edge e he

theorem deletion_edge (M S : Finset E) (hMS : M ⊆ S) (e : E) (he : e ∈ S) :
    deletion D M S hMS ((family D S).edge e) =
      if e ∈ M then (family D M).edge e else 1 := by
  by_cases hm : e ∈ M <;> simpa [deletion, hm] using (familyLink D M S hMS).delete_edge e he

theorem retraction (M S : Finset E) (hMS : M ⊆ S) :
    (deletion D M S hMS).comp (inclusion D M S hMS) = MonoidHom.id _ :=
  Link.left_inverse D (family D M) (family D S) hMS (familyLink D M S hMS)

theorem inclusion_injective (M S : Finset E) (hMS : M ⊆ S) :
    Function.Injective (inclusion D M S hMS) :=
  Link.injective D (family D M) (family D S) hMS (familyLink D M S hMS)

theorem inclusion_comp (N M S : Finset E) (hNM : N ⊆ M) (hMS : M ⊆ S) :
    (inclusion D M S hMS).comp (inclusion D N M hNM) =
      inclusion D N S (fun e he => hMS (hNM he)) := by
  apply (family D N).hom_ext
  intro e he
  change inclusion D M S hMS (inclusion D N M hNM ((family D N).edge e)) = _
  rw [inclusion_edge D N M hNM e he, inclusion_edge D M S hMS e (hNM he),
    inclusion_edge D N S _ e he]

theorem deletion_comp (N M S : Finset E) (hNM : N ⊆ M) (hMS : M ⊆ S) :
    (deletion D N M hNM).comp (deletion D M S hMS) =
      deletion D N S (fun e he => hMS (hNM he)) := by
  apply (family D S).hom_ext
  intro e he
  change deletion D N M hNM (deletion D M S hMS ((family D S).edge e)) = _
  rw [deletion_edge D M S hMS e he, deletion_edge D N S _ e he]
  by_cases hm : e ∈ M
  · rw [if_pos hm, deletion_edge D N M hNM e hm]
  · have hn : e ∉ N := fun h => hm (hNM h)
    rw [if_neg hm, if_neg hn, map_one]

/-- The unconditional exact replacement statement for the constructed inclusions. -/
theorem replacement (M S : Finset E) (hMS : M ⊆ S) (u v : V)
    (g : (family D M).Carrier)
    (p : D.WalkValue (S : Set E) (family D S).edge u v (inclusion D M S hMS g)) :
    D.WalkValue (M : Set E) (family D M).edge u v g :=
  (familyLink D M S hMS).replace u v g p

/-- Inclusion preserves the values of genuine smaller walks. -/
theorem map_walk (M S : Finset E) (hMS : M ⊆ S) {u v : V}
    {g : (family D M).Carrier}
    (p : D.WalkValue (M : Set E) (family D M).edge u v g) :
    D.WalkValue (M : Set E) (family D S).edge u v (inclusion D M S hMS g) := by
  induction p with
  | nil v => simpa using (WalkValue.nil (D := D) (S := (M : Set E))
      (a := (family D S).edge) v)
  | @cons u v w e g he hj p ih =>
      simpa only [map_mul, inclusion_edge D M S hMS e he] using
        (WalkValue.cons he hj ih)

noncomputable def projector (M : Finset E) :
    (family D Finset.univ).Carrier →* (family D Finset.univ).Carrier :=
  (inclusion D M Finset.univ (Finset.subset_univ M)).comp
    (deletion D M Finset.univ (Finset.subset_univ M))

theorem projector_edge (M : Finset E) (e : E) :
    projector D M ((family D Finset.univ).edge e) =
      if e ∈ M then (family D Finset.univ).edge e else 1 := by
  change inclusion D M Finset.univ _ (deletion D M Finset.univ _
    ((family D Finset.univ).edge e)) = _
  rw [deletion_edge D M Finset.univ _ e (Finset.mem_univ e)]
  by_cases he : e ∈ M
  · simp only [if_pos he, inclusion_edge D M Finset.univ _ e he]
  · simp only [if_neg he, map_one]

/-- The commuting-projector argument of the current Corollary 4.4. -/
theorem projector_inter (M N : Finset E) :
    (projector D M).comp (projector D N) = projector D (M ∩ N) := by
  apply (family D Finset.univ).hom_ext
  intro e _he
  change projector D M (projector D N ((family D Finset.univ).edge e)) = _
  rw [projector_edge, projector_edge]
  by_cases hn : e ∈ N
  · rw [if_pos hn, projector_edge]
    by_cases hm : e ∈ M <;> simp [hm, hn]
  · rw [if_neg hn, map_one]
    simp [hn]

/-- A restricted walk's value is fixed by the matching deletion projector. -/
theorem walk_projector (M : Finset E) {u v : V}
    {g : (family D Finset.univ).Carrier}
    (p : D.WalkValue (M : Set E) (family D Finset.univ).edge u v g) :
    projector D M g = g := by
  induction p with
  | nil => exact map_one _
  | @cons u v w e k he hj p ih =>
      have heM : e ∈ M := he
      rw [map_mul, projector_edge]
      simp only [if_pos heM, ih]

/-- The replacement walk has exactly the original two lifted endpoints. -/
theorem exact_intersection_walk (M N : Finset E) (u v : V)
    (g h : (family D Finset.univ).Carrier)
    (p : D.CayleyWalk (M : Set E) (family D Finset.univ).edge u g v h)
    (q : D.CayleyWalk (N : Set E) (family D Finset.univ).edge u g v h) :
    D.CayleyWalk ((M ∩ N : Finset E) : Set E) (family D Finset.univ).edge u g v h := by
  have hp := walk_projector D M p.value
  have hq := walk_projector D N q.value
  have hf : projector D (M ∩ N) (g⁻¹ * h) = g⁻¹ * h := by
    have hc := DFunLike.congr_fun (projector_inter D M N) (g⁻¹ * h)
    change projector D M (projector D N (g⁻¹ * h)) = _ at hc
    rw [hq, hp] at hc
    exact hc.symm
  let k := deletion D (M ∩ N) Finset.univ (Finset.subset_univ _) (g⁻¹ * h)
  have hk : inclusion D (M ∩ N) Finset.univ (Finset.subset_univ _) k = g⁻¹ * h := hf
  have base := p.value.mono (show (M : Set E) ⊆ ((Finset.univ : Finset E) : Set E) from
    fun _ _ => Finset.mem_univ _)
  rw [← hk] at base
  have small := replacement D (M ∩ N) Finset.univ (Finset.subset_univ _)
    u v k base
  have full := map_walk D (M ∩ N) Finset.univ (Finset.subset_univ _) small
  rw [hk] at full
  exact (D.cayleyWalk_iff_value _ _ u v g h).2 full

/-- Exact intersections of components in the actual final lift, not in a quotient. -/
theorem component_intersection (M N : Finset E)
    (z : V × (family D Finset.univ).Carrier) :
    D.componentSet (M : Set E) (family D Finset.univ).edge z ∩
        D.componentSet (N : Set E) (family D Finset.univ).edge z =
      D.componentSet ((M ∩ N : Finset E) : Set E) (family D Finset.univ).edge z := by
  ext y
  change (D.CayleyWalk (M : Set E) (family D Finset.univ).edge z.1 z.2 y.1 y.2 ∧
      D.CayleyWalk (N : Set E) (family D Finset.univ).edge z.1 z.2 y.1 y.2) ↔
    D.CayleyWalk ((M ∩ N : Finset E) : Set E)
      (family D Finset.univ).edge z.1 z.2 y.1 y.2
  constructor
  · rintro ⟨hp, hq⟩
    exact exact_intersection_walk D M N z.1 y.1 z.2 y.2 hp hq
  · intro hp
    exact ⟨hp.mono (fun _ he => (Finset.mem_inter.mp he).1),
      hp.mono (fun _ he => (Finset.mem_inter.mp he).2)⟩

end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
