import GluingEPPA.Steiner.FiniteInduction
import GluingEPPA.Steiner.MaskGenerated

/-!
# Unconditional finite exact transport

The group and its deletion maps are the concrete recursive construction.
Walk replacement is proved for that construction, not an external premise.
-/

namespace GluingEPPA.Steiner.FiniteFamily

universe u
variable {V E : Type u} [Fintype E] [DecidableEq E] [Finite V]
attribute [local instance] Classical.propDecidable

abbrev FullGroup (D : EdgeGraph V E) := (family D (Finset.univ : Finset E)).Carrier

noncomputable def fullEdge (D : EdgeGraph V E) : E → FullGroup D :=
  (family D Finset.univ).edge

theorem fullGeneration (D : EdgeGraph V E) (g : FullGroup D) :
    ∃ w : List E, wordValue (fullEdge D) w = g := by
  obtain ⟨w, hw⟩ := (family D (Finset.univ : Finset E)).generated g
  refine ⟨w.map Subtype.val, ?_⟩
  simpa only [wordValue, List.map_map, Function.comp_def, fullEdge] using hw

def belowUniv (R : Set E) : R.toFinset ⊆ (Finset.univ : Finset E) :=
  Finset.subset_univ _

noncomputable def project (D : EdgeGraph V E) (R : Set E) : FullGroup D →* FullGroup D :=
  (inclusion D R.toFinset Finset.univ (belowUniv R)).comp
    (retraction D R.toFinset Finset.univ (belowUniv R))

theorem project_edge (D : EdgeGraph V E) (R : Set E) (e : E) :
    project D R (fullEdge D e) = if e ∈ R then fullEdge D e else 1 := by
  change inclusion D R.toFinset Finset.univ (belowUniv R)
    (retraction D R.toFinset Finset.univ (belowUniv R) ((family D Finset.univ).edge e)) = _
  rw [Good.retAll_edge D Finset.univ (good D Finset.univ) R.toFinset
    (belowUniv R) e (Finset.mem_univ e)]
  by_cases he : e ∈ R
  · have hs : e ∈ R.toFinset := by simpa using he
    rw [ite_eq_left hs, ite_eq_left he]
    exact Good.incAll_edge D Finset.univ (good D Finset.univ)
      R.toFinset (belowUniv R) e hs
  · have hs : e ∉ R.toFinset := by simpa using he
    simp only [ite_eq_right hs, ite_eq_right he, map_one]

noncomputable def deletions (D : EdgeGraph V E) : DeletionSystem E (FullGroup D) where
  edge := fullEdge D
  project := project D
  on_edge := project_edge D
  project_inter := project_inter_of_generation (fullEdge D) (fullGeneration D)
    (project D) (project_edge D)

/-- A fixed value of the concrete deletion map has a representing walk in
that subset, with the original endpoints and the full original group value. -/
theorem replaceFixed (D : EdgeGraph V E) (R : Set E) (u v : V) (g : FullGroup D)
    (p : D.WalkValue Set.univ (fullEdge D) u v g)
    (hg : project D R g = g) : D.WalkValue R (fullEdge D) u v g := by
  let S := R.toFinset
  let i := inclusion D S Finset.univ (belowUniv R)
  let r := retraction D S Finset.univ (belowUniv R)
  have hval : i (r g) = g := hg
  have p' : D.WalkValue (↑(Finset.univ : Finset E) : Set E)
      (family D Finset.univ).edge u v (i (r g)) := by
    simpa only [Finset.coe_univ, hval, fullEdge] using p
  have q := replaceWalk D S Finset.univ (belowUniv R) u v (r g) p'
  have hRS : (↑S : Set E) ⊆ R := by
    intro e he
    simpa [S] using he
  have hab : ∀ e ∈ (↑S : Set E), i ((family D S).edge e) = fullEdge D e := by
    intro e he
    exact Good.incAll_edge D Finset.univ (good D Finset.univ) S (belowUniv R) e he
  have q' := q.mapOn (b := fullEdge D) i hRS hab
  simpa only [hval] using q'

/-- The general finite same-value common-walk theorem. There is no older
family, compatibility, or replacement premise in this statement. -/
theorem exactTransport (D : EdgeGraph V E) (M N : Set E) (u v : V) (g : FullGroup D) :
    D.WalkValue (M ∩ N) (fullEdge D) u v g ↔
      D.WalkValue M (fullEdge D) u v g ∧ D.WalkValue N (fullEdge D) u v g :=
  (deletions D).exact_transport_iff D (replaceFixed D) M N u v g

/-- An identity-valued walk cannot connect distinct graph vertices. -/
theorem value_one_endpoints (D : EdgeGraph V E) (u v : V)
    (p : D.WalkValue Set.univ (fullEdge D) u v 1) : u = v := by
  have q := replaceFixed D (∅ : Set E) u v 1 p (map_one (project D ∅))
  cases q with
  | nil => rfl
  | cons he hj hq => exact False.elim he

/-- A loop-free graph edge never receives the identity. This rules out
vacuous satisfaction of transport by collapsing all graph vertices. -/
theorem fullEdge_ne_one (D : EdgeGraph V E) (e : E) : fullEdge D e ≠ 1 := by
  intro he
  have p : D.WalkValue Set.univ (fullEdge D) (D.source e) (D.target e) (fullEdge D e) :=
    EdgeGraph.WalkValue.single (Set.mem_univ e) (D.joins_endpoints e)
  have q : D.WalkValue Set.univ (fullEdge D) (D.source e) (D.target e) 1 := by
    simpa only [he] using p
  exact D.loopless e (value_one_endpoints D (D.source e) (D.target e) q)

theorem fullGroup_finite (D : EdgeGraph V E) : Finite (FullGroup D) := inferInstance

theorem fullEdge_involutive (D : EdgeGraph V E) (e : E) :
    fullEdge D e * fullEdge D e = 1 := (family D Finset.univ).involutive e

end GluingEPPA.Steiner.FiniteFamily
