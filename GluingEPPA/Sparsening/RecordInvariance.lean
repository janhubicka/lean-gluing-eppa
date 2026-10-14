import GluingEPPA.Sparsening.StarCorrection

/-!
The records used in the separator theorem are invariant under genuine
Boolean transport paths. The converse (records determine the path class)
is a separate complete-support walk lemma; it is not assumed here.
-/
namespace GluingEPPA.Sparsening
universe u v
variable {V : Type u} {E : Type v}
variable (G : GluingEPPA.EdgeGraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma boundary_flip (chi : E → ZMod 2) (e : E) (v : V) :
    boundary G (GluingEPPA.EdgeGraph.flip chi e) v = boundary G chi v +
      ((if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0)) := by
  change boundary G (chi + edgeUnit e) v = _
  rw [boundary_add]
  simp [boundary, edgeUnit, ite_mul]

def charge (p : V × (E → ZMod 2)) : V → ZMod 2 :=
  fun v => boundary G p.2 v + (if p.1 = v then 1 else 0)

theorem charge_odd (p : V × (E → ZMod 2)) : (∑ v, charge G p v) = 1 := by
  simp [charge, Finset.sum_add_distrib, sum_boundary]

lemma charge_step {p q : V × (E → ZMod 2)} (h : G.LiftEdge p q) :
    charge G p = charge G q := by
  obtain ⟨e, he, hchi⟩ := h
  funext v
  change boundary G p.2 v + (if p.1 = v then 1 else 0) =
    boundary G q.2 v + (if q.1 = v then 1 else 0)
  rw [hchi, boundary_flip]
  have endpoints :
      (if G.left e = v then (1 : ZMod 2) else 0) +
        (if G.right e = v then 1 else 0) =
      (if p.1 = v then 1 else 0) + (if q.1 = v then 1 else 0) := by
    rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb, add_comm]
  rw [endpoints]
  calc
    boundary G p.2 v + (if p.1 = v then 1 else 0) =
      boundary G p.2 v + (if p.1 = v then 1 else 0) +
        ((if q.1 = v then 1 else 0) + (if q.1 = v then 1 else 0)) := by
          rw [bit_add_self, add_zero]
    _ = boundary G p.2 v + ((if p.1 = v then 1 else 0) +
        (if q.1 = v then 1 else 0)) + (if q.1 = v then 1 else 0) := by abel

theorem charge_path {p q : V × (E → ZMod 2)}
    (h : Relation.ReflTransGen G.LiftEdge p q) : charge G p = charge G q := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (charge_step G step)

/-- A coordinate external to a point's support cannot be traversed while
transporting that point, in either direction. -/
lemma exterior_step (allowed : V → Prop) (e : E)
    (outside : ¬ (allowed (G.left e) ∧ allowed (G.right e)))
    {p q : V × (E → ZMod 2)} (h : restrictedLift G allowed p q) : p.2 e = q.2 e := by
  obtain ⟨⟨d, hd, hchi⟩, hp, hq⟩ := h
  have hne : e ≠ d := by
    intro he
    subst d
    apply outside
    rcases hd with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨ha ▸ hp, hb ▸ hq⟩
    · exact ⟨hb ▸ hq, ha ▸ hp⟩
  rw [hchi]
  simp [GluingEPPA.EdgeGraph.flip, hne]

theorem exterior_path (allowed : V → Prop) (e : E)
    (outside : ¬ (allowed (G.left e) ∧ allowed (G.right e)))
    {p q : V × (E → ZMod 2)}
    (h : Relation.ReflTransGen (restrictedLift G allowed) p q) : p.2 e = q.2 e := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (exterior_step G allowed e outside step)

end GluingEPPA.Sparsening
