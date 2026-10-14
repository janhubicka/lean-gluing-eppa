import GluingEPPA.Sparsening.AtlasEndpoint

/-! One Boolean coordinate per unordered pair of DISTINCT charts.
Endpoint representatives are irrelevant: incidence is equality of unordered
pairs. The induced edge permutations satisfy identity and composition. -/
namespace GluingEPPA.Sparsening.CompleteChartGraph
universe u
variable {V : Type u}

abbrev Edge (V : Type u) :=
  {e : Sym2 V // ∃ a b : V, a ≠ b ∧ e = s(a, b)}

noncomputable def graph (V : Type u) : EdgeGraph V (Edge V) where
  left e := e.val.out.1
  right e := e.val.out.2

theorem inc_iff (e : Edge V) (a b : V) :
    (graph V).Inc e a b ↔ e.val = s(a, b) := by
  have h : e.val = s(e.val.out.1, e.val.out.2) := e.val.out_eq.symm
  change ((a = e.val.out.1 ∧ b = e.val.out.2) ∨
    (a = e.val.out.2 ∧ b = e.val.out.1)) ↔ e.val = s(a, b)
  conv_rhs => rw [h, Sym2.eq_iff]
  tauto

def edge (a b : V) (h : a ≠ b) : Edge V := ⟨s(a, b), a, b, h, rfl⟩

theorem complete (a b : V) (h : a ≠ b) : ∃ e, (graph V).Inc e a b :=
  ⟨edge a b h, (inc_iff _ a b).mpr rfl⟩

theorem loopless (e : Edge V) (a : V) : ¬ (graph V).Inc e a a := by
  intro h
  obtain ⟨b, c, hbc, he⟩ := e.property
  have hh := Sym2.eq_iff.mp (he.symm.trans ((inc_iff e a a).mp h))
  rcases hh with ⟨hb, hc⟩ | ⟨hb, hc⟩ <;> exact hbc (hb.trans hc.symm)

def image (h : V ≃ V) (e : Edge V) : Edge V :=
  ⟨Sym2.map h e.val, by
    obtain ⟨a, b, hab, he⟩ := e.property
    refine ⟨h a, h b, fun hh => hab (h.injective hh), ?_⟩
    rw [he, Sym2.map_mk]⟩

def perm (h : V ≃ V) : Edge V ≃ Edge V where
  toFun := image h
  invFun := image h.symm
  left_inv e := by
    apply Subtype.ext
    change Sym2.map h.symm (Sym2.map h e.val) = e.val
    induction e.val using Sym2.inductionOn with
    | _ a b => simp only [Sym2.map_mk, Equiv.symm_apply_apply]
  right_inv e := by
    apply Subtype.ext
    change Sym2.map h (Sym2.map h.symm e.val) = e.val
    induction e.val using Sym2.inductionOn with
    | _ a b => simp only [Sym2.map_mk, Equiv.apply_symm_apply]

theorem perm_inc (h : V ≃ V) (e : Edge V) (a b : V) :
    (graph V).Inc (perm h e) (h a) (h b) ↔ (graph V).Inc e a b := by
  rw [inc_iff, inc_iff]
  change Sym2.map h e.val = s(h a, h b) ↔ e.val = s(a, b)
  rw [← Sym2.map_mk]
  exact ⟨fun he => Sym2.map.injective h.injective he, congrArg (Sym2.map h)⟩

@[simp] theorem perm_refl : perm (Equiv.refl V) = Equiv.refl (Edge V) := by
  apply Equiv.ext
  intro e
  apply Subtype.ext
  change Sym2.map (Equiv.refl V) e.val = e.val
  induction e.val using Sym2.inductionOn with
  | _ a b => rfl

@[simp] theorem perm_trans (h g : V ≃ V) :
    perm (h.trans g) = (perm h).trans (perm g) := by
  apply Equiv.ext
  intro e
  apply Subtype.ext
  change Sym2.map (h.trans g) e.val = Sym2.map g (Sym2.map h e.val)
  induction e.val using Sym2.inductionOn with
  | _ a b => rfl

instance [Finite V] : Finite (Edge V) := inferInstance
end GluingEPPA.Sparsening.CompleteChartGraph
