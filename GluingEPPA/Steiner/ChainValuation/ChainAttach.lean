import GluingEPPA.Steiner.ChainValuation.ChainState
import GluingEPPA.Steiner.ChainValuation.ChainExtend

/-!
# Attaching one separated Cayley block to a chain state

The new space is the exact injective pushout. Its labelled edge relation is
the union of old chain edges and new block edges. Internal separation is used
only in the cross-case: an exit-attachment point is outside the previous entry,
so an edge absent from the old last block cannot arrive from an earlier block.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]
variable (C : ChainState E) (B : GroupBlock E)
variable (h : C.last.Carrier)
variable (left : K →* C.last.Carrier) (right : K →* B.Carrier)
variable (hleft : Function.Injective left) (hright : Function.Injective right)

/-- The outgoing attachment inside the old last block. -/
def exitSet : Set C.last.Carrier :=
  Set.range (fun k : K => h * left k)

/-- The new chain space after one attachment. -/
abbrev ExtendedSpace :=
  ChainExtend C.lastEmbed C.lastInjective h left hleft right hright

def oldEmbed : C.Space → ExtendedSpace C B h left right hleft hright :=
  pushoutInl (attachInto C.lastEmbed h left) right
    (attachInto_injective C.lastEmbed C.lastInjective h left hleft) hright

def newEmbed : B.Carrier → ExtendedSpace C B h left right hleft hright :=
  pushoutInr (attachInto C.lastEmbed h left) right
    (attachInto_injective C.lastEmbed C.lastInjective h left hleft) hright

theorem oldEmbed_injective :
    Function.Injective (oldEmbed C B h left right hleft hright) :=
  pushoutInl_injective _ _ _ _

theorem newEmbed_injective :
    Function.Injective (newEmbed C B h left right hleft hright) :=
  pushoutInr_injective _ _ _ _

theorem oldEmbed_eq_newEmbed_iff (x : C.Space) (y : B.Carrier) :
    oldEmbed C B h left right hleft hright x =
        newEmbed C B h left right hleft hright y ↔
      ∃ k : K, C.lastEmbed (h * left k) = x ∧ right k = y :=
  chainExtend_overlap_iff C.lastEmbed C.lastInjective h left hleft
    right hright x y

/-- The union of the old global edge relation and the new block edge relation. -/
def extendedEdgeRel (e : E)
    (x y : ExtendedSpace C B h left right hleft hright) : Prop :=
  (∃ u v, (C.matching e).Rel u v ∧
      oldEmbed C B h left right hleft hright u = x ∧
      oldEmbed C B h left right hleft hright v = y) ∨
  (∃ g, e ∈ B.active ∧
      newEmbed C B h left right hleft hright g = x ∧
      newEmbed C B h left right hleft hright (g * B.edge e) = y)

/-- The endpoint agreement in the only nontrivial uniqueness case. -/
theorem cross_endpoint
    (hsep : Disjoint C.entry (exitSet C h left))
    (hshared : ∀ e, e ∈ C.last.active → e ∈ B.active →
      ∃ k : K, left k = C.last.edge e ∧ right k = B.edge e)
    {e : E} {u v : C.Space} {g : B.Carrier}
    (hold : (C.matching e).Rel u v)
    (hnew : e ∈ B.active)
    (hsource :
      oldEmbed C B h left right hleft hright u =
        newEmbed C B h left right hleft hright g) :
    oldEmbed C B h left right hleft hright v =
      newEmbed C B h left right hleft hright (g * B.edge e) := by
  obtain ⟨k, hu, hg⟩ :=
    (oldEmbed_eq_newEmbed_iff C B h left right hleft hright u g).1 hsource
  subst u
  subst g
  by_cases heold : e ∈ C.last.active
  · have hlast := C.last_active e heold (h * left k)
    have hv :
        v = C.lastEmbed ((h * left k) * C.last.edge e) :=
      (C.matching e).unique hold hlast
    rw [hv]
    obtain ⟨ke, hkeL, hkeR⟩ := hshared e heold hnew
    have hatt := pushout_attachment
      (attachInto C.lastEmbed h left) right
      (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
      hright (k * ke)
    change oldEmbed C B h left right hleft hright
        (C.lastEmbed (h * left (k * ke))) =
      newEmbed C B h left right hleft hright (right (k * ke)) at hatt
    convert hatt using 1 <;>
      simp only [map_mul, hkeL, hkeR, mul_assoc]
  · have hexit : h * left k ∈ exitSet C h left :=
      ⟨k, rfl⟩
    have hnotentry : h * left k ∉ C.entry := by
      intro hentry
      exact Set.disjoint_left.1 hsep hentry hexit
    exact False.elim ((C.last_external e heold (h * left k) hnotentry)
      ⟨v, hold⟩)

/-- The union edge relation is a matching. -/
def extendedMatching
    (hsep : Disjoint C.entry (exitSet C h left))
    (hshared : ∀ e, e ∈ C.last.active → e ∈ B.active →
      ∃ k : K, left k = C.last.edge e ∧ right k = B.edge e)
    (e : E) :
    Matching (ExtendedSpace C B h left right hleft hright) where
  Rel := extendedEdgeRel C B h left right hleft hright e
  symm := by
    rintro x y (⟨u, v, huv, rfl, rfl⟩ | ⟨g, he, rfl, rfl⟩)
    · exact Or.inl ⟨v, u, (C.matching e).symm huv, rfl, rfl⟩
    · refine Or.inr ⟨g * B.edge e, he, rfl, ?_⟩
      rw [mul_assoc, B.square e he, mul_one]
  unique := by
    rintro x y z hy hz
    rcases hy with ⟨u₁, v₁, hu₁v₁, hu₁, hv₁⟩ | ⟨g₁, he₁, hg₁, hg₁'⟩
    · rcases hz with ⟨u₂, v₂, hu₂v₂, hu₂, hv₂⟩ | ⟨g₂, he₂, hg₂, hg₂'⟩
      · have hu : u₁ = u₂ :=
          oldEmbed_injective C B h left right hleft hright (hu₁.trans hu₂.symm)
        subst u₂
        have hv : v₁ = v₂ := (C.matching e).unique hu₁v₁ hu₂v₂
        simpa [hv₁, hv₂, hv]
      · rw [← hv₁, ← hg₂']
        exact cross_endpoint C B h left right hleft hright hsep hshared
          hu₁v₁ he₂ (hu₁.trans hg₂.symm)
    · rcases hz with ⟨u₂, v₂, hu₂v₂, hu₂, hv₂⟩ | ⟨g₂, he₂, hg₂, hg₂'⟩
      · rw [← hg₁', ← hv₂]
        exact (cross_endpoint C B h left right hleft hright hsep hshared
          hu₂v₂ he₁ (hu₂.trans hg₁.symm)).symm
      · have hg : g₁ = g₂ :=
          newEmbed_injective C B h left right hleft hright
            (hg₁.trans hg₂.symm)
        subst g₂
        simpa [hg₁', hg₂']

/-- Attach one new block and retain the invariant needed for the next step. -/
noncomputable def extend
    (hsep : Disjoint C.entry (exitSet C h left))
    (hshared : ∀ e, e ∈ C.last.active → e ∈ B.active →
      ∃ k : K, left k = C.last.edge e ∧ right k = B.edge e) :
    ChainState E where
  Space := ExtendedSpace C B h left right hleft hright
  finiteSpace := inferInstance
  last := B
  lastEmbed := newEmbed C B h left right hleft hright
  lastInjective := newEmbed_injective C B h left right hleft hright
  entry := Set.range right
  matching := extendedMatching C B h left right hleft hright hsep hshared
  last_active e he g := by
    apply Or.inr
    exact ⟨g, he, rfl, rfl⟩
  last_external e he g hg := by
    rintro ⟨y, hy⟩
    rcases hy with ⟨u, v, huv, hu, _⟩ | ⟨k, hek, hk, _⟩
    · obtain ⟨q, _, hq⟩ :=
        (oldEmbed_eq_newEmbed_iff C B h left right hleft hright u g).1
          (hu.trans rfl)
      exact hg ⟨q, hq⟩
    · exact he hek

end GluingEPPA.Steiner.ChainValuation
