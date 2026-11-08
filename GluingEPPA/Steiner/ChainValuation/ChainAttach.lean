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
variable (A B : GroupBlock E) (C : ChainState E A)
variable (h : A.Carrier)
variable (left : K →* A.Carrier) (right : K →* B.Carrier)
variable (hleft : Function.Injective left) (hright : Function.Injective right)

def exitSet : Set A.Carrier :=
  Set.range (fun k : K => h * left k)

abbrev ExtendedSpace :=
  ChainExtend C.lastEmbed C.lastInjective h left hleft right hright

def oldEmbed : C.Space → ExtendedSpace A B C h left right hleft hright :=
  pushoutInl (attachInto C.lastEmbed h left) right
    (attachInto_injective C.lastEmbed C.lastInjective h left hleft) hright

def newEmbed : B.Carrier → ExtendedSpace A B C h left right hleft hright :=
  pushoutInr (attachInto C.lastEmbed h left) right
    (attachInto_injective C.lastEmbed C.lastInjective h left hleft) hright

theorem oldEmbed_injective :
    Function.Injective (oldEmbed A B C h left right hleft hright) :=
  pushoutInl_injective _ _ _ _

theorem newEmbed_injective :
    Function.Injective (newEmbed A B C h left right hleft hright) :=
  pushoutInr_injective _ _ _ _

theorem oldEmbed_eq_newEmbed_iff (x : C.Space) (y : B.Carrier) :
    oldEmbed A B C h left right hleft hright x =
        newEmbed A B C h left right hleft hright y ↔
      ∃ k : K, C.lastEmbed (h * left k) = x ∧ right k = y :=
  chainExtend_overlap_iff C.lastEmbed C.lastInjective h left hleft
    right hright x y

def extendedEdgeRel (e : E)
    (x y : ExtendedSpace A B C h left right hleft hright) : Prop :=
  (∃ u v, (C.matching e).Rel u v ∧
      oldEmbed A B C h left right hleft hright u = x ∧
      oldEmbed A B C h left right hleft hright v = y) ∨
  (∃ g, e ∈ B.active ∧
      newEmbed A B C h left right hleft hright g = x ∧
      newEmbed A B C h left right hleft hright (g * B.edge e) = y)

theorem cross_endpoint
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    {e : E} {u v : C.Space} {g : B.Carrier}
    (hold : (C.matching e).Rel u v)
    (hnew : e ∈ B.active)
    (hsource :
      oldEmbed A B C h left right hleft hright u =
        newEmbed A B C h left right hleft hright g) :
    oldEmbed A B C h left right hleft hright v =
      newEmbed A B C h left right hleft hright (g * B.edge e) := by
  obtain ⟨k, hu, hg⟩ :=
    (oldEmbed_eq_newEmbed_iff A B C h left right hleft hright u g).1 hsource
  subst u
  subst g
  by_cases heold : e ∈ A.active
  · have hlast := C.last_active e heold (h * left k)
    have hv :
        v = C.lastEmbed ((h * left k) * A.edge e) :=
      (C.matching e).unique hold hlast
    rw [hv]
    obtain ⟨ke, hkeL, hkeR⟩ := hshared e heold hnew
    have hatt := pushout_attachment
      (attachInto C.lastEmbed h left) right
      (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
      hright (k * ke)
    change oldEmbed A B C h left right hleft hright
        (C.lastEmbed (h * left (k * ke))) =
      newEmbed A B C h left right hleft hright (right (k * ke)) at hatt
    convert hatt using 1 <;>
      simp only [map_mul, hkeL, hkeR, mul_assoc]
  · have hexit : h * left k ∈ exitSet A h left := ⟨k, rfl⟩
    have hnotentry : h * left k ∉ C.entry := by
      intro hentry
      exact Set.disjoint_left.1 hsep hentry hexit
    exact False.elim ((C.last_external e heold (h * left k) hnotentry)
      ⟨v, hold⟩)

def extendedMatching
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (e : E) :
    Matching (ExtendedSpace A B C h left right hleft hright) where
  Rel := extendedEdgeRel A B C h left right hleft hright e
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
          oldEmbed_injective A B C h left right hleft hright (hu₁.trans hu₂.symm)
        subst u₂
        have hv : v₁ = v₂ := (C.matching e).unique hu₁v₁ hu₂v₂
        rw [← hv₁, ← hv₂, hv]
      · rw [← hv₁, ← hg₂']
        exact cross_endpoint A B C h left right hleft hright hsep hshared
          hu₁v₁ he₂ (hu₁.trans hg₂.symm)
    · rcases hz with ⟨u₂, v₂, hu₂v₂, hu₂, hv₂⟩ | ⟨g₂, he₂, hg₂, hg₂'⟩
      · rw [← hg₁', ← hv₂]
        exact (cross_endpoint A B C h left right hleft hright hsep hshared
          hu₂v₂ he₁ (hu₂.trans hg₁.symm)).symm
      · have hg : g₁ = g₂ :=
          newEmbed_injective A B C h left right hleft hright
            (hg₁.trans hg₂.symm)
        subst g₂
        rw [← hg₁', ← hg₂']

noncomputable def extend
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e) :
    ChainState E B where
  Space := ExtendedSpace A B C h left right hleft hright
  finiteSpace := inferInstance
  lastEmbed := newEmbed A B C h left right hleft hright
  lastInjective := newEmbed_injective A B C h left right hleft hright
  entry := Set.range right
  matching := extendedMatching A B C h left right hleft hright hsep hshared
  last_active e he g := by
    apply Or.inr
    exact ⟨g, he, rfl, rfl⟩
  last_external e he g hg := by
    rintro ⟨y, hy⟩
    rcases hy with ⟨u, v, huv, hu, _⟩ | ⟨k, hek, hk, _⟩
    · obtain ⟨q, _, hq⟩ :=
        (oldEmbed_eq_newEmbed_iff A B C h left right hleft hright u g).1 hu
      exact hg ⟨q, hq⟩
    · exact he hek

/-- Every vertex of one extended chain comes from its previous chain or
from the new last block. This is the literal coverage statement needed to
construct equivariant covers of restricted chain components. -/
theorem extendedSpace_covered
    (q : ExtendedSpace A B C h left right hleft hright) :
    (∃ x : C.Space,
      oldEmbed A B C h left right hleft hright x = q) ∨
      (∃ y : B.Carrier,
      newEmbed A B C h left right hleft hright y = q) :=
  pushout_covered (attachInto C.lastEmbed h left) right
    (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
    hright q

end GluingEPPA.Steiner.ChainValuation
