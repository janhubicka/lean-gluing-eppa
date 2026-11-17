import GluingEPPA.Steiner.ChainValuation.StateRelabelExtension

/-!
# Separation is natural under chain-state relabelling

A commuting square for the attachment-interface subgroup carries the exit
set of the last Cayley block exactly onto the target exit set. Together
with the entry-set equivalence in StateRelabel this transports the
disjointness condition in both directions. The target separation proof
can therefore be derived rather than supplied independently.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E E' : Type u} {K K' : Type v}
variable [Group K] [Group K']

/-- The image of an actual exit attachment under a group equivalence
is the corresponding exit attachment of the relabelled group. -/
theorem exitSet_relabel_iff
    (A : GroupBlock.{u,v} E) (A' : GroupBlock.{u,v} E')
    (FA : A.Carrier ≃* A'.Carrier) (FK : K ≃* K')
    (h : A.Carrier) (h' : A'.Carrier)
    (left : K →* A.Carrier) (left' : K' →* A'.Carrier)
    (hH : FA h = h')
    (hL : ∀ k, FA (left k) = left' (FK k))
    (g : A.Carrier) :
    g ∈ exitSet A h left ↔ FA g ∈ exitSet A' h' left' := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨FK k, ?_⟩
    have hs : FA (h * left k) = h' * left' (FK k) := by
      rw [map_mul, hH, hL]
    exact hs.symm.trans (congrArg FA hk)
  · rintro ⟨k', hk'⟩
    obtain ⟨k, rfl⟩ := FK.surjective k'
    refine ⟨k, FA.injective ?_⟩
    have hs : FA (h * left k) = h' * left' (FK k) := by
      rw [map_mul, hH, hL]
    exact hs.trans hk'

namespace StateRelabel

/-- Entry/exit disjointness for the next chain block is preserved and
reflected by a genuine chain-state equivalence. -/
theorem entry_exit_disjoint_iff
    (p : E ≃ E')
    (A : GroupBlock.{u,v} E) (A' : GroupBlock.{u,v} E')
    (C : ChainState E A) (C' : ChainState E' A')
    (FA : A.Carrier ≃* A'.Carrier)
    (R : StateRelabel p FA C C') (FK : K ≃* K')
    (h : A.Carrier) (h' : A'.Carrier)
    (left : K →* A.Carrier) (left' : K' →* A'.Carrier)
    (hH : FA h = h')
    (hL : ∀ k, FA (left k) = left' (FK k)) :
    Disjoint C.entry (exitSet A h left) ↔
      Disjoint C'.entry (exitSet A' h' left') := by
  constructor
  · intro hd
    apply Set.disjoint_left.mpr
    intro y hyEntry hyExit
    obtain ⟨g, rfl⟩ := FA.surjective y
    exact (Set.disjoint_left.mp hd)
      ((R.entry g).mpr hyEntry)
      ((exitSet_relabel_iff A A' FA FK h h' left left' hH hL g).mpr hyExit)
  · intro hd
    apply Set.disjoint_left.mpr
    intro g hgEntry hgExit
    exact (Set.disjoint_left.mp hd)
      ((R.entry g).mp hgEntry)
      ((exitSet_relabel_iff A A' FA FK h h' left left' hH hL g).mp hgExit)

/-- The target separation condition of one attachment is a consequence
of source separation: no second geometric premise is needed. -/
noncomputable def extension_from_source
    (p : E ≃ E')
    (A B : GroupBlock.{u,v} E)
    (A' B' : GroupBlock.{u,v} E')
    (C : ChainState E A) (C' : ChainState E' A')
    (FA : A.Carrier ≃* A'.Carrier)
    (FB : B.Carrier ≃* B'.Carrier)
    (R : StateRelabel p FA C C')
    (FK : K ≃* K')
    (h : A.Carrier) (h' : A'.Carrier)
    (hH : FA h = h')
    (left : K →* A.Carrier) (right : K →* B.Carrier)
    (left' : K' →* A'.Carrier) (right' : K' →* B'.Carrier)
    (hL : ∀ k, FA (left k) = left' (FK k))
    (hR : ∀ k, FB (right k) = right' (FK k))
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hleft' : Function.Injective left') (hright' : Function.Injective right')
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (hshared' : ∀ e, e ∈ A'.active → e ∈ B'.active →
      ∃ k : K', left' k = A'.edge e ∧ right' k = B'.edge e)
    (hActiveB : ∀ e, e ∈ B.active ↔ p e ∈ B'.active)
    (hEdgeB : ∀ e ∈ B.active, FB (B.edge e) = B'.edge (p e)) :
    StateRelabel p FB
      (ChainValuation.extend A B C h left right
        hleft hright hsep hshared)
      (ChainValuation.extend A' B' C' h' left' right'
        hleft' hright'
        ((entry_exit_disjoint_iff p A A' C C' FA R FK
          h h' left left' hH hL).mp hsep) hshared') :=
  extension p A B A' B' C C' FA FB R FK h h' hH
    left right left' right' hL hR hleft hright hleft' hright'
    hsep
    ((entry_exit_disjoint_iff p A A' C C' FA R FK
      h h' left left' hH hL).mp hsep)
    hshared hshared' hActiveB hEdgeB

end StateRelabel
end GluingEPPA.Steiner.ChainValuation
