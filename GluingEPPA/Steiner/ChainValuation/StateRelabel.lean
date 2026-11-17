import GluingEPPA.Steiner.ChainValuation.GroupBlockRelabel

/-!
# Equivariance interface for literal finite chain states

The group-coordinate equivalence preserves the current Cayley block;
the space equivalence reflects all genuine labelled edges.
Missing-edge fixed points then follow automatically.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E E' : Type u}

/-- Simultaneous equivalences of the current Cayley block and the
partly built literal chain, including exact edge reflection. -/
structure StateRelabel
    (p : E ≃ E')
    {A : GroupBlock.{u,v} E} {A' : GroupBlock.{u,v} E'}
    (F : A.Carrier ≃* A'.Carrier)
    (C : ChainState E A) (C' : ChainState E' A') where
  space : C.Space ≃ C'.Space
  lastEmbed : ∀ g : A.Carrier,
    space (C.lastEmbed g) = C'.lastEmbed (F g)
  entry : ∀ g : A.Carrier, g ∈ C.entry ↔ F g ∈ C'.entry
  matching : ∀ (e : E) (x y : C.Space),
    (C.matching e).Rel x y ↔
      (C'.matching (p e)).Rel (space x) (space y)

namespace StateRelabel

/-- At the initial one-block chain, relabelling is the old group
isomorphism itself. -/
noncomputable def initial
    (A : GroupBlock.{u,v} E) (A' : GroupBlock.{u,v} E')
    (p : E ≃ E') (F : A.Carrier ≃* A'.Carrier)
    (hActive : ∀ e, e ∈ A.active ↔ p e ∈ A'.active)
    (hEdge : ∀ e ∈ A.active, F (A.edge e) = A'.edge (p e)) :
    StateRelabel p F (ChainState.first A) (ChainState.first A') where
  space := F.toEquiv
  lastEmbed := by intro g; rfl
  entry := by intro g; simp [ChainState.first]
  matching := by
    intro e x y
    exact groupBlock_edgeRel_relabel_iff A A' p F hActive hEdge e x y

/-- Edge-reflecting chain-state equivalences conjugate every completed
letter action, including all isolated/fixed vertices. -/
theorem completed_perm
    (p : E ≃ E')
    {A : GroupBlock.{u,v} E} {A' : GroupBlock.{u,v} E'}
    (F : A.Carrier ≃* A'.Carrier)
    {C : ChainState E A} {C' : ChainState E' A'}
    (R : StateRelabel p F C C') (e : E) (x : C.Space) :
    R.space ((C.matching e).perm x) =
      (C'.matching (p e)).perm (R.space x) :=
  matching_perm_conjugate_of_rel_iff R.space
    (C.matching e) (C'.matching (p e)) (R.matching e) x

end StateRelabel
end GluingEPPA.Steiner.ChainValuation
