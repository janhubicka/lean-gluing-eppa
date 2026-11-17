import GluingEPPA.Steiner.ChainValuation.LinkChain
import GluingEPPA.Steiner.ChainValuation.ChainIndexRelabel
import GluingEPPA.Steiner.ChainValuation.RangeRelabel

/-!
# Relabelling data for the actual LinkChain tests

Compatible old-stage group isomorphisms transport all proper block atoms
and the two inclusion maps from each actual intersection stage. These
commuting squares imply that the literal separated-triple predicate is
invariant. No test-space equivalence is postulated by this structure;
those are to be constructed from the block and pushout equivalences.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain

universe u
variable {V E V' E' : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']
variable (S : Finset E) (T : Finset E')
variable (old : ∀ i : Proper S, Data E i.val)
variable (old' : ∀ i : Proper T, Data E' i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))
variable (L' : ∀ m t : Proper T, m.val ⊆ t.val → Link D' (old' m) (old' t))

/-- Exactly the earlier group and Link isomorphisms used by the chain test
relabeling induction. These are to be supplied by the actual recursive
family's stage isomorphisms and generator-extensionality. -/
structure RelabelData (p : E ≃ E') where
  proper : Proper S ≃ Proper T
  stage : ∀ i : Proper S, (old i).Carrier ≃* (old' (proper i)).Carrier
  active : ∀ i e, e ∈ i.val ↔ p e ∈ (proper i).val
  edge : ∀ i e, e ∈ i.val →
    stage i ((old i).edge e) = (old' (proper i)).edge (p e)
  interface : ∀ i j : Proper S,
    (old (common S i j)).Carrier ≃*
      (old' (common T (proper i) (proper j))).Carrier
  leftComm : ∀ i j (k : (old (common S i j)).Carrier),
    stage i (left D S old L i j k) =
      left D' T old' L' (proper i) (proper j) (interface i j k)
  rightComm : ∀ i j (k : (old (common S i j)).Carrier),
    stage j (right D S old L i j k) =
      right D' T old' L' (proper i) (proper j) (interface i j k)

namespace RelabelData

variable {p : E ≃ E'}

/-- Transport an actual labelled Cayley block together with its group
coordinate. The shift coordinate is transformed by the corresponding old
stage group isomorphism. -/
noncomputable def atomEquiv (R : RelabelData D D' S T old old' L L' p) :
    Atom S old ≃ Atom T old' :=
  ChainValuation.atomRelabel R.proper (fun i => (R.stage i).toEquiv)

/-- Preservation of the exact separated-triple predicate follows from
the two commuting interface squares and reflects every disjointness
witness, not just the forward implication. -/
theorem tripleSeparated_iff (R : RelabelData D D' S T old old' L L' p)
    (x y z : Atom S old) :
    tripleSeparated D S old L x y z ↔
      tripleSeparated D' T old' L'
        ((atomEquiv D D' S T old old' L L' R) x) ((atomEquiv D D' S T old old' L L' R) y) ((atomEquiv D D' S T old old' L L' R) z) := by
  change Disjoint
      (ChainValuation.leftCoset (right D S old L x.1 y.1).range 1)
      (ChainValuation.leftCoset (left D S old L y.1 z.1).range y.2) ↔
    Disjoint
      (ChainValuation.leftCoset
        (right D' T old' L' (R.proper x.1) (R.proper y.1)).range 1)
      (ChainValuation.leftCoset
        (left D' T old' L' (R.proper y.1) (R.proper z.1)).range
          (R.stage y.1 y.2))
  exact ChainValuation.disjoint_interface_cosets_relabel_iff
    (R.stage y.1)
    (R.interface x.1 y.1) (R.interface y.1 z.1)
    (right D S old L x.1 y.1) (left D S old L y.1 z.1)
    (right D' T old' L' (R.proper x.1) (R.proper y.1))
    (left D' T old' L' (R.proper y.1) (R.proper z.1))
    (R.rightComm x.1 y.1) (R.leftComm y.1 z.1) y.2

end RelabelData
end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain
