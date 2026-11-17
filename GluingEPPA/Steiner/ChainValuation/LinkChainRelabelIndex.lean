import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelData
import GluingEPPA.Steiner.ChainValuation.ChainTests
import Mathlib.Data.List.OfFn

/-!
# Naturality of the literal separated-chain finite index

The proper-stage relabelling sends the full list of actual chain atoms to
another genuine separated list. The raw finite tuples are relabelled with
the same length. It follows that the finite index set of *all* bounded
separated tests is equivalent to the target index set, without extra tests
or a reindexing by isomorphism classes.
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
variable {p : E ≃ E'}
namespace RelabelData

variable (R : RelabelData D D' S T old old' L L' p)

/-- Every finite list of actual consecutive block atoms preserves and
reflects the separated triple condition under relabelling. -/
theorem separatedList_relabel (atoms : List (Atom S old)) :
    separatedList D S old L atoms ↔
      separatedList D' T old' L' (atoms.map R.atomEquiv) := by
  induction atoms with
  | nil =>
      simp [separatedList]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [separatedList]
      | cons y ys =>
          cases ys with
          | nil =>
              simp [separatedList]
          | cons z zs =>
              change (tripleSeparated D S old L x y z ∧
                separatedList D S old L (y :: z :: zs)) ↔
                (tripleSeparated D' T old' L'
                  ((atomEquiv D D' S T old old' L L' R) x)
                  ((atomEquiv D D' S T old old' L L' R) y)
                  ((atomEquiv D D' S T old old' L L' R) z) ∧
                separatedList D' T old' L'
                  (((atomEquiv D D' S T old old' L L' R) y) ::
                    ((atomEquiv D D' S T old old' L L' R) z) ::
                    (zs.map R.atomEquiv)))
              exact and_congr (R.tripleSeparated_iff x y z) ih

/-- The raw positive-length test indices, with their literal finite
block tuples, relabel uniformly at every position. -/
noncomputable def rawRelabel
    (R : RelabelData D D' S T old old' L L' p) (N : Nat) :
    ChainValuation.RawChain N S old ≃ ChainValuation.RawChain N T old' :=
  ChainValuation.rawChainRelabel N R.proper (fun i => (R.stage i).toEquiv)

/-- Relabelling a raw chain produces precisely the pointwise transformed
list of block atoms, including the unused last shift. -/
theorem rawRelabel_list (N : Nat) (c : ChainValuation.RawChain N S old) :
    List.ofFn ((R.rawRelabel N) c).2 =
      (List.ofFn c.2).map R.atomEquiv := by
  change List.ofFn
      (fun i => (atomEquiv D D' S T old old' L L' R) (c.2 i)) =
    (List.ofFn c.2).map (atomEquiv D D' S T old old' L L' R)
  simpa only [Function.comp_def] using
    (List.map_ofFn (f := c.2)
      (g := atomEquiv D D' S T old old' L L' R)).symm

/-- The genuine separated tests, rather than arbitrary raw bounded
chains, are mapped bijectively under diagram-data relabelling. -/
theorem isSeparated_relabel (N : Nat)
    (c : ChainValuation.RawChain N S old) :
    IsSeparated D N S old L c ↔
      IsSeparated D' N T old' L' ((R.rawRelabel N) c) := by
  change separatedList D S old L (List.ofFn c.2) ↔
    separatedList D' T old' L' (List.ofFn ((R.rawRelabel N) c).2)
  rw [R.rawRelabel_list N c]
  exact R.separatedList_relabel (List.ofFn c.2)

/-- The complete finite index family of bounded separated-chain tests
is invariant under a compatible relabelling of preceding group/Link data. -/
noncomputable def chainIndexEquiv
    (R : RelabelData D D' S T old old' L L' p) (N : Nat) :
    SeparatedChains D N S old L ≃ SeparatedChains D' N T old' L' :=
  (R.rawRelabel N).subtypeEquiv (R.isSeparated_relabel N)

end RelabelData
end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain
