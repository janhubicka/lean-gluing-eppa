import GluingEPPA.Steiner.DiagramExactProperties

/-!
# Natural word actions for the actual recursively constructed diagrams

The recursive group is the permutation diagram Q_S: its vertices are
the actions of words and its labelled edges append a letter. This
module states equivariance directly on those vertex actions for any
isomorphism of loopless edge-labelled base graphs.

The graph isomorphism may reverse the two endpoints of each named
undirected edge independently. The induced map preserves transitions
and actual lifted walks. Identity and composition of the underlying
family isomorphisms are supplied by naturalIso_refl and naturalIso_comp
from RecursiveNaturality.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {V E V' E' : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']

/-- Diagram naturality in right word-action notation: relabelling a
valuation vertex commutes with following any word of named edges. -/
theorem diagram_word_action_naturality
    (f : Iso D D') (S : Finset E) (T : Finset E')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S)
    (w : List E) (g : (family D S).Carrier) :
    naturalIso D D' f S T hST (wordPermutation D S w g) =
      wordPermutation D' T (w.map f.edge)
        (naturalIso D D' f S T hST g) := by
  have hw :
      naturalIso D D' f S T hST (wordValue D S w) =
        wordValue D' T (w.map f.edge) := by
    simpa only [wordValue, List.map_map, Function.comp_def] using
      (naturalIso_word D D' f S T hST w)
  change naturalIso D D' f S T hST (g * wordValue D S w) =
      naturalIso D D' f S T hST g *
        wordValue D' T (w.map f.edge)
  rw [map_mul, hw]

/-- The same relabelling of valuation vertices preserves and reflects
actual lifted walks, with *both* lifted endpoints fixed. -/
theorem diagram_lift_walk_naturality
    (f : Iso D D') (S : Finset E) (T : Finset E')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S)
    (M : Set E) (N : Set E') (hMN : ∀ e, f.edge e ∈ N ↔ e ∈ M)
    (u v : V) (g h : (family D S).Carrier) :
    D.CayleyWalk M (family D S).edge u g v h ↔
      D'.CayleyWalk N (family D' T).edge
        (f.vertex u) (naturalIso D D' f S T hST g)
        (f.vertex v) (naturalIso D D' f S T hST h) := by
  exact (naturalIso_cayleyWalk_iff D D' f S T hST
    M N hMN u v g h).symm

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
