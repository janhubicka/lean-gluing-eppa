import GluingEPPA.Steiner.DiagramFullDomainExtension

/-!
# Identity and composition of the actual initial Steiner diagram action

The abstract quotient relabelling formula is already checked. For a
coherent EPPA family we also need the *concrete* ambient-label action
sigma -> inputSymmetry P sigma to preserve identity and composition.

The proof is extensional: the action on semantic sites and the named
inclusion edges already composes, and all remaining structure fields
are proofs of relational compatibility.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {A : Type u} [Fintype A] [DecidableEq A]

/-- Edge-graph isomorphisms are determined by their maps on
vertices and named edges. -/
private theorem graph_iso_ext {V E : Type u} (D : EdgeGraph V E)
    (f g : Iso D D)
    (hv : f.vertex = g.vertex) (he : f.edge = g.edge) : f = g := by
  cases f with
  | mk fv fe fp =>
      cases g with
      | mk gv ge gp =>
          dsimp at hv he
          cases hv
          cases he
          rfl

/-- The graph action of the identity permutation is the identity. -/
theorem graphRelabel_id (R : A → A → A → Prop) :
    graphRelabel R (Equiv.refl A) = Iso.refl (graph R) := by
  apply graph_iso_ext (graph R)
  · apply Equiv.ext
    intro s
    exact Site.relabel_refl R s
  · apply Equiv.ext
    intro e
    exact edgeRelabel_refl R e

/-- Graph relabellings compose on *actual* semantic vertices and
named edges, not merely on their presentations as pairs. -/
theorem graphRelabel_comp (R : A → A → A → Prop)
    (σ τ : Equiv.Perm A) :
    graphRelabel R (σ.trans τ) =
      (graphRelabel R σ).trans (graphRelabel R τ) := by
  apply graph_iso_ext (graph R)
  · apply Equiv.ext
    intro s
    change Site.relabel R (σ.trans τ) s =
      Site.relabel R τ (Site.relabel R σ s)
    exact (Site.relabel_trans R σ τ s).symm
  · apply Equiv.ext
    intro e
    change edgeRelabel R (σ.trans τ) e =
      edgeRelabel R τ (edgeRelabel R σ e)
    exact (edgeRelabel_trans R σ τ e).symm

/-- The extra local-system, triple and overlap fields of a compatible
relabelling are propositions; hence its graph and label maps determine it. -/
private theorem labelled_symmetry_ext (P : Input A)
    (f g : LabelledSymmetry (graph P.triple) (localDiagram P))
    (hgraph : f.graph = g.graph) (hlabels : f.labels = g.labels) :
    f = g := by
  cases f with
  | mk fg fl fp ft fo =>
      cases g with
      | mk gg gl gp gt go =>
          dsimp at hgraph hlabels
          cases hgraph
          cases hlabels
          rfl

/-- Ambient label permutations act identically on the concrete
Steiner diagram when they are the identity. -/
theorem inputSymmetry_id (P : Input A) :
    inputSymmetry P (Equiv.refl A) =
      LabelledSymmetry.id (graph P.triple) (localDiagram P) := by
  apply labelled_symmetry_ext P
  · exact graphRelabel_id P.triple
  · rfl

/-- The concrete initial Steiner diagram realizes the permutation
group action exactly. This is the remaining relabelling-composition
hypothesis of the final coherent extension formula. -/
theorem inputSymmetry_comp (P : Input A) (σ τ : Equiv.Perm A) :
    inputSymmetry P (σ.trans τ) =
      LabelledSymmetry.trans (graph P.triple) (localDiagram P)
        (inputSymmetry P σ) (inputSymmetry P τ) := by
  apply labelled_symmetry_ext P
  · exact graphRelabel_comp P.triple σ τ
  · rfl

end GluingEPPA.Steiner.InitialSites
