import GluingEPPA.Steiner.DiagramInputAction

/-!
# A coherent family of automorphisms of the actual finite Steiner quotient

For each closed subset U of the input, choose its distinguished root
edge as prefix (or the identity when U is all of A). This choice
depends on U, not on a particular partial automorphism.

Completing each partial bijection by the increasing bijection of
complements produces a compatible permutation of the input labels.
The relabelling action on the *actual* initial Steiner diagram is
functorial, and the two middle root-prefix involutions cancel.
Consequently the extensions compose **before** we assume that the
partial bijections preserve the input Steiner triples.

The separate pointwise proper/full lemmas establish extension on
embedded points when the partial bijection is a Steiner isomorphism.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u
variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]
variable (P : Input A)
variable [Fintype (Edge P.triple)] [DecidableEq (Edge P.triple)]

/-- The source or target prefix from Section 6. A full subsystem
uses the identity instead of a nonexistent root loop. -/
noncomputable def domainPrefix (U : Finset A)
    (hU : Closed P.triple (U : Set A)) :
    (family (graph P.triple) Finset.univ).Carrier :=
  if h : (U : Set A) = Set.univ then 1 else
    (family (graph P.triple) Finset.univ).edge
      (rootEdge P.triple (U : Set A) hU h)

/-- Each chosen prefix is an involution, including the full case. -/
theorem domainPrefix_square (U : Finset A)
    (hU : Closed P.triple (U : Set A)) :
    domainPrefix P U hU * domainPrefix P U hU = 1 := by
  unfold domainPrefix
  split_ifs with h
  · simp
  · exact family_square (graph P.triple) Finset.univ
      (rootEdge P.triple (U : Set A) hU h)

/-- The concrete three-factor map for a partial bijection between
closed subsets; preservation of triples is needed only to show
it extends the original partial automorphism, not to define it. -/
noncomputable def coherentExtension (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W}) :
    Equiv.Perm
      (realizedPoint (graph P.triple) (localDiagram P)) :=
  extensionMap (graph P.triple) (localDiagram P)
    (domainPrefix P U hU) (domainPrefix P W hW)
    (inputSymmetry P (OrderedCompletion.totalCompletion U W f))

/-- Identity restrictions have identity extensions. -/
theorem coherentExtension_id (U : Finset A)
    (hU : Closed P.triple (U : Set A)) :
    coherentExtension P U U hU hU
        (Equiv.refl {x : A // x ∈ U}) =
      Equiv.refl (realizedPoint (graph P.triple) (localDiagram P)) := by
  unfold coherentExtension
  rw [OrderedCompletion.totalCompletion_id]
  rw [inputSymmetry_id]
  exact extensionMap_id (graph P.triple) (localDiagram P)
    (domainPrefix P U hU) (domainPrefix_square P U hU)

/-- Coherence of the chosen extensions: exact composition, with
no commutation assumption between the prefix maps and relabellings. -/
theorem coherentExtension_comp
    (U W T : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (hT : Closed P.triple (T : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (g : {x : A // x ∈ W} ≃ {x : A // x ∈ T}) :
    (coherentExtension P U W hU hW f).trans
      (coherentExtension P W T hW hT g) =
    coherentExtension P U T hU hT (f.trans g) := by
  unfold coherentExtension
  rw [extensionMap_comp (graph P.triple) (localDiagram P)
    (domainPrefix P U hU) (domainPrefix P W hW)
    (domainPrefix P T hT)
    (inputSymmetry P (OrderedCompletion.totalCompletion U W f))
    (inputSymmetry P (OrderedCompletion.totalCompletion W T g))
    (domainPrefix_square P W hW)]
  rw [← inputSymmetry_comp P
    (OrderedCompletion.totalCompletion U W f)
    (OrderedCompletion.totalCompletion W T g)]
  rw [OrderedCompletion.totalCompletion_trans]

end GluingEPPA.Steiner.InitialSites
