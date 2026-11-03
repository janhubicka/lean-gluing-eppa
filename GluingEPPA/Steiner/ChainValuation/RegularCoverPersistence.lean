import GluingEPPA.Steiner.ChainValuation.LastBlockRegularCover

/-!
# Regular smaller-mask cosets persist through later chain attachments

The last-block regular component lemma is not tied to the end of the
finished chain. Its genuine matching edges persist under each subsequent
injective pushout attachment. Thus any regular K_M coset in an earlier block
continues to cover its complete M-word component in the final chain.

The statement is one exact extension step, with the existing ChainState
and ChainAttach definitions. The induction over arbitrarily many
attachments may now reuse it unchanged.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {M : Finset E} {K : Type v} [Group K]
variable (A : EdgeGraph.RecursiveRecord.Data E M)
variable (B C : GroupBlock E) (D : ChainState E B)
variable (h : B.Carrier)
variable (left : K →* B.Carrier) (right : K →* C.Carrier)
variable (hleft : Function.Injective left) (hright : Function.Injective right)
variable (hsep : Disjoint D.entry (exitSet B h left))
variable (hshared : ∀ e, e ∈ B.active → e ∈ C.active →
  ∃ k : K, left k = B.edge e ∧ right k = C.edge e)
variable (f : A.Carrier → D.Space)
variable (hreal : ∀ e ∈ M, ∀ x : A.Carrier,
  (D.matching e).Rel (f x) (f (x * A.edge e)))

include hreal

/-- All genuine regular coset edges remain genuine edges in the enlarged
chain. This uses the actual quotient and its matching, not an invented
equivalence relation. -/
theorem regular_edges_survive_extension
    (e : E) (he : e ∈ M) (x : A.Carrier) :
    ((extend B C D h left right hleft hright hsep hshared).matching e).Rel
        (oldEmbed B C D h left right hleft hright (f x))
        (oldEmbed B C D h left right hleft hright
          (f (x * A.edge e))) := by
  exact old_edge_survives C B D h left right hleft hright
    hsep hshared e (hreal e he x)

/-- A regular coset's image under the old-block injection is exactly its
M-word component after one more attachment. No new M-points can appear
in that component. -/
theorem regular_cover_survives_extension
    (x : A.Carrier) :
    Set.range (fun a : A.Carrier =>
      oldEmbed B C D h left right hleft hright (f a)) =
      EdgeGraph.RecursiveRecord.ChainValuation.wordReach
        (fun e => ((extend B C D h left right hleft hright hsep hshared)
          .matching e).perm) (S := M)
        (oldEmbed B C D h left right hleft hright (f x)) := by
  let D' := extend B C D h left right hleft hright hsep hshared
  let f' : A.Carrier → D'.Space :=
    fun a => oldEmbed B C D h left right hleft hright (f a)
  have hletter : ∀ e ∈ M, ∀ a : A.Carrier,
      f' (a * A.edge e) = (D'.matching e).perm (f' a) := by
    intro e he a
    exact (D'.matching e).perm_eq_of_rel
      (regular_edges_survive_extension A B C D h left right hleft hright
        hsep hshared f hreal e he a) |>.symm
  exact EdgeGraph.RecursiveRecord.ChainValuation.regular_cover_is_component
    (fun e => (D'.matching e).perm) A f' hletter x

end GluingEPPA.Steiner.ChainValuation
