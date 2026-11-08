import GluingEPPA.Steiner.ChainValuation.RestrictedCosetChart
import GluingEPPA.Steiner.ChainValuation.MatchingMap

/-!
# Edge-reflecting bijective charts preserve completed matching actions

The final restricted-chain normalization must preserve *every* named
letter action, including fixed points at vertices with no genuine edge
of that colour. For a bijective chart, it is enough to establish that
genuine labelled edges are preserved AND reflected. The exact
edge-reflection equivalence automatically gives the missing
edge-lifting property, hence intertwines completed involutions
and all words in the relevant alphabet.

This is the action-theoretic final step of a normalized chart once
its geometric bijectivity and genuine-edge reflection are established.
It does not assert that the global normalized chain chart exists.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {X : Type u} {Y : Type v} {E : Type w}

/-- Bijective reflection of genuine edges is sufficient to
intertwine the completed involutions, including fixed points. -/
theorem matchingEquiv_perm
    (M : Matching X) (N : Matching Y) (f : X ≃ Y)
    (hrel : ∀ x y, M.Rel x y ↔ N.Rel (f x) (f y))
    (x : X) :
    f (M.perm x) = N.perm (f x) := by
  apply matchingMap_perm M N f
  · intro a b hab
    exact (hrel a b).mp hab
  · intro a z hz
    refine ⟨f.symm z, ?_, f.apply_symm_apply z⟩
    apply (hrel a (f.symm z)).mpr
    simpa using hz

/-- A bijection reflecting the genuine edges for every selected letter
intertwines every *whole word* in the smaller mask, not merely its
evaluation at a preferred vertex. -/
theorem matchingEquiv_word_onMask
    (S : Finset E) (M : E → Matching X) (N : E → Matching Y)
    (f : X ≃ Y)
    (hrel : ∀ e ∈ S, ∀ x y, (M e).Rel x y ↔
      (N e).Rel (f x) (f y))
    (w : List E) (hw : ∀ e ∈ w, e ∈ S) (x : X) :
    f (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (M e).perm) w x) =
      EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (N e).perm) w (f x) := by
  apply matchingMap_word_onMask S M N f
  · intro e he a b hab
    exact (hrel e he a b).mp hab
  · intro e he a z hz
    refine ⟨f.symm z, ?_, f.apply_symm_apply z⟩
    apply (hrel e he a (f.symm z)).mpr
    simpa using hz
  · exact hw

end GluingEPPA.Steiner.ChainValuation
