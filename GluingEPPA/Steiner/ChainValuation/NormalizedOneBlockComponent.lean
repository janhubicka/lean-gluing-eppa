import GluingEPPA.Steiner.ChainValuation.NormalizedProperMaskReindex
import GluingEPPA.Steiner.ChainValuation.LinkCosetEquiv
import GluingEPPA.Steiner.ChainValuation.LinkLastCoset
import GluingEPPA.Steiner.ChainValuation.ReachComponentWords

/-!
# Base case of the genuine proper-M finite-chain normal form

If M is not contained in the alphabet A of one original earlier
Cayley block, its M-component is a left coset of the literal
K_(M intersect A). The normalized mask is a proper subset of M.

The exact coset equivalence is upgraded to an equivalence with the
WHOLE genuine labelled M-component of the old block, together with
two-way edge reflection and exact compatibility with the
completed action of every word over M.

This is the single-block base case of the remaining proper-mask
interval induction. It does not postulate a global group K_S or
a replacement chain, and does not yet assemble multiple blocks.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- A genuine proper-M earlier group is equivalent to a complete
M-reachable component in the old original Cayley group K_A. -/
noncomputable def normalizedOneBlock_equiv
    (M A : Proper S) (hproper : ¬ M.val ⊆ A.val)
    (g : (old A).Carrier) :
    (smallerOld S old M (normalizedProperMask S M A hproper)).Carrier ≃
      MatchingReachComponent (block S old A).matching M.val g := by
  change (old (Step.meet S M A)).Carrier ≃
      MatchingReachComponent (block S old A).matching M.val g
  let F := restrictedBlock_cosetEquiv D S old L M A g
  let G :
      {y : (old A).Carrier //
        y ∈ leftCoset (restrictedSubgroup D S old L M A) g} →
      MatchingReachComponent (block S old A).matching M.val g :=
    fun y => ⟨y.val,
      (restricted_block_reach_iff_coset D S old L M A g y.val).mpr
        y.property⟩
  have hInjective : Function.Injective G := by
    intro x y hxy
    -- An equality after the embedding G reflects the underlying point.
    apply Subtype.val_injective
    exact congrArg Subtype.val hxy
  have hSurjective : Function.Surjective G := by
    intro y
    refine ⟨⟨y.val,
      (restricted_block_reach_iff_coset
        D S old L M A g y.val).mp y.property⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact F.trans (Equiv.ofBijective G ⟨hInjective, hSurjective⟩)

/-- The normalized chart uses the genuine previous Link inclusion,
left-translated by g, without changing any point coordinates. -/
theorem normalizedOneBlock_equiv_val
    (M A : Proper S) (hproper : ¬ M.val ⊆ A.val)
    (g : (old A).Carrier)
    (x : (smallerOld S old M (normalizedProperMask S M A hproper)).Carrier) :
    ((normalizedOneBlock_equiv D S old L M A hproper g) x).val =
      ((restrictedBlock_cosetEquiv D S old L M A g x).val) := by
  rfl

/-- For any e in M, the smaller earlier Cayley graph has
exactly the actual e-edges of the original reachable M-component,
including absent letters which have no genuine edges. -/
theorem normalizedOneBlock_edge_iff
    (M A : Proper S) (hproper : ¬ M.val ⊆ A.val)
    (g : (old A).Carrier)
    (e : E) (he : e ∈ M.val)
    (x y : (smallerOld S old M
      (normalizedProperMask S M A hproper)).Carrier) :
    ((block S old (Step.meet S M A)).matching e).Rel x y ↔
      ((block S old A).matching e).Rel
        ((normalizedOneBlock_equiv D S old L M A hproper g) x).val
        ((normalizedOneBlock_equiv D S old L M A hproper g) y).val := by
  rw [normalizedOneBlock_equiv_val D S old L M A hproper g x,
      normalizedOneBlock_equiv_val D S old L M A hproper g y]
  exact restrictedBlock_cosetEquiv_edge_iff
    D S old L M A g e he x y

/-- The completed action of every M-word is conjugate under
the literal smaller-stage chart, including fixed-point completion. -/
theorem normalizedOneBlock_word_val
    (M A : Proper S) (hproper : ¬ M.val ⊆ A.val)
    (g : (old A).Carrier)
    (word : List E) (hw : ∀ e ∈ word, e ∈ M.val)
    (x : (smallerOld S old M
      (normalizedProperMask S M A hproper)).Carrier) :
    ((normalizedOneBlock_equiv D S old L M A hproper g)
      (matchingWordApply
        (fun e => (block S old (Step.meet S M A)).matching e)
        word x)).val =
    matchingWordApply (block S old A).matching word
      ((normalizedOneBlock_equiv D S old L M A hproper g) x).val := by
  exact componentChart_word_perm_val
    (block S old A).matching M.val g
    (fun e => (block S old (Step.meet S M A)).matching e)
    (normalizedOneBlock_equiv D S old L M A hproper g)
    (fun e he x y =>
      normalizedOneBlock_edge_iff D S old L M A hproper g e he x y)
    word hw x

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
