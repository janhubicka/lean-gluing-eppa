import GluingEPPA.Steiner.ChainValuation.ActualNormalizedBoundary

/-!
# Separation survives normalized restricted block charts

An interior block of the manuscript's separated Link chain has
disjoint entry and exit cosets in the actual earlier group K_A.
Every normalized M-block is embedded by a left translation of
K_(M∩A) into K_A. Therefore the preimages of the original entry
and exit cosets under that chart are disjoint.

This isolates the separation condition that a full normalized
smaller-mask chain must preserve. The proof is independent of any
unconstructed top-stage group, and of a choice of representatives
beyond the chart translation.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The actual translated normalized chart for a restricted block. -/
noncomputable def normalizedBlockChart
    (M A : Proper S) (g : (old A).Carrier) :
    (old (Step.meet S M A)).Carrier → (old A).Carrier :=
  fun t =>
    g * (L (Step.meet S M A) A Finset.inter_subset_right).incl t

/-- Any two sets which map into the original disjoint entry/exit
cosets remain disjoint after pulling them back along the normalized
chart. This form is ready to use for the eventual recorded boundary
subsets of the smaller-mask block. -/
theorem normalizedBlock_separated_of_maps
    (M : Proper S) (x y z : Atom S old)
    (hsep : tripleSeparated D S old L x y z)
    (g : (old y.1).Carrier)
    (entry exit : Set (old (Step.meet S M y.1)).Carrier)
    (hentry : ∀ t ∈ entry,
      normalizedBlockChart D S old L M y.1 g t ∈
        leftCoset (right D S old L x.1 y.1).range 1)
    (hexit : ∀ t ∈ exit,
      normalizedBlockChart D S old L M y.1 g t ∈
        leftCoset (left D S old L y.1 z.1).range y.2) :
    Disjoint entry exit := by
  apply Set.disjoint_left.mpr
  intro t ht1 ht2
  exact (Set.disjoint_left.mp hsep)
    (hentry t ht1) (hexit t ht2)

/-- In particular, the exact preimages of the real entry and exit
sets under any normalized translated Cayley chart are disjoint. -/
theorem normalizedBlock_preimage_separated
    (M : Proper S) (x y z : Atom S old)
    (hsep : tripleSeparated D S old L x y z)
    (g : (old y.1).Carrier) :
    Disjoint
      {t : (old (Step.meet S M y.1)).Carrier |
        normalizedBlockChart D S old L M y.1 g t ∈
          leftCoset (right D S old L x.1 y.1).range 1}
      {t : (old (Step.meet S M y.1)).Carrier |
        normalizedBlockChart D S old L M y.1 g t ∈
          leftCoset (left D S old L y.1 z.1).range y.2} := by
  exact normalizedBlock_separated_of_maps D S old L
    M x y z hsep g _ _ (by intro t ht; exact ht)
    (by intro t ht; exact ht)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
