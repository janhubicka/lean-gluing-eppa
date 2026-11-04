import GluingEPPA.Steiner.ChainValuation.ComponentCosetQuotient
import GluingEPPA.Steiner.ChainValuation.LinkRestrictedMatching

/-!
# Restricted attachment matching on the actual M-component quotients

The earlier Link construction already gives a partial matching between
Set-valued restricted left cosets on the two adjacent Cayley groups.
The quotient-coset equivalence converts each *actual* M-component
quotient into one such coset. We reindex the matching along these
injective maps, with no ambient larger group K_S.

This is the local bridge needed to instantiate MatchingGluing on
genuine Cayley-block connectivity. Identifying this matching at each
boundary of a full separated chain remains a separate induction.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v u' v'
variable {X : Type u} {Y : Type v}
variable {X' : Type u'} {Y' : Type v'}

/-- The component map on a disjoint union of two different sorts. -/
def sumComponentMap (f : X' → X) (g : Y' → Y) :
    Sum X' Y' → Sum X Y
  | .inl x => .inl (f x)
  | .inr y => .inr (g y)

theorem sumComponentMap_injective
    (f : X' → X) (g : Y' → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (sumComponentMap f g) := by
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          exact congrArg Sum.inl (hf (Sum.inl.inj hxy))
      | inr b =>
          cases hxy
  | inr a =>
      cases y with
      | inl b =>
          cases hxy
      | inr b =>
          exact congrArg Sum.inr (hg (Sum.inr.inj hxy))

/-- Pulling a partial matching back through injections on both
sides gives another genuine partial matching, not a general relation. -/
def Matching.pullbackSum
    (T : Matching (Sum X Y))
    (f : X' → X) (g : Y' → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Matching (Sum X' Y') where
  Rel a b := T.Rel (sumComponentMap f g a) (sumComponentMap f g b)
  symm := by
    intro a b h
    exact T.symm h
  unique := by
    intro a b c hab hac
    apply sumComponentMap_injective f g hf hg
    exact T.unique hab hac

end GluingEPPA.Steiner.ChainValuation

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe w
variable {V E : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The honest quotient-class-to-coset map for an earlier block. -/
noncomputable def componentCosetMap (M A : Proper S) :
    Quotient (labelReachSetoid
        (fun e => ((block S old A).matching e).Rel) M.val) →
      Set (old A).Carrier :=
  fun c => ((restrictedBlockComponentsEquiv D S old L M A) c).val

theorem componentCosetMap_injective (M A : Proper S) :
    Function.Injective (componentCosetMap D S old L M A) := by
  intro x y hxy
  apply (restrictedBlockComponentsEquiv D S old L M A).injective
  exact Subtype.ext hxy

/-- The matching between **actual** M-component quotient classes
of two distinct earlier Cayley blocks, obtained from the literal
two-group Link matching of their corresponding left cosets. -/
noncomputable def restrictedActualComponentMatching
    (M A B : Proper S) (h : (old A).Carrier) :
    Matching (Sum
      (Quotient (labelReachSetoid
        (fun e => ((block S old A).matching e).Rel) M.val))
      (Quotient (labelReachSetoid
        (fun e => ((block S old B).matching e).Rel) M.val))) :=
  (restrictedLinkMatching D S old L M A B h).pullbackSum
    (componentCosetMap D S old L M A)
    (componentCosetMap D S old L M B)
    (componentCosetMap_injective D S old L M A)
    (componentCosetMap_injective D S old L M B)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
