import GluingEPPA.Steiner.ChainValuation.NormalizedProperRawChain
import GluingEPPA.Steiner.ChainValuation.ActualNormalizedBoundary
import Mathlib.Data.List.OfFn

/-!
# Normalized restrictions are actual earlier separated-chain tests

The normalized interface groups are indexed as M ∩ (A ∩ B), whereas
the chain constructor at M uses (M ∩ A) ∩ (M ∩ B).  The equality of
these indices identifies their actual Link inclusion ranges.  Thus
separation proved in the original family is precisely the separation
required by `SeparatedChains` at M; it is not an additional premise.

The final construction takes a positive bounded list of actual source
masks and shifts with the normalized interface separation proved for
each consecutive triple.  It returns a test in the same finite family
recorded by `testPackage`, retaining the exact list and its length.
Selection of that list from a component and its action equivalence
are separate obligations.
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

private theorem inclusionRange_congr_source
    (X Y T : Proper S) (hXY : X = Y)
    (hX : X.val ⊆ T.val) (hY : Y.val ⊆ T.val) :
    (L X T hX).incl.range = (L Y T hY).incl.range := by
  subst Y
  rfl

/-- The left interface of an actual chain at M is the original
triple-intersection inclusion, with only its index reassociated. -/
theorem normalizedProper_left_range
    (M A B : Proper S) (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val) :
    (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M A hA)
      (normalizedProperMask S M B hB)).range =
    (normalizedCommonLeft D S old L M A B).range := by
  change
    (L (liftProperMask S M
      (Step.meet M.val (normalizedProperMask S M A hA)
        (normalizedProperMask S M B hB)))
      (Step.meet S M A) _).incl.range =
    (L (Step.meet S M (Step.meet S A B))
      (Step.meet S M A) _).incl.range
  exact inclusionRange_congr_source D S old L _ _ _
    (normalizedTripleMask S M A B hA hB) _ _

/-- The corresponding right interface uses the same genuine
earlier group and inclusion range. -/
theorem normalizedProper_right_range
    (M A B : Proper S) (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val) :
    (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M A hA)
      (normalizedProperMask S M B hB)).range =
    (normalizedCommonRight D S old L M A B).range := by
  change
    (L (liftProperMask S M
      (Step.meet M.val (normalizedProperMask S M A hA)
        (normalizedProperMask S M B hB)))
      (Step.meet S M B) _).incl.range =
    (L (Step.meet S M (Step.meet S A B))
      (Step.meet S M B) _).incl.range
  exact inclusionRange_congr_source D S old L _ _ _
    (normalizedTripleMask S M A B hA hB) _ _

/-- The actual earlier-stage triple condition is equivalent to
the normalized entry/exit condition in the original Link family. -/
theorem normalizedProper_tripleSeparated_iff
    (M : Proper S) (x y z : NormalizedProperSource S old M) :
    tripleSeparated D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperAtom S old M x)
      (normalizedProperAtom S old M y)
      (normalizedProperAtom S old M z) ↔
    Disjoint
      (leftCoset (normalizedCommonRight D S old L M x.mask y.mask).range 1)
      (leftCoset (normalizedCommonLeft D S old L M y.mask z.mask).range y.shift) := by
  unfold tripleSeparated
  change Disjoint
    (leftCoset (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M x.mask x.proper)
      (normalizedProperMask S M y.mask y.proper)).range 1)
    (leftCoset (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M y.mask y.proper)
      (normalizedProperMask S M z.mask z.proper)).range y.shift) ↔ _
  rw [normalizedProper_right_range, normalizedProper_left_range]
  rfl

/-- Separation written using the actual original common-interface maps. -/
def NormalizedSeparated (M : Proper S) : List (NormalizedProperSource S old M) → Prop
  | x :: y :: z :: rest =>
      Disjoint
        (leftCoset (normalizedCommonRight D S old L M x.mask y.mask).range 1)
        (leftCoset (normalizedCommonLeft D S old L M y.mask z.mask).range y.shift) ∧
      NormalizedSeparated M (y :: z :: rest)
  | _ => True

theorem normalizedProperList_separated_iff
    (M : Proper S) (sources : List (NormalizedProperSource S old M)) :
    separatedList D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (sources.map (normalizedProperAtom S old M)) ↔
    NormalizedSeparated D S old L M sources := by
  induction sources with
  | nil => rfl
  | cons x rest ih =>
      cases rest with
      | nil => rfl
      | cons y rest =>
          cases rest with
          | nil => rfl
          | cons z rest =>
              change
                (tripleSeparated D M.val (smallerOld S old M) (smallerLinks D S old L M)
                  (normalizedProperAtom S old M x)
                  (normalizedProperAtom S old M y)
                  (normalizedProperAtom S old M z) ∧ _) ↔ _
              exact and_congr
                (normalizedProper_tripleSeparated_iff D S old L M x y z) ih

/-- A nonempty bounded normalized source list with its proved
interface separations belongs to the actual earlier test family. -/
noncomputable def normalizedProperSeparatedChain
    (M : Proper S) (N : Nat)
    (sources : List (NormalizedProperSource S old M))
    (hne : sources ≠ []) (hbound : sources.length ≤ N)
    (hsep : NormalizedSeparated D S old L M sources) :
    SeparatedChains D N M.val (smallerOld S old M) (smallerLinks D S old L M) := by
  have hpos : 0 < sources.length := List.length_pos_iff.mpr hne
  let r : ChainValuation.ChainLength N :=
    ⟨⟨sources.length, Nat.lt_succ_of_le hbound⟩, hpos⟩
  let c := normalizedProperRawChain S old M N r (fun i => sources.get i)
  refine ⟨c, ?_⟩
  change separatedList D M.val (smallerOld S old M) (smallerLinks D S old L M)
    (List.ofFn (fun i : Fin sources.length =>
      normalizedProperAtom S old M (sources.get i)))
  have hlist :
      List.ofFn (fun i : Fin sources.length => normalizedProperAtom S old M (sources.get i)) =
      sources.map (normalizedProperAtom S old M) := by
    exact List.ofFn_getElem_eq_map sources (normalizedProperAtom S old M)
  rw [hlist]
  exact (normalizedProperList_separated_iff D S old L M sources).mpr hsep

theorem normalizedProperSeparatedChain_length
    (M : Proper S) (N : Nat)
    (sources : List (NormalizedProperSource S old M))
    (hne : sources ≠ []) (hbound : sources.length ≤ N)
    (hsep : NormalizedSeparated D S old L M sources) :
    ((normalizedProperSeparatedChain D S old L M N sources hne hbound hsep).val.1.val : Nat) =
      sources.length := rfl

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
