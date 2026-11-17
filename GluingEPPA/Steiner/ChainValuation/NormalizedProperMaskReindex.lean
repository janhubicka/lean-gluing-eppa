import GluingEPPA.Steiner.ChainValuation.LinkChain

/-!
# Reindex the actual earlier recursive family under a smaller mask

For the proper-mask alternative of the chain-restriction lemma,
an original block with mask A becomes the earlier block M intersection A.
If M is not contained in A, this mask is *proper in M*, so the
normalized component can be built using the real earlier data
already present at that proper stage.

We explicitly transport the family of old data and Links from
proper subsets of S to proper subsets of M. No arbitrary groups,
choice of replacement stages, or fictional ambient K_S are used.

The final triple-index identity identifies the normalized common
interface with the actual group at M intersection A intersection B.
This is a type-level input for assembling the remaining finite
proper-mask interval as a genuine earlier chain test.
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

/-- The canonical inclusion of proper indices below M into proper
indices below S. It retains the exact original group carrier. -/
def liftProperMask (M : Proper S) (T : Proper M.val) : Proper S :=
  ⟨T.val, lt_trans T.property M.property⟩

@[simp] theorem liftProperMask_val (M : Proper S) (T : Proper M.val) :
    (liftProperMask S M T).val = T.val := rfl

/-- A mask M intersection A, with M not included in A, is genuinely
a proper earlier index of M. -/
def normalizedProperMask (M A : Proper S)
    (h : ¬ M.val ⊆ A.val) : Proper M.val :=
  ⟨M.val ∩ A.val, Step.meet_lt_left S h⟩

@[simp] theorem normalizedProperMask_val (M A : Proper S)
    (h : ¬ M.val ⊆ A.val) :
    (normalizedProperMask S M A h).val = M.val ∩ A.val := rfl

/-- The normalized index is the SAME earlier index, not a fresh
isomorphic copy of the group at M intersection A. -/
theorem lift_normalizedProperMask (M A : Proper S)
    (h : ¬ M.val ⊆ A.val) :
    liftProperMask S M (normalizedProperMask S M A h) =
      Step.meet S M A := by
  apply Subtype.ext
  rfl

/-- Restrict the actual previously available finite recursive
groups to all proper submasks of M. -/
def smallerOld (M : Proper S) :
    ∀ T : Proper M.val, Data E T.val :=
  fun T => old (liftProperMask S M T)

/-- Restrict the actual previously available Link maps. Their
inclusion, deletion, and replacement fields are unchanged. -/
def smallerLinks (M : Proper S) :
    ∀ T U : Proper M.val, T.val ⊆ U.val →
      Link D (smallerOld S old M T) (smallerOld S old M U) :=
  fun T U h => L (liftProperMask S M T) (liftProperMask S M U) h

/-- The normalized source group is definitionally the original
earlier K_(M intersection A) group, including its named generators. -/
theorem normalizedProper_data (M A : Proper S)
    (h : ¬ M.val ⊆ A.val) :
    smallerOld S old M (normalizedProperMask S M A h) =
      old (Step.meet S M A) := by
  rfl

/-- The triple common mask of normalized blocks is literally
the older M intersection A intersection B stage. -/
theorem normalizedTripleMask (M A B : Proper S)
    (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val) :
    liftProperMask S M
      (Step.meet M.val
        (normalizedProperMask S M A hA)
        (normalizedProperMask S M B hB)) =
      Step.meet S M (Step.meet S A B) := by
  apply Subtype.ext
  ext e
  simp only [liftProperMask, normalizedProperMask, Step.meet,
    Finset.mem_inter]
  tauto

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
