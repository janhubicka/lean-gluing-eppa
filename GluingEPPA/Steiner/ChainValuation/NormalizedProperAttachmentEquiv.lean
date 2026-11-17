import GluingEPPA.Steiner.ChainValuation.NormalizedProperSeparatedChain
import GluingEPPA.Steiner.ChainValuation.NormalizedTwoBlockComponent

/-!
# The normalized attachment is the literal smaller-stage attachment

The interface index M ∩ (A ∩ B) equals the index
(M ∩ A) ∩ (M ∩ B) used by the earlier chain constructor.  Transport
along this equality gives a concrete multiplicative equivalence of
the actual earlier carriers.  Both inclusion maps commute pointwise
with that transport.

Consequently a normalized attachment and the literal smaller-stage
attachment have equivalent quotient spaces.  The equivalence preserves
the old and new embeddings and reflects every labelled edge.  The old
side may already have been identified with a smaller-chain prefix;
this is exactly the inductive form needed for a finite source trace.
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

/-- Equality of proper indices transports the actual group structure. -/
def properIndexMulEquiv {X Y : Proper S} (h : X = Y) :
    (old X).Carrier ≃* (old Y).Carrier := by
  cases h
  exact MulEquiv.refl _

omit [Finite V] [Fintype E] [DecidableEq E] in
private theorem inclusion_properIndexMulEquiv
    (X Y T : Proper S) (hXY : X = Y)
    (hX : X.val ⊆ T.val) (hY : Y.val ⊆ T.val) (x : (old X).Carrier) :
    (L Y T hY).incl (properIndexMulEquiv S old hXY x) = (L X T hX).incl x := by
  subst Y
  rfl

/-- The canonical interface change of parameters, from the original
triple-mask group to the actual common group of the smaller chain. -/
def normalizedProperInterfaceEquiv (M A B : Proper S)
    (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val) :
    (old (Step.meet S M (common S A B))).Carrier ≃*
      (smallerOld S old M (common M.val
        (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))).Carrier :=
  properIndexMulEquiv S old (normalizedTripleMask S M A B hA hB).symm

theorem normalizedProper_left_apply (M A B : Proper S)
    (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val)
    (t : (old (Step.meet S M (common S A B))).Carrier) :
    left D M.val (smallerOld S old M) (smallerLinks D S old L M)
        (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)
        (normalizedProperInterfaceEquiv S old M A B hA hB t) =
      normalizedCommonLeft D S old L M A B t := by
  exact inclusion_properIndexMulEquiv D S old L _ _ _
    (normalizedTripleMask S M A B hA hB).symm _ _ t

theorem normalizedProper_right_apply (M A B : Proper S)
    (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val)
    (t : (old (Step.meet S M (common S A B))).Carrier) :
    right D M.val (smallerOld S old M) (smallerLinks D S old L M)
        (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)
        (normalizedProperInterfaceEquiv S old M A B hA hB t) =
      normalizedCommonRight D S old L M A B t := by
  exact inclusion_properIndexMulEquiv D S old L _ _ _
    (normalizedTripleMask S M A B hA hB).symm _ _ t

/-- Source state of one original normalized attachment. -/
abbrev normalizedProperAttachmentSource (M A B : Proper S)
    (C : ChainState E (block S old (Step.meet S M A)))
    (shift : (old (Step.meet S M A)).Carrier) :=
  ExtendedSpace (block S old (Step.meet S M A)) (block S old (Step.meet S M B)) C shift
    (normalizedCommonLeft D S old L M A B) (normalizedCommonRight D S old L M A B)
    (normalizedCommonLeft_injective D S old L M A B)
    (normalizedCommonRight_injective D S old L M A B)

/-- Target state of the literal smaller-stage attachment. -/
abbrev normalizedProperAttachmentTarget (M A B : Proper S)
    (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val)
    (C : ChainState E (block S old (Step.meet S M A)))
    (shift : (old (Step.meet S M A)).Carrier) :=
  ExtendedSpace
    (block M.val (smallerOld S old M) (normalizedProperMask S M A hA))
    (block M.val (smallerOld S old M) (normalizedProperMask S M B hB)) C shift
    (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
    (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
    (left_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
    (right_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))

section Attachment

variable (M A B : Proper S) (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val)
variable (C C' : ChainState E (block S old (Step.meet S M A)))
variable (F : C.Space ≃ C'.Space)
variable (hlast : ∀ t, F (C.lastEmbed t) = C'.lastEmbed t)
variable (shift : (old (Step.meet S M A)).Carrier)

/-- A compatible prefix equivalence and the canonical interface cast
induce an equivalence to the actual smaller-chain attachment. -/
noncomputable def normalizedProperAttachmentEquiv :
    normalizedProperAttachmentSource D S old L M A B C shift ≃
      normalizedProperAttachmentTarget D S old L M A B hA hB C' shift :=
  pushoutEquivOfEquivs
    (attachInto C.lastEmbed shift (normalizedCommonLeft D S old L M A B))
    (normalizedCommonRight D S old L M A B)
    (attachInto_injective C.lastEmbed C.lastInjective shift
      (normalizedCommonLeft D S old L M A B)
      (normalizedCommonLeft_injective D S old L M A B))
    (normalizedCommonRight_injective D S old L M A B)
    (attachInto C'.lastEmbed shift
      (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
        (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)))
    (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
    (attachInto_injective C'.lastEmbed C'.lastInjective shift
      (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
        (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
      (left_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
        (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)))
    (right_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
      (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
    F (Equiv.refl _) (normalizedProperInterfaceEquiv S old M A B hA hB).toEquiv
    (by
      intro t
      exact (hlast _).trans
        (congrArg (fun v : (old (Step.meet S M A)).Carrier => C'.lastEmbed (shift * v))
          (normalizedProper_left_apply D S old L M A B hA hB t).symm))
    (by intro t; exact (normalizedProper_right_apply D S old L M A B hA hB t).symm)

theorem normalizedProperAttachmentEquiv_old (x : C.Space) :
    normalizedProperAttachmentEquiv D S old L M A B hA hB C C' F hlast shift
      (oldEmbed (block S old (Step.meet S M A)) (block S old (Step.meet S M B)) C shift
        (normalizedCommonLeft D S old L M A B) (normalizedCommonRight D S old L M A B)
        (normalizedCommonLeft_injective D S old L M A B)
        (normalizedCommonRight_injective D S old L M A B) x) =
      oldEmbed
        (block M.val (smallerOld S old M) (normalizedProperMask S M A hA))
        (block M.val (smallerOld S old M) (normalizedProperMask S M B hB)) C' shift
        (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (left_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (right_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)) (F x) := rfl

theorem normalizedProperAttachmentEquiv_new (x : (old (Step.meet S M B)).Carrier) :
    normalizedProperAttachmentEquiv D S old L M A B hA hB C C' F hlast shift
      (newEmbed (block S old (Step.meet S M A)) (block S old (Step.meet S M B)) C shift
        (normalizedCommonLeft D S old L M A B) (normalizedCommonRight D S old L M A B)
        (normalizedCommonLeft_injective D S old L M A B)
        (normalizedCommonRight_injective D S old L M A B) x) =
      newEmbed
        (block M.val (smallerOld S old M) (normalizedProperMask S M A hA))
        (block M.val (smallerOld S old M) (normalizedProperMask S M B hB)) C' shift
        (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (left_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (right_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)) x := rfl

/-- Every genuine label is preserved and reflected.  These relations
are definitionally the matching relations of the two `extend` states. -/
theorem normalizedProperAttachmentEquiv_edge_iff
    (e : E)
    (hedge : ∀ x y, (C.matching e).Rel x y ↔ (C'.matching e).Rel (F x) (F y))
    (x y : normalizedProperAttachmentSource D S old L M A B C shift) :
    extendedEdgeRel (block S old (Step.meet S M A)) (block S old (Step.meet S M B)) C shift
        (normalizedCommonLeft D S old L M A B) (normalizedCommonRight D S old L M A B)
        (normalizedCommonLeft_injective D S old L M A B)
        (normalizedCommonRight_injective D S old L M A B) e x y ↔
      extendedEdgeRel
        (block M.val (smallerOld S old M) (normalizedProperMask S M A hA))
        (block M.val (smallerOld S old M) (normalizedProperMask S M B hB)) C' shift
        (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (left_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))
        (right_injective D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)) e
        (normalizedProperAttachmentEquiv D S old L M A B hA hB C C' F hlast shift x)
        (normalizedProperAttachmentEquiv D S old L M A B hA hB C C' F hlast shift y) := by
  let G := normalizedProperAttachmentEquiv D S old L M A B hA hB C C' F hlast shift
  have hold := normalizedProperAttachmentEquiv_old D S old L M A B hA hB C C' F hlast shift
  have hnew := normalizedProperAttachmentEquiv_new D S old L M A B hA hB C C' F hlast shift
  constructor
  · rintro (⟨a, b, hab, ha, hb⟩ | ⟨g, he, hg, hg'⟩)
    · refine Or.inl ⟨F a, F b, (hedge a b).mp hab, ?_, ?_⟩
      · rw [← ha]
        exact (hold a).symm
      · rw [← hb]
        exact (hold b).symm
    · refine Or.inr ⟨g, he, ?_, ?_⟩
      · rw [← hg]
        exact (hnew g).symm
      · rw [← hg']
        exact (hnew _).symm
  · rintro (⟨a', b', hab, ha, hb⟩ | ⟨g, he, hg, hg'⟩)
    · obtain ⟨a, rfl⟩ := F.surjective a'
      obtain ⟨b, rfl⟩ := F.surjective b'
      exact Or.inl ⟨a, b, (hedge a b).mpr hab,
        G.injective ((hold a).trans ha), G.injective ((hold b).trans hb)⟩
    · exact Or.inr ⟨g, he,
        G.injective ((hnew g).trans hg), G.injective ((hnew _).trans hg')⟩

end Attachment

/-- The literal smaller attachment has the same exit subset in the
unchanged last-block coordinates. -/
theorem normalizedProper_exitSet (M A B : Proper S)
    (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val)
    (shift : (old (Step.meet S M A)).Carrier) :
    exitSet (block M.val (smallerOld S old M) (normalizedProperMask S M A hA)) shift
        (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)) =
      exitSet (block S old (Step.meet S M A)) shift
        (normalizedCommonLeft D S old L M A B) := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨s, rfl⟩ := (normalizedProperInterfaceEquiv S old M A B hA hB).surjective t
    exact ⟨s, (congrArg (fun v : (old (Step.meet S M A)).Carrier => shift * v)
      (normalizedProper_left_apply D S old L M A B hA hB s)).symm.trans ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨normalizedProperInterfaceEquiv S old M A B hA hB t,
      (congrArg (fun v : (old (Step.meet S M A)).Carrier => shift * v)
        (normalizedProper_left_apply D S old L M A B hA hB t)).trans ht⟩

/-- The next entry subset is unchanged by the interface reparametrization. -/
theorem normalizedProper_entrySet (M A B : Proper S)
    (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val) :
    Set.range (right D M.val (smallerOld S old M) (smallerLinks D S old L M)
        (normalizedProperMask S M A hA) (normalizedProperMask S M B hB)) =
      Set.range (normalizedCommonRight D S old L M A B) := by
  exact congrArg (fun H : Subgroup (old (Step.meet S M B)).Carrier =>
      (H : Set (old (Step.meet S M B)).Carrier))
    (normalizedProper_right_range D S old L M A B hA hB)

theorem normalizedProper_target_separated (M A B : Proper S)
    (hA : ¬ M.val ⊆ A.val) (hB : ¬ M.val ⊆ B.val)
    (C C' : ChainState E (block S old (Step.meet S M A)))
    (shift : (old (Step.meet S M A)).Carrier)
    (hentry : C'.entry = C.entry)
    (hsep : Disjoint C.entry (exitSet (block S old (Step.meet S M A)) shift
      (normalizedCommonLeft D S old L M A B))) :
    Disjoint C'.entry
      (exitSet (block M.val (smallerOld S old M) (normalizedProperMask S M A hA)) shift
        (left D M.val (smallerOld S old M) (smallerLinks D S old L M)
          (normalizedProperMask S M A hA) (normalizedProperMask S M B hB))) := by
  rw [hentry, normalizedProper_exitSet]
  exact hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
