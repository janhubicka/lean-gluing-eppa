import GluingEPPA.Reducts.AnchorGroupDescent
import GluingEPPA.Reducts.MultipartiteWitnessScope

/-! Retained earlier application; no new example-specific theorem is added.
The general equality-free transfer is developed separately. -/
namespace GluingEPPA.Reducts.AnchorMultipartiteTransfer
open GluingEPPA.Reducts.AnchorExtraction
open GluingEPPA.Reducts.AnchorActions
open GluingEPPA.Reducts.AnchorGroupDescent
open GluingEPPA.Reducts.MultipartiteActualLocalActions
open GluingEPPA.Reducts.MultipartiteWitnessScope
universe u
variable {A V Z J I K : Type u}

def pullbackInput {Y : Type u} (T : Input V I) (p : Y → V) : Input Y I where
  owner y := T.owner (p y)
  color x y := T.color (p x) (p y)
  within x y h := T.within (p x) (p y) h
  reverse x y h := T.reverse (p x) (p y) h

noncomputable section
variable {e : A ↪ V} {L : Rel A → Prop} {H : Equiv.Perm V → Prop}
variable (S : System e L H Z J) [Nonempty V]
def extractedInput (T : Input V I) : Input (Real S) I := pullbackInput T (projection S)

theorem extracted_copy_color (T : Input V I) (B : Input A K)
    (he : ∀ a b, T.color (e a) (e b) = B.color a b)
    (hH : ∀ h : Equiv.Perm V, H h → ∀ x y, T.color (h x) (h y) = T.color x y)
    (j : J) (hj : retained S j) (a b : A) :
    (extractedInput S T).color (chart S j hj a) (chart S j hj b) = B.color a b := by
  obtain ⟨h,hh,ha,hp⟩ := chart_has_ambient_label S j hj
  change T.color (projection S (chart S j hj a)) (projection S (chart S j hj b)) = _
  rw [hp,hp,hH h hh,he]

theorem extracted_copy_part (T : Input V I) (B : Input A K)
    (he : ∀ a b, T.color (e a) (e b) = B.color a b)
    (hH : ∀ h : Equiv.Perm V, H h → ∀ x y, T.color (h x) (h y) = T.color x y)
    (j : J) (hj : retained S j) (a b : A) :
    (extractedInput S T).owner (chart S j hj a) = (extractedInput S T).owner (chart S j hj b) ↔
      B.owner a = B.owner b := by
  rw [same_part_iff,same_part_iff,extracted_copy_color S T B he hH j hj a b,
    extracted_copy_color S T B he hH j hj b a]

theorem extracted_action_color (T : Input V I)
    (hH : ∀ h : Equiv.Perm V, H h → ∀ x y, T.color (h x) (h y) = T.color x y)
    (g : (realHom S).range) (x y : Real S) :
    (extractedInput S T).color (g.val x) (g.val y) = (extractedInput S T).color x y := by
  change T.color (projection S (g.val x)) (projection S (g.val y)) = _
  rw [descended_equivariant S,descended_equivariant S]
  exact hH (descendedMap S g).val (anchor_range_allowed S (descendedMap S g)) _ _

theorem extracted_action_part (T : Input V I)
    (hH : ∀ h : Equiv.Perm V, H h → ∀ x y, T.color (h x) (h y) = T.color x y)
    (g : (realHom S).range) (x y : Real S) :
    (extractedInput S T).owner (g.val x) = (extractedInput S T).owner (g.val y) ↔
      (extractedInput S T).owner x = (extractedInput S T).owner y := by
  rw [same_part_iff,same_part_iff,extracted_action_color S T hH g x y,
    extracted_action_color S T hH g y x]

theorem extracted_parts_surjective (T : Input V I)
    (hp : Function.Surjective (projection S)) (ho : Function.Surjective T.owner) :
    Function.Surjective (extractedInput S T).owner := by
  intro i
  obtain ⟨v,hv⟩ := ho i
  obtain ⟨y,hy⟩ := hp v
  exact ⟨y,(congrArg T.owner hy).trans hv⟩
end

theorem ordered_palette_pullback {Y M : Type u} {d : Nat}
    (p : Y → V) (g : Y → Y) (h : V → V) (c : (Fin d → V) → M) (gamma : M → M)
    (heq : ∀ y, p (g y) = h (p y))
    (hc : ∀ t : Fin d → V, c (h ∘ t) = gamma (c t)) (t : Fin d → Y) :
    c (p ∘ g ∘ t) = gamma (c (p ∘ t)) := by
  have hfun : p ∘ g ∘ t = h ∘ (p ∘ t) := funext (fun i => heq (t i))
  rw [hfun,hc]
end GluingEPPA.Reducts.AnchorMultipartiteTransfer
