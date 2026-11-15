import GluingEPPA.Reducts.AnchorGroupDescent
import GluingEPPA.Reducts.MultipartiteWitnessScope

/-! The multipartite structural transfer uses the constructed anchor projection.
No unspecified completion or free relational-union property is assumed.
Ordered tuple pullback is also checked for any prescribed palette action;
normalized set-cochain pullback is a different, unclaimed convention here. -/
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

def extractedInput (T : Input V I) : Input S.Real I := pullbackInput T S.projection

theorem extracted_copy_color (T : Input V I) (B : Input A K)
    (he : ∀ a b, T.color (e a) (e b) = B.color a b)
    (hH : ∀ h : Equiv.Perm V, H h → ∀ x y, T.color (h x) (h y) = T.color x y)
    (j : J) (hj : S.retained j) (a b : A) :
    (S.extractedInput T).color (S.chart j hj a) (S.chart j hj b) = B.color a b := by
  obtain ⟨h,hh,ha,hp⟩ := S.chart_has_ambient_label j hj
  change T.color (S.projection (S.chart j hj a)) (S.projection (S.chart j hj b)) = _
  rw [hp,hp,hH h hh,he]

theorem extracted_copy_part (T : Input V I) (B : Input A K)
    (he : ∀ a b, T.color (e a) (e b) = B.color a b)
    (hH : ∀ h : Equiv.Perm V, H h → ∀ x y, T.color (h x) (h y) = T.color x y)
    (j : J) (hj : S.retained j) (a b : A) :
    (S.extractedInput T).owner (S.chart j hj a) = (S.extractedInput T).owner (S.chart j hj b) ↔
      B.owner a = B.owner b := by
  rw [same_part_iff,same_part_iff,S.extracted_copy_color T B he hH j hj a b,
    S.extracted_copy_color T B he hH j hj b a]

theorem extracted_action_color (T : Input V I)
    (hH : ∀ h : Equiv.Perm V, H h → ∀ x y, T.color (h x) (h y) = T.color x y)
    (g : S.realHom.range) (x y : S.Real) :
    (S.extractedInput T).color (g.val x) (g.val y) = (S.extractedInput T).color x y := by
  change T.color (S.projection (g.val x)) (S.projection (g.val y)) = _
  rw [S.descended_equivariant,S.descended_equivariant]
  exact hH (S.descendedMap g).val (S.anchor_range_allowed (S.descendedMap g)) _ _

theorem extracted_action_part (T : Input V I)
    (hH : ∀ h : Equiv.Perm V, H h → ∀ x y, T.color (h x) (h y) = T.color x y)
    (g : S.realHom.range) (x y : S.Real) :
    (S.extractedInput T).owner (g.val x) = (S.extractedInput T).owner (g.val y) ↔
      (S.extractedInput T).owner x = (S.extractedInput T).owner y := by
  rw [same_part_iff,same_part_iff,S.extracted_action_color T hH g x y,
    S.extracted_action_color T hH g y x]

theorem extracted_parts_surjective (T : Input V I)
    (hp : Function.Surjective S.projection) (ho : Function.Surjective T.owner) :
    Function.Surjective (S.extractedInput T).owner := by
  intro i
  obtain ⟨v,hv⟩ := ho i
  obtain ⟨y,hy⟩ := hp v
  exact ⟨y,(congrArg T.owner hy).trans hv⟩

end

/-- Includes repeated entries: this is ordinary ordered-tuple pullback. -/
theorem ordered_palette_pullback {Y M : Type u} {d : Nat}
    (p : Y → V) (g : Y → Y) (h : V → V) (c : (Fin d → V) → M) (gamma : M → M)
    (heq : ∀ y, p (g y) = h (p y))
    (hc : ∀ t : Fin d → V, c (h ∘ t) = gamma (c t)) (t : Fin d → Y) :
    c (p ∘ g ∘ t) = gamma (c (p ∘ t)) := by
  have hfun : p ∘ g ∘ t = h ∘ (p ∘ t) := funext (fun i => heq (t i))
  rw [hfun,hc]

end GluingEPPA.Reducts.AnchorMultipartiteTransfer
