import GluingEPPA.Reducts.AnchorGroupDescent
import GluingEPPA.Reducts.PullbackPresentations

/-! Uniform structural descent through the constructed anchor projection.
No language, palette, affine law or output completion is supplied. -/
namespace GluingEPPA.Reducts.AnchorStructureTransfer
open GluingEPPA.Reducts.AnchorExtraction
open GluingEPPA.Reducts.AnchorActions
open GluingEPPA.Reducts.AnchorGroupDescent
open GluingEPPA.Reducts.PullbackPresentations
noncomputable section
universe u v w
variable {A V Z J : Type u} {e : A ↪ V}
variable {L : Rel A → Prop} {H : Equiv.Perm V → Prop}
variable (S : System e L H Z J) [Nonempty V]
variable (P : Presentation.{u,v})

def extracted (T : P.Obj V) : P.Obj (Real S) := P.pull (projection S) T

theorem retained_copy (A0 : P.Obj A) (T : P.Obj V)
    (he : P.pull e T = A0)
    (hH : ∀ h : Equiv.Perm V, H h → P.IsInvariant T h)
    (j : J) (hj : retained S j) :
    P.IsEmbedding A0 (extracted S P T) (chart S j hj) := by
  obtain ⟨h, hh, ha, hp⟩ := chart_has_ambient_label S j hj
  refine ⟨(chart S j hj).injective, ?_⟩
  change P.pull (chart S j hj) (P.pull (projection S) T) = A0
  calc
    P.pull (chart S j hj) (P.pull (projection S) T) =
        P.pull (projection S ∘ chart S j hj) T :=
      (P.pull_comp (chart S j hj) (projection S) T).symm
    _ = P.pull (h ∘ e) T := congrArg (fun f => P.pull f T) (funext hp)
    _ = P.pull e (P.pull h T) := P.pull_comp e h T
    _ = A0 := by rw [hH h hh, he]

theorem image_action (T : P.Obj V)
    (hH : ∀ h : Equiv.Perm V, H h → P.IsInvariant T h)
    (g : (realHom S).range) :
    P.IsInvariant (extracted S P T) g.val := by
  exact P.equivariant_pullback (projection S) g.val (descendedMap S g).val T
    (descended_equivariant S g)
    (hH (descendedMap S g).val (anchor_range_allowed S (descendedMap S g)))

theorem structural_transfer (A0 : P.Obj A) (T : P.Obj V)
    (he : P.pull e T = A0)
    (hH : ∀ h : Equiv.Perm V, H h → P.IsInvariant T h) :
    ∃ B : P.Obj (Real S), B = P.pull (projection S) T ∧
      (∀ j (hj : retained S j), P.IsEmbedding A0 B (chart S j hj)) ∧
      (∀ g : (realHom S).range, P.IsInvariant B g.val) := by
  exact ⟨extracted S P T, rfl, retained_copy S P A0 T he hH, image_action S P T hH⟩

theorem member_transfer
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} (f : X → Y) (T : P.Obj Y),
      Member T → Member (P.pull f T))
    (T : P.Obj V) (hT : Member T) : Member (extracted S P T) :=
  closed (projection S) T hT

theorem member_transfer_surjective
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} (f : X → Y), Function.Surjective f →
      ∀ T : P.Obj Y, Member T → Member (P.pull f T))
    (hs : Function.Surjective (projection S))
    (T : P.Obj V) (hT : Member T) : Member (extracted S P T) :=
  closed (projection S) hs T hT

theorem surjective_readout_transfer (Q : Presentation.{u,w})
    (R : SurjectiveReduct P Q) (T : P.Obj V) (A0 : Q.Obj A)
    (hs : Function.Surjective (projection S))
    (he : Q.pull e (R.interpret T) = A0)
    (hH : ∀ h : Equiv.Perm V, H h → Q.IsInvariant (R.interpret T) h) :
    ∃ B : P.Obj (Real S), B = P.pull (projection S) T ∧
      R.interpret B = Q.pull (projection S) (R.interpret T) ∧
      (∀ j (hj : retained S j), Q.IsEmbedding A0 (R.interpret B) (chart S j hj)) ∧
      (∀ g : (realHom S).range, Q.IsInvariant (R.interpret B) g.val) := by
  refine ⟨P.pull (projection S) T, rfl, R.natural (projection S) hs T, ?_, ?_⟩
  · rw [R.natural (projection S) hs T]
    exact retained_copy S Q A0 (R.interpret T) he hH
  · rw [R.natural (projection S) hs T]
    exact image_action S Q (R.interpret T) hH

theorem completed_local_section {X Tree : Type u} (T : P.Obj V)
    (r : X ↪ Real S) (q : Tree → Real S) (s : X → Tree) (hs : q ∘ s = r) :
    P.IsEmbedding (P.pull r (extracted S P T))
      (P.pull q (extracted S P T)) s :=
  P.pullback_section (extracted S P T) r q s hs

theorem quotient_structure_transfer (C : StableCongruence P)
    (A0 : C.quotient.Obj A) (T : C.quotient.Obj V)
    (he : C.quotient.pull e T = A0)
    (hH : ∀ h : Equiv.Perm V, H h → C.quotient.IsInvariant T h) :
    ∃ B : C.quotient.Obj (Real S), B = C.quotient.pull (projection S) T ∧
      (∀ j (hj : retained S j), C.quotient.IsEmbedding A0 B (chart S j hj)) ∧
      (∀ g : (realHom S).range, C.quotient.IsInvariant B g.val) :=
  structural_transfer S C.quotient A0 T he hH
end
end GluingEPPA.Reducts.AnchorStructureTransfer
