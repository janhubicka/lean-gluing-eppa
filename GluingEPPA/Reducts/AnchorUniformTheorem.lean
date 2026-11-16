import GluingEPPA.Reducts.AnchorLabelledCoherence

/-! The assembled uniform refinement and the exact label-forgetting criterion.
All output maps are the concrete anchor maps. Geometry is supplied only on
the incoming augmented realization, never on the extracted carrier. -/
namespace GluingEPPA.Reducts.AnchorUniformTheorem
open GluingEPPA.Reducts.AnchorExtraction
open GluingEPPA.Reducts.AnchorFamily
open GluingEPPA.Reducts.AnchorActions
open GluingEPPA.Reducts.AnchorGroupDescent
open GluingEPPA.Reducts.AnchorGeometry
open GluingEPPA.Reducts.AnchorGeneralTheorem
open GluingEPPA.Reducts.AnchorLabelledCoherence
open GluingEPPA.Reducts.PullbackPresentations
open GluingEPPA.Reducts.AnchorStructureTransfer
noncomputable section
universe u v
variable {A V Z J : Type u} {e : A ↪ V}
variable {L : Rel A → Prop} {H : Subgroup (Equiv.Perm V)}
variable (S : System e L (fun h => h ∈ H) Z J) [Nonempty V]

structure LabelledLaws (theta : RealGroup S →* H)
    (F : (f : Rel A) → L f → (h : H) → Compatible e f h.val → RealGroup S) : Prop where
  over : ∀ f hf h hc, theta (F f hf h hc) = h
  agrees : ∀ f hf h hc a b, f a b →
    (F f hf h hc).val (chart S S.root (root_retained S) a) = chart S S.root (root_retained S) b
  identity : ∀ D hf, F (partialId D) hf 1 (identityCompatible D) = 1
  composition : ∀ f g hf hg hfg h k hc kc, Matching f g →
    F (relComp f g) hfg (k*h) (compatible_comp e f g h.val k.val hc kc) =
      F g hg k kc * F f hf h hc

theorem constructed_labelled_laws (R : CoherentRaw S)
    (hs : Function.Surjective (projection S)) :
    LabelledLaws S (ambientDescent S hs) (labelledLift S R) :=
  ⟨labelledLift_over S R hs, labelledLift_extends S R,
    labelledLift_identity S R, labelledLift_comp S R⟩

structure AmbientSelection (e : A ↪ V) (L : Rel A → Prop) (H : Subgroup (Equiv.Perm V)) where
  choose : (f : Rel A) → L f → H
  compatible : ∀ f hf, Compatible e f (choose f hf).val
  identity : ∀ D hf, choose (partialId D) hf = 1
  composition : ∀ f g hf hg hfg, Matching f g →
    choose (relComp f g) hfg = choose g hg * choose f hf

structure OutputSelection where
  choose : (f : Rel A) → L f → RealGroup S
  agrees : ∀ f hf a b, f a b →
    (choose f hf).val (chart S S.root (root_retained S) a) = chart S S.root (root_retained S) b
  identity : ∀ D hf, choose (partialId D) hf = 1
  composition : ∀ f g hf hg hfg, Matching f g →
    choose (relComp f g) hfg = choose g hg * choose f hf

/-- Necessity projects any coherent output selection through the constructed map. -/
def selectionToAmbient (hs : Function.Surjective (projection S)) (O : OutputSelection S) :
    AmbientSelection e L H where
  choose f hf := ambientDescent S hs (O.choose f hf)
  compatible := by
    intro f hf a b hab
    have h := congrArg (projection S) (O.agrees f hf a b hab)
    rw [ambientDescent_equivariant S hs, projection_root S a, projection_root S b] at h
    exact h
  identity := by
    intro D hf
    rw [O.identity, (ambientDescent S hs).map_one]
  composition := by
    intro f g hf hg hfg hm
    rw [O.composition f g hf hg hfg hm, (ambientDescent S hs).map_mul]

/-- Sufficiency restricts the already coherent assignment on all labelled arrows. -/
def selectionToOutput (R : CoherentRaw S) (C : AmbientSelection e L H) : OutputSelection S where
  choose f hf := labelledLift S R f hf (C.choose f hf) (C.compatible f hf)
  agrees f hf := labelledLift_extends S R f hf (C.choose f hf) (C.compatible f hf)
  identity := by
    intro D hf
    exact (labelledLift_label_congr S R (partialId D) hf (C.choose _ hf) 1
      (C.compatible _ hf) (identityCompatible D) (C.identity D hf)).trans
      (labelledLift_identity S R D hf)
  composition := by
    intro f g hf hg hfg hm
    exact (labelledLift_label_congr S R (relComp f g) hfg (C.choose _ hfg)
      (C.choose g hg * C.choose f hf) (C.compatible _ hfg)
      (compatible_comp e f g _ _ (C.compatible f hf) (C.compatible g hg))
      (C.composition f g hf hg hfg hm)).trans
      (labelledLift_comp S R f g hf hg hfg (C.choose f hf) (C.choose g hg)
        (C.compatible f hf) (C.compatible g hg) hm)

theorem coherent_forgetting_iff (R : CoherentRaw S)
    (hs : Function.Surjective (projection S)) :
    Nonempty (OutputSelection S) ↔ Nonempty (AmbientSelection e L H) :=
  ⟨fun ⟨O⟩ => ⟨selectionToAmbient S hs O⟩,
    fun ⟨C⟩ => ⟨selectionToOutput S R C⟩⟩

theorem real_group_preserves_copies (g : RealGroup S) (j : J) (hj : retained S j) :
    ∃ k, ∃ hk : retained S k, ∀ a, g.val (chart S j hj a) = chart S k hk a := by
  let t := imageLift S g
  let s := chosen S t
  obtain ⟨k,hk⟩ := s.forward_copy j
  refine ⟨k,s.image_retained j k hj hk,?_⟩
  intro a
  have h := s.restrict_chart j k hj hk a
  change realHom S (imageLift S g) (chart S j hj a) = _ at h
  rw [imageLift_spec S g] at h
  exact h

/-- Uniform conditional endpoint. The incoming augmented geometry remains
an explicit premise; the extracted projection, action, structure and coherent
labelled extensions are all constructed. -/
theorem general_structured_labelled_refinement [Finite Z]
    (R : CoherentRaw S) (hzero : L (emptyRel A))
    (hlift : ∀ f, L f → ∃ h : H, Compatible e f h.val)
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, h ∈ H ∧ ∃ a : A, h (e a) = v)
    (n : Nat) (hconf : Conformal n (sourceEdges S)) (hchord : Chordal n (sourceEdges S))
    (P : Presentation.{u,v}) (A0 : P.Obj A) (T : P.Obj V)
    (he : P.pull e T = A0) (hH : ∀ h : H, P.IsInvariant T h.val)
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} (p : X → Y), Function.Surjective p →
      ∀ B : P.Obj Y, Member B → Member (P.pull p B)) (hT : Member T) :
    Finite (Real S) ∧ Function.Surjective (projection S) ∧
    ∃ B : P.Obj (Real S), ∃ theta : RealGroup S →* H, ∃ sec : H →* RealGroup S,
      B = P.pull (projection S) T ∧ Member B ∧
      (∀ h, theta (sec h) = h) ∧ Function.Surjective theta ∧
      (∀ g y, projection S (g.val y) = (theta g).val (projection S y)) ∧
      LabelledLaws S theta (labelledLift S R) ∧
      (∀ j (hj : retained S j), P.IsEmbedding A0 B (chart S j hj)) ∧
      (∀ g : RealGroup S, P.IsInvariant B g.val) ∧
      (∀ y : Real S, ∃ j, ∃ hj : retained S j, ∃ a, chart S j hj a = y) ∧
      (∀ g : RealGroup S, ∀ j (hj : retained S j),
        ∃ k, ∃ hk : retained S k, ∀ a, g.val (chart S j hj a) = chart S k hk a) ∧
      (∀ j k (hj : retained S j) (hk : retained S k),
        ∃ g : RealGroup S, ∀ a, g.val (chart S j hj a) = chart S k hk a) ∧
      (∀ j k (hj : retained S j) (hk : retained S k),
        ∃ f, L f ∧ ∀ a b, chart S j hj a = chart S k hk b ↔ f a b) ∧
      (∀ f, L f → ∃ j, ∃ hj : retained S j, ∀ a b,
        chart S S.root (root_retained S) a = chart S j hj b ↔ f a b) ∧
      Conformal n (extractedEdges S) ∧ Chordal n (extractedEdges S) := by
  have hs := projection_surjective S R.realizes hzero (fun h hh => H.inv_mem hh) horbit
  have hpres : ∀ h : Equiv.Perm V, h ∈ H → P.IsInvariant T h := fun h hh => hH ⟨h,hh⟩
  refine ⟨extracted_finite S,hs,P.pull (projection S) T,ambientDescent S hs,
    ambientSection S R hzero,rfl,closed (projection S) hs T hT,
    ambientSection_rightInverse S R hzero hs,?_,ambientDescent_equivariant S hs,
    constructed_labelled_laws S R hs,retained_copy S P A0 T he hpres,
    image_action S P T hpres,extracted_cover S,real_group_preserves_copies S,
    extracted_transitive S R.ordinary,full_real_overlap S,?_,
    conformal_transfer S n hconf,chordal_transfer S n hchord⟩
  · intro h
    exact ⟨ambientSection S R hzero h,ambientSection_rightInverse S R hzero hs h⟩
  · intro f hf
    obtain ⟨h,hc⟩ := hlift f hf
    exact every_real_overlap S R.realizes f hf h.val h.property hc

end
end GluingEPPA.Reducts.AnchorUniformTheorem
