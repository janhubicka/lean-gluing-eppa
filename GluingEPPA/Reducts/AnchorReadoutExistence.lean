import GluingEPPA.Reducts.AnchorExistenceReduction

/-!
The general existence reduction for a surjective-natural reduct readout.
Ambient permutations need preserve only the reduct, NOT the source presentation.
Only surjective source pullbacks are required to preserve the source class.
The source structure, target readout, exact overlaps, local copy geometry,
split ambient action and all labelled coherent lifts are produced together.
The set-geometric existence principle is still an explicit hypothesis.
-/
namespace GluingEPPA.Reducts.AnchorReadoutExistence
open GluingEPPA.Reducts.AnchorExtraction
open GluingEPPA.Reducts.AnchorFamily
open GluingEPPA.Reducts.AnchorGeometry
open GluingEPPA.Reducts.AnchorGeneralTheorem
open GluingEPPA.Reducts.AnchorLabelledCoherence
open GluingEPPA.Reducts.AnchorUniformTheorem
open GluingEPPA.Reducts.AnchorExistenceReduction
open GluingEPPA.Reducts.PullbackPresentations
noncomputable section
universe u v w

/-- The reduct class is the same-carrier image of a source class. This
existential definition requires no choice of a canonical presentation. -/
def ImageMember {P : Presentation.{u,v}} {Q : Presentation.{u,w}}
    (F : SurjectiveReduct P Q)
    (Member : {X : Type u} → P.Obj X → Prop)
    {X : Type u} (B : Q.Obj X) : Prop :=
  ∃ T : P.Obj X, Member T ∧ F.interpret T = B

theorem image_member_pullback {P : Presentation.{u,v}} {Q : Presentation.{u,w}}
    (F : SurjectiveReduct P Q)
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} (p : X → Y), Function.Surjective p →
      ∀ T : P.Obj Y, Member T → Member (P.pull p T))
    {X Y : Type u} (p : X → Y) (hp : Function.Surjective p)
    (B : Q.Obj Y) (hB : ImageMember F Member B) :
    ImageMember F Member (Q.pull p B) := by
  obtain ⟨T,hT,rfl⟩ := hB
  exact ⟨P.pull p T,closed p hp T hT,F.natural p hp T⟩

/-- Complete conditional reduct realization with a constructed source model.
There is deliberately no source-invariance premise and no claim that the
readout commutes with restricting to an arbitrary induced substructure. -/
theorem general_readout_theorem_from_set_realization
    {A V : Type u} [Finite A] [Finite V] [Nonempty V]
    (e : A ↪ V) (L : Rel A → Prop) (H : Subgroup (Equiv.Perm V))
    (n : Nat) (geo : GeometricPrinciple.{u} n) (hL : ClosedPartialFamily A L)
    (hlift : ∀ f, L f → ∃ h : H, Compatible e f h.val)
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, h ∈ H ∧ ∃ a : A, h (e a) = v)
    (P : Presentation.{u,v}) (Q : Presentation.{u,w}) (F : SurjectiveReduct P Q)
    (A0 : Q.Obj A) (T : P.Obj V)
    (he : Q.pull e (F.interpret T) = A0)
    (hH : ∀ h : H, Q.IsInvariant (F.interpret T) h.val)
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} (p : X → Y), Function.Surjective p →
      ∀ B : P.Obj Y, Member B → Member (P.pull p B)) (hT : Member T) :
    ∃ (Z J : Type u) (S : System e L (fun h => h ∈ H) Z J) (R : CoherentRaw S),
    Finite (Real S) ∧ Function.Surjective (projection S) ∧
    ∃ T' : P.Obj (Real S), ∃ theta : RealGroup S →* H, ∃ sec : H →* RealGroup S,
      T' = P.pull (projection S) T ∧ Member T' ∧
      F.interpret T' = Q.pull (projection S) (F.interpret T) ∧
      (∀ h, theta (sec h) = h) ∧ Function.Surjective theta ∧
      (∀ g y, projection S (g.val y) = (theta g).val (projection S y)) ∧
      LabelledLaws S theta (labelledLift S R) ∧
      (∀ j (hj : retained S j), Q.IsEmbedding A0 (F.interpret T') (chart S j hj)) ∧
      (∀ g : RealGroup S, Q.IsInvariant (F.interpret T') g.val) ∧
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
  obtain ⟨Z,J,S,R,hfinite,hs,B,theta,sec,hB,_,hsec,htheta,heq,hlaws,
    hcopies,hactions,hcover,hperm,htrans,hover,hevery,hconf,hchord⟩ :=
    general_theorem_from_set_realization e L H n geo hL hlift horbit
      Q A0 (F.interpret T) he hH (fun {_} _ => True)
      (fun {_ _} _ _ _ _ => True.intro) True.intro
  have hread : F.interpret (P.pull (projection S) T) = B :=
    (F.natural (projection S) hs T).trans hB.symm
  refine ⟨Z,J,S,R,hfinite,hs,P.pull (projection S) T,theta,sec,
    rfl,closed (projection S) hs T hT,F.natural (projection S) hs T,
    hsec,htheta,heq,hlaws,?_,?_,hcover,hperm,htrans,hover,hevery,hconf,hchord⟩
  · simpa only [hread] using hcopies
  · simpa only [hread] using hactions

/-- The ambient action may fail to preserve its presentation. The conclusion
still places the output reduct in the image of the stipulated source class. -/
theorem extracted_readout_in_image {P : Presentation.{u,v}} {Q : Presentation.{u,w}}
    (F : SurjectiveReduct P Q)
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} (p : X → Y), Function.Surjective p →
      ∀ T : P.Obj Y, Member T → Member (P.pull p T))
    {X V : Type u} (p : X → V) (hp : Function.Surjective p)
    (T : P.Obj V) (hT : Member T) :
    ImageMember F Member (Q.pull p (F.interpret T)) :=
  image_member_pullback F Member closed p hp (F.interpret T) ⟨T,hT,rfl⟩

end
end GluingEPPA.Reducts.AnchorReadoutExistence
