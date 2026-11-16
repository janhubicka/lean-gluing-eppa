import GluingEPPA.Reducts.AnchorExistenceReduction

/-!
A general finite-source-class reduct realization. Ambient symmetries preserve
only the reduct, not its source presentation. Naturality and class closure
are required ONLY for surjections between finite carriers. This matters when
Member is a class of finite structures: closure under arbitrary infinite
cloning would be an unnecessarily strong, often impossible premise.
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
universe u v w z

/-- The object map need obey naturality only on finite surjections. Its values
on other carriers play no role in the finite realization theorem. -/
structure FiniteSurjectiveReadout (P : Presentation.{u,v}) (Q : Presentation.{u,w}) where
  interpret : {X : Type u} → P.Obj X → Q.Obj X
  natural : ∀ {X Y : Type u} [Finite X] [Finite Y] (p : X → Y),
    Function.Surjective p → ∀ T : P.Obj Y,
      interpret (P.pull p T) = Q.pull p (interpret T)

namespace FiniteSurjectiveReadout

def ofSurjective {P : Presentation.{u,v}} {Q : Presentation.{u,w}}
    (F : SurjectiveReduct P Q) : FiniteSurjectiveReadout P Q where
  interpret := F.interpret
  natural := by
    intro X Y _ _ p hp T
    exact F.natural p hp T

def identity (P : Presentation.{u,v}) : FiniteSurjectiveReadout P P where
  interpret T := T
  natural := by intro X Y _ _ p hp T; rfl

/-- Successive permitted readouts again have the same uniform interface. -/
def comp {P : Presentation.{u,v}} {Q : Presentation.{u,w}} {R : Presentation.{u,z}}
    (F : FiniteSurjectiveReadout P Q) (G : FiniteSurjectiveReadout Q R) :
    FiniteSurjectiveReadout P R where
  interpret T := G.interpret (F.interpret T)
  natural := by
    intro X Y _ _ p hp T
    rw [F.natural p hp T, G.natural p hp (F.interpret T)]

/-- Stable presentation quotients enter the same readout theorem without
any choice of representatives or lifts of quotient automorphisms. -/
def quotient {P : Presentation.{u,v}} (C : StableCongruence P) :
    FiniteSurjectiveReadout P C.quotient where
  interpret {X} T := Quotient.mk (C.rel X) T
  natural := by intro X Y _ _ p hp T; rfl

end FiniteSurjectiveReadout

/-- The reduct class is the same-carrier image of a source class. No canonical
presentation or invariance of source membership under congruence is needed. -/
def ImageMember {P : Presentation.{u,v}} {Q : Presentation.{u,w}}
    (F : FiniteSurjectiveReadout P Q)
    (Member : {X : Type u} → P.Obj X → Prop)
    {X : Type u} (B : Q.Obj X) : Prop :=
  ∃ T : P.Obj X, Member T ∧ F.interpret T = B

theorem image_member_pullback {P : Presentation.{u,v}} {Q : Presentation.{u,w}}
    (F : FiniteSurjectiveReadout P Q)
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} [Finite X] [Finite Y] (p : X → Y),
      Function.Surjective p → ∀ T : P.Obj Y, Member T → Member (P.pull p T))
    {X Y : Type u} [Finite X] [Finite Y] (p : X → Y) (hp : Function.Surjective p)
    (B : Q.Obj Y) (hB : ImageMember F Member B) :
    ImageMember F Member (Q.pull p B) := by
  obtain ⟨T,hT,rfl⟩ := hB
  exact ⟨P.pull p T,closed p hp T hT,F.natural p hp T⟩

/-- Complete conditional reduct realization with a constructed source model.
There is no source-invariance premise, no closure under infinite cloning,
and no assertion that readout commutes with arbitrary restrictions. -/
theorem general_readout_theorem_from_set_realization
    {A V : Type u} [Finite A] [Finite V] [Nonempty V]
    (e : A ↪ V) (L : Rel A → Prop) (H : Subgroup (Equiv.Perm V))
    (n : Nat) (geo : GeometricPrinciple.{u} n) (hL : ClosedPartialFamily A L)
    (hlift : ∀ f, L f → ∃ h : H, Compatible e f h.val)
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, h ∈ H ∧ ∃ a : A, h (e a) = v)
    (P : Presentation.{u,v}) (Q : Presentation.{u,w}) (F : FiniteSurjectiveReadout P Q)
    (A0 : Q.Obj A) (T : P.Obj V)
    (he : Q.pull e (F.interpret T) = A0)
    (hH : ∀ h : H, Q.IsInvariant (F.interpret T) h.val)
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} [Finite X] [Finite Y] (p : X → Y),
      Function.Surjective p → ∀ B : P.Obj Y, Member B → Member (P.pull p B))
    (hT : Member T) :
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
  letI : Finite (Real S) := hfinite
  have hread : F.interpret (P.pull (projection S) T) = B :=
    (F.natural (projection S) hs T).trans hB.symm
  refine ⟨Z,J,S,R,hfinite,hs,P.pull (projection S) T,theta,sec,
    rfl,closed (projection S) hs T hT,F.natural (projection S) hs T,
    hsec,htheta,heq,hlaws,?_,?_,hcover,hperm,htrans,hover,hevery,hconf,hchord⟩
  · simpa only [hread] using hcopies
  · simpa only [hread] using hactions

theorem extracted_readout_in_image {P : Presentation.{u,v}} {Q : Presentation.{u,w}}
    (F : FiniteSurjectiveReadout P Q)
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} [Finite X] [Finite Y] (p : X → Y),
      Function.Surjective p → ∀ T : P.Obj Y, Member T → Member (P.pull p T))
    {X V : Type u} [Finite X] [Finite V] (p : X → V) (hp : Function.Surjective p)
    (T : P.Obj V) (hT : Member T) :
    ImageMember F Member (Q.pull p (F.interpret T)) :=
  image_member_pullback F Member closed p hp (F.interpret T) ⟨T,hT,rfl⟩

end
end GluingEPPA.Reducts.AnchorReadoutExistence
