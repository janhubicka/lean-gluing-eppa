import GluingEPPA.Reducts.AnchorUniformTheorem
import Mathlib.Data.Fintype.Sum

/-! The general theorem as an implication from a single set-realization
principle. Closure of the decorated family and all output data are derived.
The geometric principle is an explicit hypothesis, never a new axiom. -/
namespace GluingEPPA.Reducts.AnchorExistenceReduction
open GluingEPPA.Reducts.AnchorExtraction
open GluingEPPA.Reducts.AnchorFamily
open GluingEPPA.Reducts.AnchorGeometry
open GluingEPPA.Reducts.AnchorGeneralTheorem
open GluingEPPA.Reducts.AnchorLabelledCoherence
open GluingEPPA.Reducts.AnchorUniformTheorem
open GluingEPPA.Reducts.PullbackPresentations
noncomputable section
universe u v

structure ClosedPartialFamily (X : Type u) (F : Rel X → Prop) : Prop where
  partial : ∀ f, F f → PartialBijection f
  identity : F (relId X)
  empty : F (emptyRel X)
  inverse : ∀ f, F f → F (relInv f)
  composition : ∀ f g, F f → F g → F (relComp f g)

/-- An incoming set-theoretic realization, before any structure or projection
has been supplied. The hyperedges are exactly the images of the copies. -/
structure GeometricRealization (X : Type u) (F : Rel X → Prop) (n : Nat) where
  Z : Type u
  J : Type u
  finiteCarrier : Finite Z
  copy : J → (X ↪ Z)
  root : J
  cover : ∀ z, ∃ j x, copy j x = z
  overlap : ∀ j k, F (fun x y => copy j x = copy k y)
  realizes : ∀ f, F f → ∃ j, ∀ x y, copy root x = copy j y ↔ f x y
  transitive : ∀ j k, ∃ p : Equiv.Perm Z,
    ((∀ i, ∃ l, ∀ x, p (copy i x) = copy l x) ∧
     (∀ i, ∃ l, ∀ x, p.symm (copy i x) = copy l x)) ∧
    ∀ x, p (copy j x) = copy k x
  extend : (f : Rel X) → F f → Equiv.Perm Z
  copies : ∀ f hf,
    (∀ i, ∃ j, ∀ x, extend f hf (copy i x) = copy j x) ∧
    (∀ i, ∃ j, ∀ x, (extend f hf).symm (copy i x) = copy j x)
  agrees : ∀ f hf x y, f x y → extend f hf (copy root x) = copy root y
  identity : ∀ D (hf : F (partialId D)), extend (partialId D) hf = 1
  composition : ∀ f g hf hg (hfg : F (relComp f g)), Matching f g →
    extend (relComp f g) hfg = extend g hg * extend f hf
  conformal : Conformal n (fun j z => ∃ x, copy j x = z)
  chordal : Chordal n (fun j z => ∃ x, copy j x = z)

/-- The external Part II dependency is an ordinary proposition parameter. -/
def GeometricPrinciple (n : Nat) : Prop :=
  ∀ (X : Type u) [Finite X] (F : Rel X → Prop),
    ClosedPartialFamily X F → Nonempty (GeometricRealization X F n)

variable {A V : Type u} (e : A ↪ V) (L : Rel A → Prop) (H : Subgroup (Equiv.Perm V))

theorem decorated_closed (hL : ClosedPartialFamily A L) :
    ClosedPartialFamily (Sum A V) (Allowed e L (fun h => h ∈ H)) := by
  refine ⟨allowed_partial e L _ hL.partial,
    allowed_identity e L _ hL.identity H.one_mem,
    allowed_empty e L _,
    allowed_inverse e L _ hL.inverse (fun h hh => H.inv_mem hh), ?_⟩
  exact allowed_composition e L _ hL.composition
    (fun h k hh hk => H.mul_mem hk hh)

def asAnchor {n : Nat}
    (R : GeometricRealization (Sum A V) (Allowed e L (fun h => h ∈ H)) n) :
    System e L (fun h => h ∈ H) R.Z R.J where
  copy := R.copy
  root := R.root
  overlap_allowed := R.overlap

def asCoherentRaw {n : Nat} [Nonempty V]
    (R : GeometricRealization (Sum A V) (Allowed e L (fun h => h ∈ H)) n) :
    CoherentRaw (asAnchor e L H R) where
  realizes := R.realizes
  transitive := R.transitive
  extend := R.extend
  copies := R.copies
  agrees := R.agrees
  identity := R.identity
  composition := R.composition

/-- A uniform existence reduction, with no supplied output realization.
The only external existence hypothesis is the general set-geometric principle.
All admissible-family conditions are on the original partial maps. -/
theorem general_theorem_from_set_realization [Finite A] [Finite V] [Nonempty V]
    (n : Nat) (geo : GeometricPrinciple.{u} n) (hL : ClosedPartialFamily A L)
    (hlift : ∀ f, L f → ∃ h : H, Compatible e f h.val)
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, h ∈ H ∧ ∃ a : A, h (e a) = v)
    (P : Presentation.{u,v}) (A0 : P.Obj A) (T : P.Obj V)
    (he : P.pull e T = A0) (hH : ∀ h : H, P.IsInvariant T h.val)
    (Member : {X : Type u} → P.Obj X → Prop)
    (closed : ∀ {X Y : Type u} (p : X → Y), Function.Surjective p →
      ∀ B : P.Obj Y, Member B → Member (P.pull p B)) (hT : Member T) :
    ∃ (Z J : Type u) (S : System e L (fun h => h ∈ H) Z J) (R : CoherentRaw S),
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
  obtain ⟨r⟩ := geo (Sum A V) (Allowed e L (fun h => h ∈ H)) (decorated_closed e L H hL)
  let S := asAnchor e L H r
  let R := asCoherentRaw e L H r
  letI : Finite r.Z := r.finiteCarrier
  exact ⟨r.Z,r.J,S,R,
    general_structured_labelled_refinement S R hL.empty hlift horbit n
      r.conformal r.chordal P A0 T he hH Member closed hT⟩

end
end GluingEPPA.Reducts.AnchorExistenceReduction
