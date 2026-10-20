import GluingEPPA.Steiner.RecursiveStep

/-!
# A finite group extension from compatible old coordinates

This is the simultaneous construction step, before the induction over finite
edge subsets. Old group/action homomorphisms are the output of the crossing
restriction argument. No new-group embedding or path membership is assumed.
-/

namespace GluingEPPA.Steiner.RecursiveStep

universe u v w z
attribute [local instance] Classical.propDecidable
variable {I : Type u} {V : Type v} {E : Type w}
variable (A : I → Type z) [∀ i, Group (A i)]
variable (T : ∀ i, Transport V (A i))
variable (R : I → Set E) (a : ∀ i, E → A i) (D : EdgeGraph V E)

/-- The coordinate homomorphisms already proved for the old groups. -/
structure CompatibleCoordinates where
  groups : ∀ r t, A r →* A t
  actions : ∀ r t, A r →* Equiv.Perm (T t).Space
  groups_on : ∀ r (e : R r) t,
    groups r t (a r e.val) = if e.val ∈ R t then a t e.val else 1
  actions_on : ∀ r (e : R r) t,
    actions r t (a r e.val) = (T t).edgePerm D (R t) (a t) e.val

variable (ha : ∀ i e, e ∈ R i → a i e * a i e = 1)

noncomputable abbrev NewGroup := GeneratedStep.Carrier (edgeValue A T R a D)
  (edgeValue_involutive A T R a D ha)

noncomputable def newGenerator (e : E) : NewGroup A T R a D ha :=
  GeneratedStep.generator (edgeValue A T R a D)
    (edgeValue_involutive A T R a D ha) e

theorem newGenerator_involutive (e : E) :
    newGenerator A T R a D ha e * newGenerator A T R a D ha e = 1 :=
  GeneratedStep.generator_involutive _ _ e

theorem newGroup_generated (g : NewGroup A T R a D ha) :
    ∃ w, wordValue (newGenerator A T R a D ha) w = g :=
  GeneratedStep.generated _ _ g

variable (hgen : ∀ i g, ∃ w : List (R i), wordValue (fun e => a i e.val) w = g)
variable (C : CompatibleCoordinates A T R a D)

noncomputable def oldInclusion (r : I) : A r →* NewGroup A T R a D ha :=
  GeneratedStep.inclusion (edgeValue A T R a D)
    (edgeValue_involutive A T R a D ha)
    (fun e : R r => a r e.val) (fun e : R r => e.val) (hgen r)
    (coordinateHom A T (C.groups r) (C.actions r))
    (fun e => coordinateHom_generator A T (C.groups r) (C.actions r)
      R a D (fun e : R r => a r e.val) (fun e : R r => e.val)
      (C.groups_on r) (C.actions_on r) e)

noncomputable def oldRetraction (r : I) : NewGroup A T R a D ha →* A r :=
  GeneratedStep.coordinate (edgeValue A T R a D)
    (edgeValue_involutive A T R a D ha) (groupProjection A T r)

noncomputable def quotientCoordinate (r : I) :
    NewGroup A T R a D ha →* Equiv.Perm (T r).Space :=
  GeneratedStep.coordinate (edgeValue A T R a D)
    (edgeValue_involutive A T R a D ha) (actionProjection A T r)

@[simp] theorem oldInclusion_generator (r : I) (e : R r) :
    oldInclusion A T R a D ha hgen C r (a r e.val) =
      newGenerator A T R a D ha e.val := by
  apply Subtype.ext
  change coordinateHom A T (C.groups r) (C.actions r) (a r e.val) =
    edgeValue A T R a D e.val
  exact coordinateHom_generator A T (C.groups r) (C.actions r)
    R a D (fun e : R r => a r e.val) (fun e : R r => e.val)
    (C.groups_on r) (C.actions_on r) e

@[simp] theorem oldRetraction_generator (r : I) (e : E) :
    oldRetraction A T R a D ha r (newGenerator A T R a D ha e) =
      if e ∈ R r then a r e else 1 := rfl

@[simp] theorem quotientCoordinate_generator (r : I) (e : E) :
    quotientCoordinate A T R a D ha r (newGenerator A T R a D ha e) =
      (T r).edgePerm D (R r) (a r) e := rfl

/-- The regular coordinate proves injectivity for every old group simultaneously. -/
theorem oldRetraction_leftInverse (r : I) :
    Function.LeftInverse (oldRetraction A T R a D ha r)
      (oldInclusion A T R a D ha hgen C r) := by
  have hid : (oldRetraction A T R a D ha r).comp
      (oldInclusion A T R a D ha hgen C r) = MonoidHom.id (A r) := by
    apply hom_ext_of_words (fun e : R r => a r e.val) (hgen r)
    intro e
    change oldRetraction A T R a D ha r
      (oldInclusion A T R a D ha hgen C r (a r e.val)) = a r e.val
    rw [oldInclusion_generator, oldRetraction_generator, ite_eq_left e.property]
  intro g
  exact DFunLike.congr_fun hid g

theorem oldInclusion_injective (r : I) :
    Function.Injective (oldInclusion A T R a D ha hgen C r) :=
  (oldRetraction_leftInverse A T R a D ha hgen C r).injective

theorem quotientCoordinate_inclusion (r : I) (g : A r) :
    quotientCoordinate A T R a D ha r
      (oldInclusion A T R a D ha hgen C r g) = (T r).action g := by
  have heq : (quotientCoordinate A T R a D ha r).comp
      (oldInclusion A T R a D ha hgen C r) = (T r).action := by
    apply hom_ext_of_words (fun e : R r => a r e.val) (hgen r)
    intro e
    change quotientCoordinate A T R a D ha r
      (oldInclusion A T R a D ha hgen C r (a r e.val)) = (T r).action (a r e.val)
    rw [oldInclusion_generator, quotientCoordinate_generator]
    simp only [Transport.edgePerm, ite_eq_left e.property]
  exact DFunLike.congr_fun heq g

/-- Property (ii) for the group actually constructed by the product step. -/
theorem new_walk_replacement
    (hstep : ∀ r e, e ∈ R r → ∀ u v, D.Joins e u v → (T r).Rel u v (a r e))
    (r : I) {u v : V} {k : NewGroup A T R a D ha} {g : A r}
    (p : D.WalkValue Set.univ (newGenerator A T R a D ha) u v k)
    (hk : k = oldInclusion A T R a D ha hgen C r g) : (T r).Rel u v g := by
  apply (T r).replacement_of_coordinate D Set.univ (newGenerator A T R a D ha)
    (fun e _ => newGenerator_involutive A T R a D ha e)
    (oldInclusion A T R a D ha hgen C r)
    (quotientCoordinate A T R a D ha r) ?_ ?_ p hk
  · exact quotientCoordinate_inclusion A T R a D ha hgen C r
  · intro e _ u v hj
    rw [quotientCoordinate_generator]
    exact (T r).edgePerm_endpoint D (R r) (a r) (ha r) (hstep r) hj

end GluingEPPA.Steiner.RecursiveStep
