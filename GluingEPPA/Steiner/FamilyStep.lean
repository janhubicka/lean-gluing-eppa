import GluingEPPA.Steiner.FamilyActions

/-!
# Complete one-stage extension of an old Steiner transport family

The old masks are indexed by I. From their named generators, inclusions,
deletions, walk membership, and actions on strictly smaller quotients, the
preceding files construct every compatible coordinate. We now apply the
finite product to obtain the new group, all embeddings and retractions,
and replacement of any full walk whose value comes from an old group.

This is the induction STEP. Constructing the whole family by well-founded
recursion over the proper edge subsets remains separate.
-/

namespace GluingEPPA.Steiner.RecursiveStep

universe u v w z
variable {I : Type u} {V : Type v} {E : Type w}
variable (A : I → Type z) [∀ i, Group (A i)]
variable (T : ∀ i, Transport V (A i))
variable (R : I → Set E) (a : ∀ i, E → A i) (D : EdgeGraph V E)
variable (F : OldGroupMaps A R a)
variable (C : OldWalkActions A T R a D F)

noncomputable abbrev NextGroup := NewGroup A T R a D C.involutive

noncomputable def nextInclusion (r : I) : A r →* NextGroup A T R a D F C :=
  oldInclusion A T R a D C.involutive C.generated
    (OldWalkActions.compatible A T R a D F C) r

noncomputable def nextRetraction (r : I) : NextGroup A T R a D F C →* A r :=
  oldRetraction A T R a D C.involutive r

@[simp] theorem nextInclusion_generator (r : I) (e : R r) :
    nextInclusion A T R a D F C r (a r e.val) =
      newGenerator A T R a D C.involutive e.val :=
  oldInclusion_generator A T R a D C.involutive C.generated
    (OldWalkActions.compatible A T R a D F C) r e

@[simp] theorem nextRetraction_generator (r : I) (e : E) :
    nextRetraction A T R a D F C r
      (newGenerator A T R a D C.involutive e) =
      if e ∈ R r then a r e else 1 :=
  oldRetraction_generator A T R a D C.involutive r e

theorem nextRetraction_leftInverse (r : I) :
    Function.LeftInverse (nextRetraction A T R a D F C r)
      (nextInclusion A T R a D F C r) :=
  oldRetraction_leftInverse A T R a D C.involutive C.generated
    (OldWalkActions.compatible A T R a D F C) r

theorem nextInclusion_injective (r : I) :
    Function.Injective (nextInclusion A T R a D F C r) :=
  (nextRetraction_leftInverse A T R a D F C r).injective

theorem nextGroup_finite [Finite I] [Finite V] [∀ i, Finite (A i)] :
    Finite (NextGroup A T R a D F C) :=
  generated_finite A T R a D C.involutive

theorem nextGroup_generated (g : NextGroup A T R a D F C) :
    ∃ w, wordValue (newGenerator A T R a D C.involutive) w = g :=
  newGroup_generated A T R a D C.involutive g

/-- The actual-walk replacement at the newly constructed stage. -/
theorem nextWalkReplacement
    (hstep : ∀ r e, e ∈ R r → ∀ u v, D.Joins e u v → (T r).Rel u v (a r e))
    (r : I) {u v : V} {k : NextGroup A T R a D F C} {g : A r}
    (p : D.WalkValue Set.univ (newGenerator A T R a D C.involutive) u v k)
    (hk : k = nextInclusion A T R a D F C r g) : (T r).Rel u v g :=
  new_walk_replacement A T R a D C.involutive C.generated
    (OldWalkActions.compatible A T R a D F C) hstep r p hk

end GluingEPPA.Steiner.RecursiveStep
