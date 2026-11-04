import GluingEPPA.Steiner.ChainValuation.PushoutFunctor

/-!
# Exact inclusion of matched restricted pieces into a full pushout

Suppose the two sides of an injective attachment have chosen subsets
U and V, and an attaching point lies in U exactly when its partner
lies in V. Restrict the interface to these points and glue precisely
these *restricted* pieces.

The resulting restricted pushout injects into the original full
pushout and its image is exactly the union of the images of U and V.
This is stronger than a surjective map from an abstract cover and
is the elementary exactness statement needed when normalizing one
component's two adjacent restricted Cayley cosets.

Nothing in this module asserts that an arbitrary subset is an
M-component: that conclusion follows only after the earlier Link
component-matching and historical-chart theorems.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable {f : Z → X} {g : Z → Y}

/-- A pair of subsets with exactly matching preimages on the
common attaching space. -/
structure MatchedRestriction (f : Z → X) (g : Z → Y) where
  left : Set X
  right : Set Y
  agree : ∀ z : Z, f z ∈ left ↔ g z ∈ right

namespace MatchedRestriction

variable (R : MatchedRestriction f g)

abbrev Left := {x : X // x ∈ R.left}
abbrev Right := {y : Y // y ∈ R.right}
abbrev Interface := {z : Z // f z ∈ R.left}

def leftAttach : R.Interface → R.Left :=
  fun z => ⟨f z.val, z.property⟩

def rightAttach : R.Interface → R.Right :=
  fun z => ⟨g z.val, (R.agree z.val).mp z.property⟩

theorem leftAttach_injective (hf : Function.Injective f) :
    Function.Injective R.leftAttach := by
  intro z z' h
  apply Subtype.ext
  exact hf (congrArg Subtype.val h)

theorem rightAttach_injective (hg : Function.Injective g) :
    Function.Injective R.rightAttach := by
  intro z z' h
  apply Subtype.ext
  exact hg (congrArg Subtype.val h)

/-- The exact set-pushout of the two selected pieces, glued
only along their common selected interface. -/
abbrev Space (hf : Function.Injective f) (hg : Function.Injective g) :=
  SetPushout R.leftAttach R.rightAttach
    (R.leftAttach_injective hf) (R.rightAttach_injective hg)

/-- The obvious map into the complete original pushout. -/
def intoFull (hf : Function.Injective f) (hg : Function.Injective g) :
    R.Space hf hg → SetPushout f g hf hg :=
  pushoutMap R.leftAttach R.rightAttach
    (R.leftAttach_injective hf) (R.rightAttach_injective hg)
    f g hf hg
    Subtype.val Subtype.val Subtype.val
    (fun z => rfl) (fun z => rfl)

/-- An inclusion of the exact restricted pushout into the entire
pushout cannot identify points. The key is the exact attachment
relation in the quotient, plus agreement of interface preimages. -/
theorem intoFull_injective (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Injective (R.intoFull hf hg) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro t s h
  have hFull :
      pushoutRel f g
        (pushoutSumMap (Subtype.val : R.Left → X)
          (Subtype.val : R.Right → Y) t)
        (pushoutSumMap (Subtype.val : R.Left → X)
          (Subtype.val : R.Right → Y) s) :=
    Quotient.exact h
  apply Quotient.sound
  cases t with
  | inl x =>
      cases s with
      | inl y =>
          change x.val = y.val at hFull
          change x = y
          exact Subtype.ext hFull
      | inr y =>
          change ∃ z : Z, f z = x.val ∧ g z = y.val at hFull
          obtain ⟨z, hx, hy⟩ := hFull
          refine ⟨⟨z, ?_⟩, ?_, ?_⟩
          · rw [hx]
            exact x.property
          · apply Subtype.ext
            exact hx
          · apply Subtype.ext
            exact hy
  | inr x =>
      cases s with
      | inl y =>
          change ∃ z : Z, g z = x.val ∧ f z = y.val at hFull
          obtain ⟨z, hx, hy⟩ := hFull
          refine ⟨⟨z, ?_⟩, ?_, ?_⟩
          · rw [hy]
            exact y.property
          · apply Subtype.ext
            exact hx
          · apply Subtype.ext
            exact hy
      | inr y =>
          change x.val = y.val at hFull
          change x = y
          exact Subtype.ext hFull

/-- Exactly the points of the full quotient represented by one of
the selected pieces. -/
def Covered (hf : Function.Injective f) (hg : Function.Injective g) :
    Set (SetPushout f g hf hg) :=
  {q | (∃ x : R.Left, pushoutInl f g hf hg x.val = q) ∨
        (∃ y : R.Right, pushoutInr f g hf hg y.val = q)}

/-- The exact restricted pushout lands in the specified union. -/
theorem intoFull_mem_covered (hf : Function.Injective f)
    (hg : Function.Injective g) (q : R.Space hf hg) :
    R.intoFull hf hg q ∈ R.Covered hf hg := by
  refine Quotient.inductionOn q ?_
  intro t
  cases t with
  | inl x =>
      exact Or.inl ⟨x, rfl⟩
  | inr y =>
      exact Or.inr ⟨y, rfl⟩

/-- Conversely, the image is the entire union of the two
restricted pieces, including all points in their overlap. -/
theorem intoFull_surjective_covered (hf : Function.Injective f)
    (hg : Function.Injective g) :
    ∀ q : {q : SetPushout f g hf hg // q ∈ R.Covered hf hg},
      ∃ p : R.Space hf hg, R.intoFull hf hg p = q.val := by
  rintro ⟨q, hq⟩
  rcases hq with ⟨x, hx⟩ | ⟨y, hy⟩
  · refine ⟨pushoutInl R.leftAttach R.rightAttach
      (R.leftAttach_injective hf) (R.rightAttach_injective hg) x, ?_⟩
    change pushoutInl f g hf hg x.val = q
    exact hx
  · refine ⟨pushoutInr R.leftAttach R.rightAttach
      (R.leftAttach_injective hf) (R.rightAttach_injective hg) y, ?_⟩
    change pushoutInr f g hf hg y.val = q
    exact hy

/-- The exact restricted quotient is *equivalent*, not merely
surjectively mapped, to the union of its selected component pieces. -/
noncomputable def equivCovered (hf : Function.Injective f)
    (hg : Function.Injective g) :
    R.Space hf hg ≃
      {q : SetPushout f g hf hg // q ∈ R.Covered hf hg} := by
  let F : R.Space hf hg →
      {q : SetPushout f g hf hg // q ∈ R.Covered hf hg} :=
    fun q => ⟨R.intoFull hf hg q, R.intoFull_mem_covered hf hg q⟩
  apply Equiv.ofBijective F
  constructor
  · intro x y h
    apply R.intoFull_injective hf hg
    exact congrArg Subtype.val h
  · intro q
    obtain ⟨x, hx⟩ := R.intoFull_surjective_covered hf hg q
    exact ⟨x, Subtype.ext hx⟩

end MatchedRestriction
end GluingEPPA.Steiner.ChainValuation
