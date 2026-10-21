import GluingEPPA.Steiner.RecordValuation

/-!
# The inclusion into the current direct-record group

This implements the paragraph after Lemma 4.1. The first coordinates are
old inclusion/deletion homomorphisms; the second coordinates are right
actions supplied by that lemma. The resulting product homomorphism takes
old generators to new generators. Old word representations show that it
lands in the literal image group. Projection proves it injective.

The final lemmas derive the inclusion's own component action and extract
the restricted walk, exactly as in the manuscript. The recursive existence
of all the required earlier-stage data remains a separate obligation.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace DirectRecord

attribute [local instance] Classical.propDecidable

universe u v w z
variable {V : Type u} {E : Type v} {I : Type z}
variable (D : EdgeGraph V E) (T : I → Set E) (K : I → Type w)
variable [∀ i, Group (K i)]
variable (a : ∀ i, E → K i) (ha : ∀ i e, e ∈ T i → a i e * a i e = 1)

/-- Combine the group coordinates and the component actions, in the paper's order. -/
def coordinateHom (k : I) (f : ∀ i, K k →* K i)
    (A : ∀ i, RightAction (K k) (D.Component (T i) (a i) (ha i))) :
    K k →* Product D T K a ha where
  toFun g i := (f i g, MulOpposite.op ((A i).perm g))
  map_one' := by
    funext i
    apply Prod.ext
    · exact map_one (f i)
    · apply MulOpposite.unop_injective
      ext c
      exact (A i).one c
  map_mul' g h := by
    funext i
    apply Prod.ext
    · exact map_mul (f i) g h
    · apply MulOpposite.unop_injective
      ext c
      exact ((A i).mul c g h).symm

theorem coordinateHom_generator (k : I) (f : ∀ i, K k →* K i)
    (A : ∀ i, RightAction (K k) (D.Component (T i) (a i) (ha i)))
    (hf : ∀ i e, e ∈ T k → f i (a k e) = if e ∈ T i then a i e else 1)
    (hA : ∀ i e, e ∈ T k → ∀ c,
      (A i).act c (a k e) = D.componentEdgePerm (T i) (a i) (ha i) e c)
    (e : E) (he : e ∈ T k) :
    coordinateHom D T K a ha k f A (a k e) = letter D T K a ha e := by
  funext i
  apply Prod.ext
  · exact hf i e he
  · apply MulOpposite.unop_injective
    ext c
    exact hA i e he c

variable (k : I) (F : K k →* Product D T K a ha)
variable (hF : ∀ e ∈ T k, F (a k e) = letter D T K a ha e)

/-- The generator rule is valid for every allowed word. -/
theorem map_word (hF : ∀ e ∈ T k, F (a k e) = letter D T K a ha e)
    (w : List E) (hw : ∀ e ∈ w, e ∈ T k) :
    F ((w.map (a k)).prod) = value D T K a ha w := by
  induction w with
  | nil => simp only [List.map_nil, List.prod_nil, map_one, value_nil]
  | cons e w ih =>
      have he := hw e (by simp)
      have hw' : ∀ f ∈ w, f ∈ T k := fun f hf => hw f (by simp [hf])
      simp only [List.map_cons, List.prod_cons, map_mul, value_cons]
      rw [hF e he, ih hw']

variable (S : Set E) (hTS : T k ⊆ S)
variable (hgen : ∀ g : K k, ∃ w : List E,
  (∀ e ∈ w, e ∈ T k) ∧ (w.map (a k)).prod = g)

/-- The actual inclusion, with codomain restricted to the image of word records. -/
noncomputable def inclusion : K k →* imageGroup D T K a ha S where
  toFun g := ⟨F g, by
    obtain ⟨w, hw, hv⟩ := hgen g
    refine ⟨w, fun e he => hTS (hw e he), ?_⟩
    simpa only [hv] using (map_word D T K a ha k F hF w hw).symm⟩
  map_one' := Subtype.ext (map_one F)
  map_mul' g h := Subtype.ext (map_mul F g h)

/-- This is the manuscript's rule i_M^S(nu_M(w)) = nu_S(w). -/
theorem inclusion_word (w : List E) (hw : ∀ e ∈ w, e ∈ T k) :
    inclusion D T K a ha k F hF S hTS hgen ((w.map (a k)).prod) =
      valuation D T K a ha S w (fun e he => hTS (hw e he)) := by
  apply Subtype.ext
  exact map_word D T K a ha k F hF w hw

/-- The old group's own coordinate is a left inverse, without assuming a section. -/
theorem projection_inclusion (g : K k) :
    projection D T K a ha S k (inclusion D T K a ha k F hF S hTS hgen g) = g := by
  change (F g k).1 = g
  obtain ⟨w, hw, hv⟩ := hgen g
  have hFg : F g = value D T K a ha w := by
    simpa only [hv] using map_word D T K a ha k F hF w hw
  rw [hFg]
  change ((restrictWord (T k) w).map (a k)).prod = g
  rw [restrictWord_eq_of_letters (T k) w hw, hv]

theorem inclusion_injective :
    Function.Injective (inclusion D T K a ha k F hF S hTS hgen) := by
  intro g h heq
  have hp := congrArg (projection D T K a ha S k) heq
  simpa only [projection_inclusion] using hp

/-- The inclusion acts on its own smaller component coordinate by the deck action.
This is derived from the generator rule and old word representations; it is
not a new induction premise. -/
theorem inclusion_componentAction (g : K k)
    (c : D.Component (T k) (a k) (ha k)) :
    (coordinateAction D T K a ha S k).act c
        (inclusion D T K a ha k F hF S hTS hgen g) =
      D.componentRightAction (T k) (a k) (ha k) c g := by
  obtain ⟨w, hw, hv⟩ := hgen g
  have hact :
      (coordinateAction D T K a ha S k).act c
          (inclusion D T K a ha k F hF S hTS hgen ((w.map (a k)).prod)) =
        D.componentWordPerm (T k) (a k) (ha k) w c := by
    rw [inclusion_word D T K a ha k F hF S hTS hgen w hw]
    rfl
  have hdeck := D.componentAction_word (T k) (T k) (a k) (ha k) (a k)
    (D.componentGroupAction (T k) (a k) (ha k))
    (fun e he d => D.componentGroupAction_edge (T k) (a k) (ha k) he d)
    w hw c
  calc
    (coordinateAction D T K a ha S k).act c
        (inclusion D T K a ha k F hF S hTS hgen g) =
      D.componentWordPerm (T k) (a k) (ha k) w c := by
        simpa only [hv] using hact
    _ = D.componentRightAction (T k) (a k) (ha k) c ((w.map (a k)).prod) :=
      hdeck.symm
    _ = D.componentRightAction (T k) (a k) (ha k) c g := by rw [hv]

/-- Extract the exact restricted walk from the coordinate for the smaller set.
The premise is the coordinate formula for the newly constructed inclusion,
not an assumed restricted-walk conclusion. -/
theorem replacement_from_coordinate (S : Set E) (k : I)
    (j : K k → imageGroup D T K a ha S)
    (hj : ∀ c g, (coordinateAction D T K a ha S k).act c (j g) =
      D.componentRightAction (T k) (a k) (ha k) c g)
    {u v : V} (w : List E) (hw : ∀ e ∈ w, e ∈ S)
    (p : D.WordWalk S u w v) (g : K k)
    (hval : valuation D T K a ha S w hw = j g) :
    D.WalkValue (T k) (a k) u v g := by
  have hcomp : D.component (T k) (a k) (ha k) u g⁻¹ =
      D.component (T k) (a k) (ha k) v 1 := by
    calc
      D.component (T k) (a k) (ha k) u g⁻¹ =
          D.componentRightAction (T k) (a k) (ha k)
            (D.component (T k) (a k) (ha k) u 1) g := by
              simp only [D.componentRightAction_apply, mul_one]
      _ = (coordinateAction D T K a ha S k).act
          (D.component (T k) (a k) (ha k) u 1) (j g) := (hj _ g).symm
      _ = (coordinateAction D T K a ha S k).act
          (D.component (T k) (a k) (ha k) u 1)
          (valuation D T K a ha S w hw) := by rw [hval]
      _ = D.componentWordPerm (T k) (a k) (ha k) w
          (D.component (T k) (a k) (ha k) u 1) := rfl
      _ = D.component (T k) (a k) (ha k) v 1 :=
          D.componentWordPerm_walk (T k) (a k) (ha k) p
  have hp := (D.component_eq_iff_value (T k) (a k) (ha k) u v g⁻¹ 1).1 hcomp
  simpa only [inv_inv, mul_one] using hp

/-- Property (II) for the actual new inclusion, with its coordinate formula proved. -/
theorem inclusion_replacement {u v : V} (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (p : D.WordWalk S u w v) (g : K k)
    (hval : valuation D T K a ha S w hw =
      inclusion D T K a ha k F hF S hTS hgen g) :
    D.WalkValue (T k) (a k) u v g := by
  exact replacement_from_coordinate D T K a ha S k
    (inclusion D T K a ha k F hF S hTS hgen)
    (fun c g => inclusion_componentAction D T K a ha k F hF S hTS hgen g c)
    w hw p g hval

end DirectRecord
end EdgeGraph
end GluingEPPA.Steiner
