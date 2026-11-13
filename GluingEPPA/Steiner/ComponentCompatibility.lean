import GluingEPPA.Steiner.ComponentInclusion
import GluingEPPA.Steiner.RightAction

/-!
# The two-part action in current-manuscript Lemma 4.1

The component sets and their injection are the actual Cayley components.
On the image of j_N^T we transport the already constructed coordinate action
of K_M on C_N. On the complement we use inverse left translation through
 i_N^T r_N^M. Both are group actions, and their generators agree with tau_e^T.
Consequently *arbitrary* equal-valued M-words act equally on all of C_T.

The earlier coordinate action, deletion map, and exact-walk replacement are
explicit induction inputs. This file does not assert their recursive
existence. The subsequent direct-record induction must supply these inputs.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

attribute [local instance] Classical.propDecidable

universe u v w z t
variable {V : Type u} {E : Type v}
variable {G : Type w} {H : Type z} {K : Type t}
variable [Group G] [Group H] [Group K]
variable (D : EdgeGraph V E)

/-- Package exactly the manuscript's deck-induced right action. -/
def componentGroupAction (T : Set E) (b : E → H)
    (hb : ∀ e ∈ T, b e * b e = 1) : RightAction H (D.Component T b hb) where
  act := D.componentRightAction T b hb
  one := D.componentRightAction_one T b hb
  mul := D.componentRightAction_mul T b hb

theorem componentGroupAction_edge (T : Set E) (b : E → H)
    (hb : ∀ e ∈ T, b e * b e = 1) {e : E} (he : e ∈ T)
    (c : D.Component T b hb) :
    (D.componentGroupAction T b hb).act c (b e) = D.componentEdgePerm T b hb e c := by
  have hi : (b e)⁻¹ = b e := by
    calc
      (b e)⁻¹ = (b e)⁻¹ * 1 := (mul_one _).symm
      _ = (b e)⁻¹ * (b e * b e) := by rw [hb e he]
      _ = b e := by group
  rw [D.componentEdgePerm_of_mem T b hb he]
  change D.componentTranslation T b hb (b e)⁻¹ c =
    D.componentTranslation T b hb (b e) c
  rw [hi]

/-- The first case of Lemma 4.1: pull back the earlier deck action. -/
theorem componentGroupAction_comap_edge (M T : Set E) (hMT : M ⊆ T)
    (a : E → G) (b : E → H) (hb : ∀ e ∈ T, b e * b e = 1)
    (i : G →* H) (hi : ∀ e ∈ M, i (a e) = b e)
    {e : E} (he : e ∈ M) (c : D.Component T b hb) :
    ((D.componentGroupAction T b hb).comap i).act c (a e) =
      D.componentEdgePerm T b hb e c := by
  change (D.componentGroupAction T b hb).act c (i (a e)) = _
  rw [hi e he]
  exact D.componentGroupAction_edge T b hb (hMT he) c

variable (N T : Set E) (a : E → G) (b : E → H)
variable (ha : ∀ e ∈ N, a e * a e = 1) (hb : ∀ e ∈ T, b e * b e = 1)
variable (hNT : N ⊆ T) (i : G →* H) (hi : ∀ e ∈ N, i (a e) = b e)
variable (hreplace : ∀ u v g, D.WalkValue T b u v (i g) → D.WalkValue N a u v g)
variable (r : K →* G) (A : RightAction K (D.Component N a ha))

/-- The manuscript's two actions glued along the injective j_N^T. -/
noncomputable def componentCompatibilityAction : RightAction K (D.Component T b hb) :=
  RightAction.glue A ((D.componentGroupAction T b hb).comap (i.comp r))
    (D.componentMap N T a b ha hb hNT i hi)
    (D.componentMap_injective N T a b ha hb hNT i hi hreplace)
    (by
      intro c g
      change D.componentTranslation T b hb (i (r g))⁻¹ c ∈
          Set.range (D.componentMap N T a b ha hb hNT i hi) ↔
        c ∈ Set.range (D.componentMap N T a b ha hb hNT i hi)
      simpa only [map_inv] using
        (D.componentMap_range_translation N T a b ha hb hNT i hi (r g)⁻¹ c))

/-- On Y the action is the earlier coordinate action, transported through j. -/
theorem componentCompatibilityAction_image (c : D.Component N a ha) (g : K) :
    (D.componentCompatibilityAction N T a b ha hb hNT i hi hreplace r A).act
        (D.componentMap N T a b ha hb hNT i hi c) g =
      D.componentMap N T a b ha hb hNT i hi (A.act c g) := by
  unfold componentCompatibilityAction
  exact RightAction.glue_apply_image _ _ _ _ _ c g

/-- On the complement it is inverse left translation through i composed with r. -/
theorem componentCompatibilityAction_outside (c : D.Component T b hb)
    (hc : c ∉ Set.range (D.componentMap N T a b ha hb hNT i hi)) (g : K) :
    (D.componentCompatibilityAction N T a b ha hb hNT i hi hreplace r A).act c g =
      D.componentRightAction T b hb c (i (r g)) := by
  unfold componentCompatibilityAction
  exact RightAction.glue_apply_outside _ _ _ _ _ hc g

/-- Every named generator has exactly the prescribed action on every component. -/
theorem componentCompatibilityAction_edge (M : Set E) (hN : N = M ∩ T)
    (m : E → K)
    (hr : ∀ e ∈ M, r (m e) = if e ∈ N then a e else 1)
    (hA : ∀ e ∈ M, ∀ c, A.act c (m e) = D.componentEdgePerm N a ha e c)
    {e : E} (he : e ∈ M) (c : D.Component T b hb) :
    (D.componentCompatibilityAction N T a b ha hb hNT i hi hreplace r A).act
        c (m e) = D.componentEdgePerm T b hb e c := by
  classical
  have heN : e ∈ T → e ∈ N := fun ht => by rw [hN]; exact ⟨he, ht⟩
  by_cases hc : c ∈ Set.range (D.componentMap N T a b ha hb hNT i hi)
  · obtain ⟨x, rfl⟩ := hc
    rw [D.componentCompatibilityAction_image, hA e he]
    apply D.componentMap_edgePerm N T a b ha hb hNT i hi hreplace
    by_cases ht : e ∈ T
    · exact Or.inl (heN ht)
    · exact Or.inr ht
  · rw [D.componentCompatibilityAction_outside N T a b ha hb hNT i hi hreplace r A c hc]
    by_cases ht : e ∈ T
    · have hn := heN ht
      rw [hr e he, if_pos hn, hi e hn]
      exact D.componentGroupAction_edge T b hb ht c
    · have hn : e ∉ N := fun h => ht (hNT h)
      rw [hr e he, if_neg hn, map_one, D.componentRightAction_one]
      symm
      apply D.componentEdgePerm_external_fixed T b hb ht c
      · intro heq
        apply hc
        rw [heq]
        exact D.distinguished_mem_componentMap_range N T a b ha hb hNT i hi _
      · intro heq
        apply hc
        rw [heq]
        exact D.distinguished_mem_componentMap_range N T a b ha hb hNT i hi _

/-- Generator agreement propagates to every word, not only to actual walks. -/
theorem componentAction_word (M T : Set E) (b : E → H)
    (hb : ∀ e ∈ T, b e * b e = 1) (m : E → K)
    (B : RightAction K (D.Component T b hb))
    (hB : ∀ e ∈ M, ∀ c, B.act c (m e) = D.componentEdgePerm T b hb e c)
    (w : List E) (hw : ∀ e ∈ w, e ∈ M) (c : D.Component T b hb) :
    B.act c ((w.map m).prod) = D.componentWordPerm T b hb w c := by
  induction w generalizing c with
  | nil => simpa only [List.map_nil, List.prod_nil, componentWordPerm_nil] using B.one c
  | cons e w ih =>
      have he : e ∈ M := hw e (by simp)
      have hw' : ∀ f ∈ w, f ∈ M := fun f hf => hw f (by simp [hf])
      simp only [List.map_cons, List.prod_cons, componentWordPerm_cons]
      rw [← B.mul, hB e he]
      exact ih hw' (D.componentEdgePerm T b hb e c)

/-- All old word equalities hold on the whole new component set. -/
theorem componentWordPerm_equal_of_value_equal (M T : Set E) (b : E → H)
    (hb : ∀ e ∈ T, b e * b e = 1) (m : E → K)
    (B : RightAction K (D.Component T b hb))
    (hB : ∀ e ∈ M, ∀ c, B.act c (m e) = D.componentEdgePerm T b hb e c)
    (p q : List E) (hp : ∀ e ∈ p, e ∈ M) (hq : ∀ e ∈ q, e ∈ M)
    (hval : (p.map m).prod = (q.map m).prod) :
    D.componentWordPerm T b hb p = D.componentWordPerm T b hb q := by
  ext c
  rw [← D.componentAction_word M T b hb m B hB p hp c,
    ← D.componentAction_word M T b hb m B hB q hq c, hval]

end EdgeGraph
end GluingEPPA.Steiner
