import GluingEPPA.Sparsening.TreeFullA

/-!
# Changing the base of a strict full-A tree

An isomorphism of the base changes neither the target carrier nor its
relations or unary fibres. At a leaf, compose the full-copy embedding.
At a gluing, insert the base isomorphism and its inverse on either side
of each root map. They cancel, so the actual pushout is unchanged.
-/

namespace GluingEPPA.Sparsening.Tree

universe u v w t
variable {L : Nat → Type u} {F : Type t}

namespace ExactUnaryEmbedding

variable {A : Type v} {B : Type w}
variable {RA : RelStructure L A} {RB : RelStructure L B}
variable {outA : F → A → Set A} {outB : F → B → Set B}

/-- The inverse of a surjective exact embedding is again exact, including
all nullary relations and equality of entire set-valued unary fibres. -/
noncomputable def inverse (e : ExactUnaryEmbedding RA outA RB outB)
    (he : Function.Surjective e.toFun) :
    ExactUnaryEmbedding RB outB RA outA := by
  classical
  let i : B ≃ A := (Equiv.ofBijective e.toFun ⟨e.injective, he⟩).symm
  have hright : ∀ b, e.toFun (i b) = b :=
    (Equiv.ofBijective e.toFun ⟨e.injective, he⟩).apply_symm_apply
  have hleft : ∀ a, i (e.toFun a) = a :=
    (Equiv.ofBijective e.toFun ⟨e.injective, he⟩).symm_apply_apply
  refine { toFun := i, injective := i.injective, rel_iff := ?_, out_eq := ?_ }
  · intro n r xs
    simpa only [hright] using (e.rel_iff r (fun k => i (xs k))).symm
  · intro f b
    ext a
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hc' : c ∈ e.toFun '' outA f (i b) := by
        rw [e.out_eq f (i b), hright b]
        exact hc
      obtain ⟨a, ha, hEq⟩ := hc'
      rw [← hEq, hleft]
      exact ha
    · intro ha
      refine ⟨e.toFun a, ?_, hleft a⟩
      have hm : e.toFun a ∈ e.toFun '' outA f (i b) := ⟨a, ha, rfl⟩
      rw [e.out_eq f (i b), hright b] at hm
      exact hm

@[simp] theorem apply_inverse (e : ExactUnaryEmbedding RA outA RB outB)
    (he : Function.Surjective e.toFun) (b : B) :
    e.toFun ((e.inverse he).toFun b) = b :=
  (Equiv.ofBijective e.toFun ⟨e.injective, he⟩).apply_symm_apply b

@[simp] theorem inverse_apply (e : ExactUnaryEmbedding RA outA RB outB)
    (he : Function.Surjective e.toFun) (a : A) :
    (e.inverse he).toFun (e.toFun a) = a :=
  (Equiv.ofBijective e.toFun ⟨e.injective, he⟩).symm_apply_apply a

theorem inverse_surjective (e : ExactUnaryEmbedding RA outA RB outB)
    (he : Function.Surjective e.toFun) :
    Function.Surjective (e.inverse he).toFun := by
  intro a
  exact ⟨e.toFun a, e.inverse_apply he a⟩

end ExactUnaryEmbedding

variable {A B : Type v}
variable {RA : RelStructure L A} {RB : RelStructure L B}
variable {outA : F → A → Set A} {outB : F → B → Set B}

/-- Replace each full B-block by the isomorphic full A-block. The target
structure and both actual gluing maps remain unchanged. -/
theorem FullATree.changeBase
    (e : ExactUnaryEmbedding RA outA RB outB)
    (he : Function.Surjective e.toFun)
    {V : Type v} {RV : RelStructure L V} {outV : F → V → Set V}
    (tree : FullATree RB outB RV outV) :
    FullATree RA outA RV outV := by
  induction tree with
  | copy RV outV d hd =>
      refine .copy RV outV (d.comp e) ?_
      intro x
      obtain ⟨b, hb⟩ := hd x
      obtain ⟨a, ha⟩ := he b
      exact ⟨a, by change d.toFun (e.toFun a) = x; rw [ha, hb]⟩
  | glue RI outI RX outX RY outY hX hY δX δY αX αY ihX ihY =>
      let inv := e.inverse he
      have hx : ((αX.comp e).comp (inv.comp δX)).toFun =
          (αX.comp δX).toFun := by
        funext x
        exact congrArg αX.toFun (e.apply_inverse he (δX.toFun x))
      have hy : ((αY.comp e).comp (inv.comp δY)).toFun =
          (αY.comp δY).toFun := by
        funext y
        exact congrArg αY.toFun (e.apply_inverse he (δY.toFun y))
      have h := FullATree.glue RI outI RX outX RY outY ihX ihY
        (inv.comp δX) (inv.comp δY) (αX.comp e) (αY.comp e)
      simpa only [hx, hy] using h

/-- Isomorphic bases define the same class of literal target trees. -/
theorem FullATree.changeBase_iff
    (e : ExactUnaryEmbedding RA outA RB outB)
    (he : Function.Surjective e.toFun)
    {V : Type v} {RV : RelStructure L V} {outV : F → V → Set V} :
    FullATree RA outA RV outV ↔ FullATree RB outB RV outV := by
  constructor
  · exact FullATree.changeBase (e.inverse he) (e.inverse_surjective he)
  · exact FullATree.changeBase e he

end GluingEPPA.Sparsening.Tree
