import GluingEPPA.Steiner.ChainValuation.StepMatchedOldComponent
import GluingEPPA.Steiner.ChainValuation.ChainExtendMatchedComponent
import GluingEPPA.Steiner.ChainValuation.LinkStepComponentMatching

/-!
# The exact full M-component at the manuscript's LinkChain.step

At the genuine separated LinkChain.step (not an auxiliary pushout),
the restricted pushout of the entire old M-component and the matched
new restricted coset is exactly the *whole* M-component of its
image in the new state. The interface-pullback hypothesis is
discharged by the previously verified earlier-stage Link identities
and the last-block coset invariant.

The second theorem upgrades exact coverage to a bijection of the
selected restricted pushout with the full actual M-component.
No normality, global K_S, or additional component-saturation axiom.
This is an induction STEP, not a finite-list normal form.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- In the literal separated LinkChain.step the entire component
is precisely the selected old component and its matched new coset. -/
theorem step_matchedOldComponent_covered_iff_reach
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k)))
    (v : (step D S old L R y hsep).state.Space) :
    v ∈ (stepMatchedOldComponentRestriction
      D S old L M R y hprev q k hq).Covered
        (attachInto_injective
          R.state.lastEmbed R.state.lastInjective R.current.2
          (left D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1))
        (right_injective D S old L R.current.1 y.1) ↔
    LabelReach
      (fun e => ((step D S old L R y hsep).state.matching e).Rel)
      M.val
      (oldEmbed (block S old R.current.1) (block S old y.1)
        R.state R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1) q)
      v := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hi := left_injective D S old L R.current.1 y.1
  let hj := right_injective D S old L R.current.1 y.1
  let hf := attachInto_injective
    R.state.lastEmbed R.state.lastInjective R.current.2 i hi
  let hpull := step_attachment_compatible D S old L M R y hprev
  let W := stepMatchedOldComponentRestriction
    D S old L M R y hprev q k hq
  let U := matchedComponentRestriction
    (fun e => (R.state.matching e).Rel)
    (fun e => (B.matching e).Rel) M.val
    (attachInto R.state.lastEmbed R.current.2 i) j
    hpull q k hq
  have hcover : W.Covered hf hj = U.Covered hf hj := by
    ext z
    change
      ((∃ x : W.Left, pushoutInl (attachInto R.state.lastEmbed R.current.2 i)
        j hf hj x.val = z) ∨
       (∃ y0 : W.Right, pushoutInr (attachInto R.state.lastEmbed R.current.2 i)
        j hf hj y0.val = z)) ↔
      ((∃ x : U.Left, pushoutInl (attachInto R.state.lastEmbed R.current.2 i)
        j hf hj x.val = z) ∨
       (∃ y0 : U.Right, pushoutInr (attachInto R.state.lastEmbed R.current.2 i)
        j hf hj y0.val = z))
    constructor
    · rintro (⟨x, hx⟩ | ⟨t, ht⟩)
      · exact Or.inl ⟨⟨x.val, x.property⟩, hx⟩
      · exact Or.inr ⟨⟨t.val,
          (restricted_block_reach_iff_coset
            D S old L M y.1 (j k) t.val).mpr t.property⟩, ht⟩
    · rintro (⟨x, hx⟩ | ⟨t, ht⟩)
      · exact Or.inl ⟨⟨x.val, x.property⟩, hx⟩
      · exact Or.inr ⟨⟨t.val,
          (restricted_block_reach_iff_coset
            D S old L M y.1 (j k) t.val).mp t.property⟩, ht⟩
  have hd := step_attachment_disjoint D S old L R y hsep
  have hs : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ t : (old (common S R.current.1 y.1)).Carrier,
        i t = A.edge e ∧ j t = B.edge e := by
    intro e heA heB
    exact shared_edge D S old L R.current.1 y.1 e heA heB
  change v ∈ W.Covered hf hj ↔
    LabelReach
      (fun e => ((extend A B R.state R.current.2 i j
        hi hj hd hs).matching e).Rel) M.val
      (oldEmbed A B R.state R.current.2 i j hi hj q) v
  rw [hcover]
  exact extend_matchedComponent_covered_iff_reach
    A B R.state R.current.2 i j hi hj hd hs
    M.val hpull q k hq v

/-- The restricted pushout of a *whole old-chain component* and its
literal new-block Link coset is bijective to the full component of
the chosen vertex in the actual extended LinkChain.step state. -/
noncomputable def step_matchedOldComponent_equivFull
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k))) :
    let W := stepMatchedOldComponentRestriction
      D S old L M R y hprev q k hq
    let i := left D S old L R.current.1 y.1
    let j := right D S old L R.current.1 y.1
    let hf := attachInto_injective
      R.state.lastEmbed R.state.lastInjective R.current.2 i
      (left_injective D S old L R.current.1 y.1)
    let hj := right_injective D S old L R.current.1 y.1
    W.Space hf hj ≃
      {v : (step D S old L R y hsep).state.Space //
        LabelReach
          (fun e => ((step D S old L R y hsep).state.matching e).Rel)
          M.val
          (oldEmbed (block S old R.current.1) (block S old y.1)
            R.state R.current.2 i j
            (left_injective D S old L R.current.1 y.1)
            (right_injective D S old L R.current.1 y.1) q)
          v} := by
  let W := stepMatchedOldComponentRestriction
    D S old L M R y hprev q k hq
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hf := attachInto_injective
    R.state.lastEmbed R.state.lastInjective R.current.2 i
    (left_injective D S old L R.current.1 y.1)
  let hj := right_injective D S old L R.current.1 y.1
  let F : W.Space hf hj →
      {v : (step D S old L R y hsep).state.Space //
        LabelReach
          (fun e => ((step D S old L R y hsep).state.matching e).Rel)
          M.val
          (oldEmbed (block S old R.current.1) (block S old y.1)
            R.state R.current.2 i j
            (left_injective D S old L R.current.1 y.1)
            (right_injective D S old L R.current.1 y.1) q)
          v} :=
    fun p => ⟨W.intoFull hf hj p,
      (step_matchedOldComponent_covered_iff_reach
        D S old L M R y hsep hprev q k hq _).mp
        (W.intoFull_mem_covered hf hj p)⟩
  apply Equiv.ofBijective F
  constructor
  · intro p p' hp
    apply W.intoFull_injective hf hj
    exact congrArg Subtype.val hp
  · intro v
    have hcovered : v.val ∈ W.Covered hf hj :=
      (step_matchedOldComponent_covered_iff_reach
        D S old L M R y hsep hprev q k hq _).mpr v.property
    obtain ⟨p, hp⟩ :=
      W.intoFull_surjective_covered hf hj ⟨v.val, hcovered⟩
    exact ⟨p, Subtype.ext hp⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
