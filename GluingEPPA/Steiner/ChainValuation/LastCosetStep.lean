import GluingEPPA.Steiner.ChainValuation.ChainComponentPullback
import GluingEPPA.Steiner.ChainValuation.Cosets

/-!
# Last-block coset induction for a genuine chain extension

The incoming chain already has the exact property that M-reachability
between points of its last block agrees with membership in left cosets
of P. The new Cayley block has the analogous property for Q. If the
attaching maps have equal pullbacks of P and Q, the exact two-group
calculation proves AttachmentReachCompatible. The checked canonical
matching theorem then proves the same last-block coset property for
the extended chain.

This isolates the full one-attachment induction from the
yet-to-be-instantiated earlier-stage Link data. It does not assert
the global normalized smaller-chain theorem.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {H : Type u} {G : Type v} {K : Type w}
variable [Group H] [Group G] [Group K]

/-- A translated common-subgroup attachment has equal restricted
left-coset connectivity on its two sides exactly when the restricted
subgroups have the same pullback to the common attaching group. -/
theorem two_group_coset_pullback
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j)
    (h : G) (k l : H) :
    (h * i k)⁻¹ * (h * i l) ∈ P ↔
      (j k)⁻¹ * j l ∈ Q := by
  have hleft : (h * i k)⁻¹ * (h * i l) = i (k⁻¹ * l) := by
    simp only [map_mul, map_inv]
    group
  have hright : (j k)⁻¹ * j l = j (k⁻¹ * l) := by
    simp only [map_mul, map_inv]
    group
  rw [hleft, hright]
  change k⁻¹ * l ∈ P.comap i ↔ k⁻¹ * l ∈ Q.comap j
  rw [hcomap]

universe a b
variable {E : Type a} {J : Type b} [Group J]
variable (A B : GroupBlock E) (C : ChainState E A)
variable (h : A.Carrier)
variable (left : J →* A.Carrier) (right : J →* B.Carrier)
variable (hleft : Function.Injective left) (hright : Function.Injective right)
variable (hsep : Disjoint C.entry (exitSet A h left))
variable (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
  ∃ k : J, left k = A.edge e ∧ right k = B.edge e)

/-- The exact last-block coset invariant, stated without a separate
quotient model or chosen representatives. -/
def LastBlockCosetInvariant (M : Finset E)
    (P : Subgroup A.Carrier) : Prop :=
  ∀ x y : A.Carrier,
    LabelReach (fun e => (C.matching e).Rel) M
      (C.lastEmbed x) (C.lastEmbed y) ↔ y ∈ leftCoset P x

/-- The earlier-stage subgroup pullback identity gives exactly
the M-component compatibility required by canonical matching. -/
theorem attachment_compatible_of_cosets
    (M : Finset E)
    (P : Subgroup A.Carrier) (Q : Subgroup B.Carrier)
    (hcomap : P.comap left = Q.comap right)
    (hprevious : LastBlockCosetInvariant A C M P)
    (hnew : ∀ x y : B.Carrier,
      LabelReach (fun e => (B.matching e).Rel) M x y ↔
        y ∈ leftCoset Q x) :
    AttachmentReachCompatible A B C h left right M := by
  intro k l
  change LabelReach (fun e => (C.matching e).Rel) M
      (C.lastEmbed (h * left k)) (C.lastEmbed (h * left l)) ↔
    LabelReach (fun e => (B.matching e).Rel) M (right k) (right l)
  rw [hprevious, hnew]
  exact two_group_coset_pullback left right P Q hcomap h k l

/-- Edges of the new block lift to the extended genuine matching. Combined
with the checked no-splitting theorem, this gives equality of whole
M-component equivalence relations on the last block. -/
theorem extended_new_reach_iff_original
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (x y : B.Carrier) :
    LabelReach
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel) M
      (newEmbed A B C h left right hleft hright x)
      (newEmbed A B C h left right hleft hright y) ↔
    LabelReach (fun e => (B.matching e).Rel) M x y := by
  constructor
  · exact chainExtend_new_components_reflect
      A B C h left right hleft hright hsep hshared M hpull x y
  · intro hxy
    apply LabelReach.map
      (fun e => (B.matching e).Rel)
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel)
      M (newEmbed A B C h left right hleft hright)
    · intro e x y hr
      change e ∈ B.active ∧ y = x * B.edge e at hr
      rcases hr with ⟨he, hval⟩
      rw [hval]
      exact Or.inr ⟨x, he, rfl, rfl⟩
    · exact hxy

/-- The inductive last-block invariant after one literal separated
attachment, with all assumptions named rather than hidden inside the
construction. -/
theorem extend_lastBlockCosetInvariant
    (M : Finset E)
    (P : Subgroup A.Carrier) (Q : Subgroup B.Carrier)
    (hcomap : P.comap left = Q.comap right)
    (hprevious : LastBlockCosetInvariant A C M P)
    (hnew : ∀ x y : B.Carrier,
      LabelReach (fun e => (B.matching e).Rel) M x y ↔
        y ∈ leftCoset Q x) :
    LastBlockCosetInvariant B
      (extend A B C h left right hleft hright hsep hshared) M Q := by
  let hpull := attachment_compatible_of_cosets
    A B C h left right M P Q hcomap hprevious hnew
  intro x y
  exact (extended_new_reach_iff_original
    A B C h left right hleft hright hsep hshared M hpull x y).trans
    (hnew x y)

end GluingEPPA.Steiner.ChainValuation
