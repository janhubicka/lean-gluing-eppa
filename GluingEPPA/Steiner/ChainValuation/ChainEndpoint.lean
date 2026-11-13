import GluingEPPA.Steiner.ChainValuation.ChainAttach

/-!
# Endpoint separation in an iterated Cayley chain

A point of the old chain outside its final block cannot be identified with
a point of the next block. At the first attachment it is enough that the
chosen initial point lies outside the outgoing attachment coset. These
statements use the *actual injective pushout* of the chain construction.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]
variable (A B : GroupBlock E) (C : ChainState E A)
variable (h : A.Carrier)
variable (left : K →* A.Carrier) (right : K →* B.Carrier)
variable (hleft : Function.Injective left) (hright : Function.Injective right)

/-- The point chosen outside the first outgoing coset cannot coincide with
any vertex of the next block. -/
theorem outside_exit_not_new
    (x : A.Carrier) (hx : x ∉ exitSet A h left)
    (y : B.Carrier) :
    oldEmbed A B C h left right hleft hright (C.lastEmbed x) ≠
      newEmbed A B C h left right hleft hright y := by
  intro heq
  obtain ⟨k, hk, _⟩ :=
    (oldEmbed_eq_newEmbed_iff A B C h left right hleft hright
      (C.lastEmbed x) y).1 heq
  have hxk : h * left k = x := C.lastInjective hk
  exact hx ⟨k, hxk⟩

/-- Once the initial point is outside the last block, it remains outside
every later block after another attachment. -/
theorem outside_last_not_new
    (x : C.Space) (hx : ∀ a : A.Carrier, C.lastEmbed a ≠ x)
    (y : B.Carrier) :
    oldEmbed A B C h left right hleft hright x ≠
      newEmbed A B C h left right hleft hright y := by
  intro heq
  obtain ⟨k, hk, _⟩ :=
    (oldEmbed_eq_newEmbed_iff A B C h left right hleft hright x y).1 heq
  exact hx (h * left k) hk

/-- Every subsequent block is disjoint from the retained initial endpoint.
The condition is stable under an arbitrary additional separated attachment;
indeed the proof only needs the exact old/new pushout. -/
theorem outside_last_propagates
    (x : C.Space) (hx : ∀ a : A.Carrier, C.lastEmbed a ≠ x) :
    ∀ y : B.Carrier,
      newEmbed A B C h left right hleft hright y ≠
        oldEmbed A B C h left right hleft hright x := by
  intro y
  exact (outside_last_not_new A B C h left right hleft hright x hx y).symm

end GluingEPPA.Steiner.ChainValuation
