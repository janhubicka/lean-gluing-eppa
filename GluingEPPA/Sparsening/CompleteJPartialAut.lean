import GluingEPPA.Sparsening.OrbitExtensionFamily

/-!
# Adding a complete auxiliary relation does not restrict partial maps

Both changes keep domains, ranges, and underlying maps literally unchanged.
In particular they preserve the matching-domain composition convention.
-/
namespace GluingEPPA.Sparsening

universe u v t
variable {L : Nat → Type u} {A : Type v} {F : Type t}

/-- Complete J needs no arity casts: its interpretation is always true.
This presentation commutes definitionally with induced substructures. -/
def completeJ (R : RelStructure L A) : RelStructure (WithJ L) A where
  rel r xs := match r with
    | Sum.inl r => R.rel r xs
    | Sum.inr _ => True

namespace ClosedPartialAut

/-- Forget J on all closed partial isomorphisms, not only automorphisms. -/
def forgetJ {R : RelStructure (WithJ L) A} {out : F → A → Set A}
    (p : ClosedPartialAut R out) : ClosedPartialAut (forgetJRelations R) out where
  dom := p.dom
  ran := p.ran
  dom_closed := p.dom_closed
  ran_closed := p.ran_closed
  map := p.map.forgetJ
  surjective := p.surjective

/-- A complete J imposes no new restriction on a partial isomorphism. -/
def withCompleteJ {R : RelStructure L A} {out : F → A → Set A}
    (p : ClosedPartialAut R out) : ClosedPartialAut (completeJ R) out where
  dom := p.dom
  ran := p.ran
  dom_closed := p.dom_closed
  ran_closed := p.ran_closed
  map := {
    toFun := p.map.toFun
    injective := p.map.injective
    rel_iff := by
      intro n r xs
      cases r with
      | inl r => exact p.map.rel_iff r xs
      | inr _ => exact Iff.rfl
    out_eq := p.map.out_eq }
  surjective := p.surjective

theorem forgetJ_withCompleteJ {R : RelStructure L A} {out : F → A → Set A}
    (p : ClosedPartialAut R out) : p.withCompleteJ.forgetJ = p := by
  cases p
  rfl

theorem withCompleteJ_forgetJ {R : RelStructure L A} {out : F → A → Set A}
    (p : ClosedPartialAut (completeJ R) out) : p.forgetJ.withCompleteJ = p := by
  cases p
  rfl

theorem IsComposition.forgetJ {R : RelStructure (WithJ L) A}
    {out : F → A → Set A} {f g h : ClosedPartialAut R out}
    (hc : IsComposition f g h) : IsComposition f.forgetJ g.forgetJ h.forgetJ := hc

theorem IsComposition.withCompleteJ {R : RelStructure L A}
    {out : F → A → Set A} {f g h : ClosedPartialAut R out}
    (hc : IsComposition f g h) :
    IsComposition f.withCompleteJ g.withCompleteJ h.withCompleteJ := hc

end ClosedPartialAut

/-- Completing J leaves all original automorphisms available. -/
def OrbitAtlas.Aut.withCompleteJ {R : RelStructure L A} {out : F → A → Set A}
    (h : OrbitAtlas.Aut R out) : OrbitAtlas.Aut (completeJ R) out where
  perm := h.perm
  rel_iff := by
    intro n r xs
    cases r with
    | inl r => exact h.rel_iff r xs
    | inr _ => exact Iff.rfl
  unary_iff := h.unary_iff

/-- The actual initial expanded structure for the canonical tower. -/
def OrbitAtlas.initialRooted [Finite A] (R : RelStructure L A)
    (out : F → A → Set A) (root : Set A)
    (hr : UnaryClosed out (fun x => x ∈ root)) :
    OrbitAtlas.FiniteRooted.{u,v,t} L F where
  Carrier := A
  finite := inferInstance
  rel := completeJ R
  out := out
  root := root
  root_closed := hr
  root_J := by intro x hx y hy; trivial

end GluingEPPA.Sparsening
