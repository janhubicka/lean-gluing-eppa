import GluingEPPA.Sparsening.TreeFullA
import GluingEPPA.Sparsening.TreeIrreducibleSide

/-!
# Closed partial automorphisms and composable triples

These are all isomorphisms between closed induced substructures, with
entire unary fibres. Composition is only used when range equals domain,
as required for coherent EPPA. The empty substructure is included.
-/
namespace GluingEPPA.Sparsening

universe u v t
variable {L : Nat → Type u} {F : Type t} {A : Type v}

structure ClosedPartialAut (R : RelStructure L A) (out : F → A → Set A) where
  dom : Set A
  ran : Set A
  dom_closed : UnaryClosed out (fun x => x ∈ dom)
  ran_closed : UnaryClosed out (fun x => x ∈ ran)
  map : Tree.ExactUnaryEmbedding (inducedRelations R dom) (inducedUnary out dom)
    (inducedRelations R ran) (inducedUnary out ran)
  surjective : Function.Surjective map.toFun

namespace ClosedPartialAut
variable {R : RelStructure L A} {out : F → A → Set A}

/-- The graph, without a choice of proof that its input lies in the domain. -/
def Graph (p : ClosedPartialAut R out) (x y : A) : Prop :=
  ∃ hx : x ∈ p.dom, (p.map.toFun ⟨x, hx⟩).val = y

/-- h is exactly g after f, with matching middle substructures. -/
def IsComposition (f g h : ClosedPartialAut R out) : Prop :=
  f.ran = g.dom ∧ h.dom = f.dom ∧ h.ran = g.ran ∧
    ∀ x y z, f.Graph x y → g.Graph y z → h.Graph x z

/-- The identity on an arbitrary closed set, including the empty set. -/
def idOn (D : Set A) (hD : UnaryClosed out (fun x => x ∈ D)) :
    ClosedPartialAut R out where
  dom := D
  ran := D
  dom_closed := hD
  ran_closed := hD
  map := Tree.ExactUnaryEmbedding.refl (inducedRelations R D) (inducedUnary out D)
  surjective := fun x => ⟨x, rfl⟩

/-- Exact identity after reindexing equal induced substructures. -/
def retag (R : RelStructure L A) (out : F → A → Set A)
    (D E : Set A) (h : D = E) :
    Tree.ExactUnaryEmbedding (inducedRelations R D) (inducedUnary out D)
      (inducedRelations R E) (inducedUnary out E) where
  toFun x := ⟨x.val, h ▸ x.property⟩
  injective := fun _ _ he => Subtype.ext (congrArg Subtype.val he)
  rel_iff _ _ := Iff.rfl
  out_eq := by
    intro f x
    ext y
    constructor
    · rintro ⟨z, hz, he⟩
      change y.val ∈ out f x.val
      rw [← congrArg Subtype.val he]
      exact hz
    · intro hy
      exact ⟨⟨y.val, h.symm ▸ y.property⟩, hy, Subtype.ext rfl⟩

theorem retag_surjective (R : RelStructure L A) (out : F → A → Set A)
    (D E : Set A) (h : D = E) :
    Function.Surjective (retag R out D E h).toFun := by
  intro y
  exact ⟨⟨y.val, h.symm ▸ y.property⟩, Subtype.ext rfl⟩

/-- Actual composition, not a postulated relation on labels. -/
def comp (f g : ClosedPartialAut R out) (hm : f.ran = g.dom) :
    ClosedPartialAut R out where
  dom := f.dom
  ran := g.ran
  dom_closed := f.dom_closed
  ran_closed := g.ran_closed
  map := g.map.comp ((retag R out f.ran g.dom hm).comp f.map)
  surjective := by
    intro z
    obtain ⟨y, hy⟩ := g.surjective z
    obtain ⟨w, hw⟩ := retag_surjective R out f.ran g.dom hm y
    obtain ⟨x, hx⟩ := f.surjective w
    refine ⟨x, ?_⟩
    change g.map.toFun ((retag R out f.ran g.dom hm).toFun (f.map.toFun x)) = z
    rw [hx, hw, hy]

theorem comp_isComposition (f g : ClosedPartialAut R out) (hm : f.ran = g.dom) :
    IsComposition f g (f.comp g hm) := by
  refine ⟨hm, rfl, rfl, ?_⟩
  rintro x y z ⟨hx, hxy⟩ ⟨hy, hyz⟩
  refine ⟨hx, ?_⟩
  change (g.map.toFun ((retag R out f.ran g.dom hm).toFun
    (f.map.toFun ⟨x, hx⟩))).val = z
  have he : (retag R out f.ran g.dom hm).toFun (f.map.toFun ⟨x, hx⟩) =
      (⟨y, hy⟩ : g.dom) := Subtype.ext hxy
  rw [he]
  exact hyz

/-- In particular the composable-triple convention includes empty identities. -/
theorem idOn_isComposition (D : Set A) (hD : UnaryClosed out (fun x => x ∈ D)) :
    IsComposition (idOn (R := R) D hD) (idOn D hD) (idOn D hD) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rintro x y z ⟨hx, hxy⟩ ⟨hy, hyz⟩
  exact ⟨hx, hxy.trans hyz⟩

end ClosedPartialAut
end GluingEPPA.Sparsening
