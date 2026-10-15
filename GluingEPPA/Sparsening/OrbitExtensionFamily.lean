import GluingEPPA.Sparsening.ClosedPartialAut
import GluingEPPA.Sparsening.OrbitTowerReduct

/-!
# Whole extension families through the canonical finite tower

The family is indexed by every closed partial automorphism of one fixed
original root. Domain and range charts are their actual images under the
root embedding. Their equality with the charts moved by the chosen
extension is proved, not assumed. The two-spoke formula then preserves
both the extension equations and coherence for every composable triple.
-/
namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v t u' v'

/-- Equality of the permutations determines a relational/unary automorphism. -/
theorem Aut.ext_perm {L : Nat → Type u} {F : Type t} {A : Type v}
    {R : RelStructure L A} {out : F → A → Set A}
    {h g : Aut R out} (he : ∀ x, h.perm x = g.perm x) : h = g := by
  have hp : h.perm = g.perm := Equiv.ext he
  cases h
  cases g
  cases hp
  rfl

/-- Every partial automorphism extends on the specified copy of its source. -/
def ExtendsAlong {L : Nat → Type u} {K : Nat → Type u'}
    {A : Type v} {B : Type v'} {F : Type t}
    {RA : RelStructure L A} {outA : F → A → Set A}
    {RB : RelStructure K B} {outB : F → B → Set B}
    (i : A → B) (H : ClosedPartialAut RA outA → Aut RB outB) : Prop :=
  ∀ (p : ClosedPartialAut RA outA) (x : p.dom),
    (H p).perm (i x.val) = i (p.map.toFun x).val

/-- Coherence is equality of actual automorphisms for every composable triple. -/
def CoherentFamily {L : Nat → Type u} {K : Nat → Type u'}
    {A : Type v} {B : Type v'} {F : Type t}
    {RA : RelStructure L A} {outA : F → A → Set A}
    {RB : RelStructure K B} {outB : F → B → Set B}
    (H : ClosedPartialAut RA outA → Aut RB outB) : Prop :=
  ∀ f g h, ClosedPartialAut.IsComposition f g h → H h = (H f).trans (H g)

open scoped Classical
noncomputable section
variable {L : Nat → Type u} {F : Type t} {A : Type v}
variable {RA : RelStructure (WithJ L) A} {outA : F → A → Set A}
attribute [local instance] chartsFintype edgesFintype

namespace FiniteRooted
variable (C : FiniteRooted.{u,v,t} L F)
variable (e : Tree.ExactUnaryEmbedding RA outA C.rootRelations C.rootOutputs)

/-- Include the exact root copy into the whole current stage. -/
def rootAmbient : Tree.ExactUnaryEmbedding RA outA C.rel C.out :=
  (Tree.ExactUnaryEmbedding.closedSubtype C.rel C.out C.root C.root_closed).comp e

/-- The actual image chart of a closed original domain or range. -/
def partChart (D : Set A) (hD : UnaryClosed outA (fun x => x ∈ D)) :
    Chart C.rel C.out C.root :=
  subchart C.rel C.out C.root ((C.rootAmbient e).toFun '' D)
    ((C.rootAmbient e).toHomEmbedding.image_closed D hD) (by
      rintro q ⟨a, ha, rfl⟩
      exact (e.toFun a).property)

theorem partChart_congr (D E : Set A)
    (hD : UnaryClosed outA (fun x => x ∈ D))
    (hE : UnaryClosed outA (fun x => x ∈ E)) (he : D = E) :
    C.partChart e D hD = C.partChart e E hE := by
  subst E
  rfl

/-- A chosen extension moves the domain chart onto the range chart.
Surjectivity is used only for the partial isomorphism, not the projection. -/
theorem partChart_image
    (H : ClosedPartialAut RA outA → Aut C.rel C.out)
    (hH : ExtendsAlong (C.rootAmbient e).toFun H)
    (p : ClosedPartialAut RA outA) :
    chartPerm C.rel C.out C.root (H p) (C.partChart e p.dom p.dom_closed) =
      C.partChart e p.ran p.ran_closed := by
  apply Subtype.ext
  ext q
  change q ∈ (H p).perm '' ((C.rootAmbient e).toFun '' p.dom) ↔
    q ∈ (C.rootAmbient e).toFun '' p.ran
  constructor
  · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(p.map.toFun ⟨a, ha⟩).val, (p.map.toFun ⟨a, ha⟩).property,
      (hH p ⟨a, ha⟩).symm⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha⟩ := p.surjective ⟨b, hb⟩
    refine ⟨(C.rootAmbient e).toFun a.val, ⟨a.val, a.property, rfl⟩, ?_⟩
    simpa only [ha] using hH p a

/-- One uniform two-spoke construction for all original partial automorphisms. -/
def refineFamily (H : ClosedPartialAut RA outA → Aut C.rel C.out) :
    ClosedPartialAut RA outA → Aut C.refine.rel C.refine.out :=
  fun p => endpoint C.rel C.out C.root C.root_closed (H p)
    (C.partChart e p.dom p.dom_closed) (C.partChart e p.ran p.ran_closed)

theorem refineFamily_extends
    (H : ClosedPartialAut RA outA → Aut C.rel C.out)
    (hH : ExtendsAlong (C.rootAmbient e).toFun H) :
    ExtendsAlong
      (fun a => ((refinedRootExact C.rel C.out C.root C.root_closed).toFun
        (e.toFun a)).val) (C.refineFamily e H) := by
  intro p x
  let D := C.partChart e p.dom p.dom_closed
  have hD : D.val ⊆ C.root := by
    rintro q ⟨a, ha, rfl⟩
    exact (e.toFun a).property
  have hE : (H p).perm '' D.val ⊆ C.root := by
    rintro q ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    change (H p).perm ((C.rootAmbient e).toFun a) ∈ C.root
    rw [hH p ⟨a, ha⟩]
    exact (e.toFun (p.map.toFun ⟨a, ha⟩).val).property
  have hp := endpoint_extends C.rel C.out C.root C.root_closed (H p) D
    hD hE ((C.rootAmbient e).toFun x.val) ⟨x.val, x.property, rfl⟩
  have himage := C.partChart_image e H hH p
  change chartPerm C.rel C.out C.root (H p) D = _ at himage
  rw [himage, hH p x] at hp
  exact hp

/-- Coherence needs no new choices: the identical middle chart cancels. -/
theorem refineFamily_coherent
    (H : ClosedPartialAut RA outA → Aut C.rel C.out)
    (hH : CoherentFamily H) : CoherentFamily (C.refineFamily e H) := by
  intro f g h hc
  apply Aut.ext_perm
  intro q
  have hmid := C.partChart_congr e f.ran g.dom f.ran_closed g.dom_closed hc.1
  have hdom := C.partChart_congr e h.dom f.dom h.dom_closed f.dom_closed hc.2.1
  have hran := C.partChart_congr e h.ran g.ran h.ran_closed g.ran_closed hc.2.2.1
  change (endpoint C.rel C.out C.root C.root_closed (H h)
    (C.partChart e h.dom h.dom_closed) (C.partChart e h.ran h.ran_closed)).perm q =
    (endpoint C.rel C.out C.root C.root_closed (H g)
      (C.partChart e g.dom g.dom_closed) (C.partChart e g.ran g.ran_closed)).perm
      ((endpoint C.rel C.out C.root C.root_closed (H f)
        (C.partChart e f.dom f.dom_closed) (C.partChart e f.ran f.ran_closed)).perm q)
  rw [hH f g h hc, hdom, hran, ← hmid]
  exact (endpoint_comp C.rel C.out C.root C.root_closed (H f) (H g)
    (C.partChart e f.dom f.dom_closed) (C.partChart e f.ran f.ran_closed)
    (C.partChart e g.ran g.ran_closed) q).symm

/-- Actual successive families, always indexed by the ORIGINAL partial maps. -/
def towerFamily (C : FiniteRooted.{u,v,t} L F)
    (H0 : ClosedPartialAut C.rootRelations C.rootOutputs → Aut C.rel C.out) :
    (n : Nat) → ClosedPartialAut C.rootRelations C.rootOutputs →
      Aut (C.tower n).rel (C.tower n).out
  | 0 => H0
  | n + 1 => (C.tower n).refineFamily (C.rootEmbedding n) (towerFamily C H0 n)

/-- Every original partial automorphism extends at every finite stage. -/
theorem towerFamily_extends
    (H0 : ClosedPartialAut C.rootRelations C.rootOutputs → Aut C.rel C.out)
    (h0 : ExtendsAlong Subtype.val H0) (n : Nat) :
    ExtendsAlong (fun a => ((C.rootEmbedding n).toFun a).val) (C.towerFamily H0 n) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact (C.tower n).refineFamily_extends (C.rootEmbedding n) (C.towerFamily H0 n) ih

/-- Coherence for the whole family persists through the actual finite tower. -/
theorem towerFamily_coherent
    (H0 : ClosedPartialAut C.rootRelations C.rootOutputs → Aut C.rel C.out)
    (h0 : CoherentFamily H0) (n : Nat) : CoherentFamily (C.towerFamily H0 n) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact (C.tower n).refineFamily_coherent (C.rootEmbedding n) (C.towerFamily H0 n) ih

end FiniteRooted
end
end GluingEPPA.Sparsening.OrbitAtlas
