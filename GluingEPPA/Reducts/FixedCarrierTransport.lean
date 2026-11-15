import GluingEPPA.Reducts.PairRowCompletion
import GluingEPPA.Reducts.MultipartiteReplication

/-!
Transport to a fixed carrier. The atlas is explicit input here; its finite
existence is proved separately in MultipartiteFiniteAtlas. The application
below uses the actually defined replica action and auxiliary table, not an
assumed upstairs automorphism. No end-to-end EPPA conclusion is asserted.
-/
namespace GluingEPPA.Reducts.FixedCarrierTransport
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.PairRowCompletion
universe u v w

structure Atlas (X : Type u) (Y : Type v) where
  forward : X → Y
  backward : Y → X
  left_inv : ∀ x, backward (forward x) = x
  right_inv : ∀ y, forward (backward y) = y

namespace Atlas

def identity (X : Type u) : Atlas X X := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def comp {X : Type u} {Y : Type v} {Z : Type w}
    (g : Atlas Y Z) (f : Atlas X Y) : Atlas X Z where
  forward x := g.forward (f.forward x)
  backward z := f.backward (g.backward z)
  left_inv := by intro x; rw [g.left_inv, f.left_inv]
  right_inv := by intro z; rw [f.right_inv, g.right_inv]

def inverse {X : Type u} {Y : Type v} (e : Atlas X Y) : Atlas Y X :=
  ⟨e.backward, e.forward, e.right_inv, e.left_inv⟩

end Atlas

/-- Forward equality determines the inverse as well. -/
theorem basePerm_ext {X : Type u} (p q : BasePerm X)
    (h : ∀ x, p.forward x = q.forward x) : p = q := by
  have hf : p.forward = q.forward := funext h
  have hb : p.backward = q.backward := by
    funext y
    calc
      p.backward y = p.backward (q.forward (q.backward y)) :=
        congrArg p.backward (q.right_inv y).symm
      _ = p.backward (p.forward (q.backward y)) :=
        congrArg p.backward (h (q.backward y)).symm
      _ = q.backward y := p.left_inv (q.backward y)
  cases p
  cases q
  cases hf
  cases hb
  rfl

def transport {X : Type u} {Y : Type v} (e : Atlas X Y)
    (p : BasePerm X) : BasePerm Y where
  forward y := e.forward (p.forward (e.backward y))
  backward y := e.forward (p.backward (e.backward y))
  left_inv := by intro y; rw [e.left_inv, p.left_inv, e.right_inv]
  right_inv := by intro y; rw [e.left_inv, p.right_inv, e.right_inv]

theorem transport_identity {X : Type u} {Y : Type v} (e : Atlas X Y) :
    transport e (BasePerm.identity X) = BasePerm.identity Y := by
  apply basePerm_ext
  intro y
  exact e.right_inv y

theorem transport_comp {X : Type u} {Y : Type v} (e : Atlas X Y)
    (g f : BasePerm X) :
    transport e (g.comp f) = (transport e g).comp (transport e f) := by
  apply basePerm_ext
  intro y
  change e.forward (g.forward (f.forward (e.backward y))) =
    e.forward (g.forward (e.backward (e.forward (f.forward (e.backward y)))))
  rw [e.left_inv]

def transportedTable {X : Type u} {Y : Type v} (e : Atlas X Y)
    (q : X → X → Bool) (y z : Y) : Bool := q (e.backward y) (e.backward z)

def transportedCross {X : Type u} {Y : Type v} (e : Atlas X Y)
    (cross : X → X → Prop) (y z : Y) : Prop := cross (e.backward y) (e.backward z)

theorem table_invariant {X : Type u} {Y : Type v} (e : Atlas X Y)
    (q : X → X → Bool) (p : BasePerm X)
    (hq : ∀ x z, q (p.forward x) (p.forward z) = q x z) (y z : Y) :
    transportedTable e q ((transport e p).forward y) ((transport e p).forward z) =
      transportedTable e q y z := by
  change q (e.backward (e.forward (p.forward (e.backward y))))
    (e.backward (e.forward (p.forward (e.backward z)))) = q (e.backward y) (e.backward z)
  rw [e.left_inv, e.left_inv]
  exact hq _ _

theorem cross_invariant {X : Type u} {Y : Type v} (e : Atlas X Y)
    (cross : X → X → Prop) (p : BasePerm X)
    (hc : ∀ x z, cross (p.forward x) (p.forward z) ↔ cross x z) (y z : Y) :
    transportedCross e cross ((transport e p).forward y) ((transport e p).forward z) ↔
      transportedCross e cross y z := by
  change cross (e.backward (e.forward (p.forward (e.backward y))))
    (e.backward (e.forward (p.forward (e.backward z)))) ↔ cross (e.backward y) (e.backward z)
  rw [e.left_inv, e.left_inv]
  exact hc _ _

theorem transport_extends {X : Type u} {Y : Type v} {D : Type w}
    (e : Atlas X Y) (a : D → X) (j : D → Y) (f : D → D) (p : BasePerm X)
    (he : ∀ d, e.forward (a d) = j d)
    (hp : ∀ d, p.forward (a d) = a (f d)) (d : D) :
    (transport e p).forward (j d) = j (f d) := by
  rw [← he d]
  change e.forward (p.forward (e.backward (e.forward (a d)))) = j (f d)
  rw [e.left_inv, hp, he]

theorem table_restrict {X : Type u} {Y : Type v} {D : Type w}
    (e : Atlas X Y) (a : D → X) (j : D → Y) (q : X → X → Bool)
    (he : ∀ d, e.forward (a d) = j d) (d d' : D) :
    transportedTable e q (j d) (j d') = q (a d) (a d') := by
  rw [← he d, ← he d']
  change q (e.backward (e.forward (a d))) (e.backward (e.forward (a d'))) = _
  rw [e.left_inv, e.left_inv]

/-- The already constructed replicated table remains invariant after transport. -/
theorem replicated_table_invariant {D U : Type u} {Y : Type v} {m : D → Nat}
    (e : Atlas (MultipartiteReplication.Space m U) Y)
    (cd : D → D → Bool) (cu : U → U → Bool) (p : BasePerm D)
    (hm : ∀ d, m (p.forward d) = m d)
    (hc : ∀ x z, cd (p.forward x) (p.forward z) = cd x z) (y z : Y) :
    transportedTable e (MultipartiteReplication.auxiliary cd cu)
      ((transport e (MultipartiteReplication.paddedPerm p hm)).forward y)
      ((transport e (MultipartiteReplication.paddedPerm p hm)).forward z) =
    transportedTable e (MultipartiteReplication.auxiliary cd cu) y z := by
  exact table_invariant e _ _
    (MultipartiteReplication.auxiliary_invariant cd cu p hm hc) y z

/-- Feed the transported orientation into the actual shared-row valuation lift. -/
theorem transported_completed_edge {X : Type u} {Y : Type v}
    (e : Atlas X Y) (cross : X → X → Prop) (q : X → X → Bool)
    (p : BasePerm X) (inside : Y → Bool) (b rows : Y → Y → Bool)
    (hb : ∀ y z, transportedCross e cross y z → b z y = Bool.not (b y z))
    (hq : ∀ x z, cross x z → q z x = Bool.not (q x z))
    (hrows : ∀ y z, transportedCross e cross y z → inside y = true → inside z = true →
      Bool.xor (rows y z) (rows z y) = Bool.xor (transportedTable e q y z) (b y z))
    (hc : ∀ x z, cross (p.forward x) (p.forward z) ↔ cross x z)
    (hinv : ∀ x z, q (p.forward x) (p.forward z) = q x z)
    (a c : Vertex Y) :
    Edge (transportedCross e cross) b
      (lift (completeRows inside b (transportedTable e q) rows) (transport e p) a)
      (lift (completeRows inside b (transportedTable e q) rows) (transport e p) c) ↔
      Edge (transportedCross e cross) b a c := by
  apply completed_lift_preserves_edge inside (transportedCross e cross) b
    (transportedTable e q) rows (transport e p) hb
  · intro y z hyz
    exact hq (e.backward y) (e.backward z) hyz
  · exact hrows
  · exact cross_invariant e cross p hc
  · intro y z _
    exact table_invariant e q p hinv y z

/-- Transport and valuation conjugation preserve the same group law. -/
theorem transported_lift_comp {X : Type u} {Y : Type v} (e : Atlas X Y)
    (mu : Y → Y → Bool) (g f : BasePerm X) (a : Vertex Y) :
    lift mu (transport e (g.comp f)) a =
      lift mu (transport e g) (lift mu (transport e f) a) := by
  rw [transport_comp, lift_comp]

/-- The concrete completed lift extends the input after transporting the base. -/
theorem transported_completed_extends {X : Type u} {Y : Type v} {D : Type w}
    (e : Atlas X Y) (a : D → X) (j : D → Y) (f : D → D) (p : BasePerm X)
    (inside : Y → Bool) (b q rows : Y → Y → Bool)
    (he : ∀ d, e.forward (a d) = j d)
    (hp : ∀ d, p.forward (a d) = a (f d))
    (hj : ∀ d, inside (j d) = true) (d : D) :
    lift (completeRows inside b q rows) (transport e p) (embed rows (j d)) =
      embed rows (j (f d)) := by
  have hs := transport_extends e a j f p he hp d
  have hi : inside ((transport e p).forward (j d)) = true := by
    rw [hs]
    exact hj (f d)
  rw [completed_lift_extends inside b q rows (transport e p) (j d) (hj d) hi, hs]

end GluingEPPA.Reducts.FixedCarrierTransport
