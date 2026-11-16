import GluingEPPA.Steiner.ChainValuation.HistoricalEmbeddedInterface
import GluingEPPA.Steiner.ChainValuation.LinkChain
import GluingEPPA.Steiner.ChainValuation.LinkStepCoset

/-!
# Separation of the genuine incoming and outgoing Link interfaces

In a literal separated LinkChain step, the old last Cayley block's
entry set is disjoint from its next exit coset. This is not merely
a statement in an abstract group: after forming the true injective
pushout, the two historical interface images remain disjoint.

The key point is that an equality between a point of the old
entry interface and a point of the newly attached interface would
force the same old Cayley coordinate into the exit set, contrary
to the original `ChainState.entry` separation condition.

The final lemma applies to a historical incoming boundary whose
actual interface map lands in the old last entry set. It is the
local step of the still-open all-history theorem separating
successive genuine historical interfaces, which in turn supplies
the geometric input for every normalized triple.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The true incoming point of the previous last block cannot be
identified, in the LITERAL extended quotient, with any point of
the new outgoing attachment. No abstract substitute gluing and
no assumption about the group at the complete alphabet S is used. -/
theorem step_entry_point_ne_new_interface
    (R : BuildResult D S old L) (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (x : (old R.current.1).Carrier)
    (hx : x ∈ R.state.entry)
    (k : (old (common S R.current.1 y.1)).Carrier) :
    oldEmbed (block S old R.current.1) (block S old y.1)
      R.state R.current.2
      (left D S old L R.current.1 y.1)
      (right D S old L R.current.1 y.1)
      (left_injective D S old L R.current.1 y.1)
      (right_injective D S old L R.current.1 y.1)
      (R.state.lastEmbed x) ≠
    newEmbed (block S old R.current.1) (block S old y.1)
      R.state R.current.2
      (left D S old L R.current.1 y.1)
      (right D S old L R.current.1 y.1)
      (left_injective D S old L R.current.1 y.1)
      (right_injective D S old L R.current.1 y.1)
      (right D S old L R.current.1 y.1 k) := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hi := left_injective D S old L R.current.1 y.1
  let hj := right_injective D S old L R.current.1 y.1
  have hdisj : Disjoint R.state.entry
      (exitSet A R.current.2 i) :=
    step_attachment_disjoint D S old L R y hsep
  intro hEq
  obtain ⟨t, htold, _⟩ :=
    (oldEmbed_eq_newEmbed_iff A B R.state R.current.2
      i j hi hj (R.state.lastEmbed x) (j k)).mp hEq
  have hExit : x ∈ exitSet A R.current.2 i :=
    ⟨t, R.state.lastInjective htold⟩
  exact (Set.disjoint_left.mp hdisj) hx hExit

/-- The images of ALL old incoming-entry points and ALL new
attaching-parameter points are disjoint in the actual quotient.
The statement retains the original two coordinate embeddings,
rather than expressing a disjointness property of fictional blocks. -/
theorem step_entry_image_disjoint_new_interface
    (R : BuildResult D S old L) (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y) :
    Disjoint
      (Set.range
        (fun x : {x : (old R.current.1).Carrier // x ∈ R.state.entry} =>
          oldEmbed (block S old R.current.1) (block S old y.1)
            R.state R.current.2
            (left D S old L R.current.1 y.1)
            (right D S old L R.current.1 y.1)
            (left_injective D S old L R.current.1 y.1)
            (right_injective D S old L R.current.1 y.1)
            (R.state.lastEmbed x.val)))
      (Set.range
        (fun k : (old (common S R.current.1 y.1)).Carrier =>
          newEmbed (block S old R.current.1) (block S old y.1)
            R.state R.current.2
            (left D S old L R.current.1 y.1)
            (right D S old L R.current.1 y.1)
            (left_injective D S old L R.current.1 y.1)
            (right_injective D S old L R.current.1 y.1)
            (right D S old L R.current.1 y.1 k))) := by
  apply Set.disjoint_left.mpr
  intro v hvEntry hvNew
  obtain ⟨x, hx⟩ := hvEntry
  obtain ⟨k, hk⟩ := hvNew
  exact (step_entry_point_ne_new_interface D S old L
    R y hsep x.val x.property k) (hx.trans hk.symm)

/-- An actual historical INCOMING interface that lies in the
last block's recorded entry set remains disjoint from the new
outgoing interface of a genuine separated LinkChain step.
The historical map may come from an arbitrarily long old chain;
only the original-entry property is required at this stage. -/
theorem step_historical_entry_disjoint_fresh_interface
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (P : HistoricalLinkBoundary D S old L M R)
    (hEntry : ∀ k : (old (common S P.leftMask P.rightMask)).Carrier,
      ∃ x : (old R.current.1).Carrier,
        x ∈ R.state.entry ∧
        P.interfaceMap D S old L k = R.state.lastEmbed x) :
    Disjoint
      (Set.range
        (fun k : (old (common S P.leftMask P.rightMask)).Carrier =>
          oldEmbed (block S old R.current.1) (block S old y.1)
            R.state R.current.2
            (left D S old L R.current.1 y.1)
            (right D S old L R.current.1 y.1)
            (left_injective D S old L R.current.1 y.1)
            (right_injective D S old L R.current.1 y.1)
            (P.interfaceMap D S old L k)))
      (Set.range
        (fun k : (old (common S R.current.1 y.1)).Carrier =>
          newEmbed (block S old R.current.1) (block S old y.1)
            R.state R.current.2
            (left D S old L R.current.1 y.1)
            (right D S old L R.current.1 y.1)
            (left_injective D S old L R.current.1 y.1)
            (right_injective D S old L R.current.1 y.1)
            (right D S old L R.current.1 y.1 k))) := by
  apply Set.disjoint_left.mpr
  intro v hOld hNew
  obtain ⟨k, hk⟩ := hOld
  obtain ⟨l, hl⟩ := hNew
  obtain ⟨x, hx, hcoord⟩ := hEntry k
  apply step_entry_point_ne_new_interface
    D S old L R y hsep x hx l
  calc
    oldEmbed (block S old R.current.1) (block S old y.1)
      R.state R.current.2
      (left D S old L R.current.1 y.1)
      (right D S old L R.current.1 y.1)
      (left_injective D S old L R.current.1 y.1)
      (right_injective D S old L R.current.1 y.1)
      (R.state.lastEmbed x) =
        oldEmbed (block S old R.current.1) (block S old y.1)
          R.state R.current.2
          (left D S old L R.current.1 y.1)
          (right D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1)
          (right_injective D S old L R.current.1 y.1)
          (P.interfaceMap D S old L k) := by rw [hcoord]
    _ = v := hk
    _ = _ := hl.symm

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
