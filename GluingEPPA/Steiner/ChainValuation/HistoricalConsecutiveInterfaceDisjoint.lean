import GluingEPPA.Steiner.ChainValuation.CoveredNamedLastInterfaceEntry
import GluingEPPA.Steiner.ChainValuation.ActualStepInterfaceSeparation

/-!
# Genuine consecutive historical interfaces are disjoint

The missing all-interior normalized chain separation does NOT
follow just from equality of historical boundary chart ranges.
The original separated LinkChain records the stronger geometric
fact: at each step its previous incoming interface and fresh
outgoing interface are disjoint in the actual injective pushout.

The local fact, proved in ActualStepInterfaceSeparation, is
propagated through the ENTIRE original finite source-named chain.
The decisive induction invariant records:
* disjointness of the embedded common-interface POINT SETS
  belonging to every consecutive pair of historical boundaries;
* the fact that the LAST boundary lies in the old last-block entry.

Old disjointness survives the next injective old-side embedding.
The new final pair is disjoint by the original step entry/exit
condition. This works without choosing a group at the full stage
S, without forgetting historical block occurrences, and without
asserting any normalized separation as an extra hypothesis.

The theorem is the geometric image-disjointness input for
transporting the actual incoming/outgoing K_(M∩A) cosets of every
active interval through the verified pointwise source charts.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w t
variable {X : Type u} {Y : Type v}
variable {A : Type w} {B : Type t}

/-- Injective maps preserve disjointness of two arbitrary
source-image sets. This is the exact point-set argument needed
when the old original quotient is embedded into the next one. -/
theorem disjoint_ranges_comp_of_injective
    (i : X → Y) (hi : Function.Injective i)
    (f : A → X) (g : B → X)
    (h : Disjoint (Set.range f) (Set.range g)) :
    Disjoint (Set.range (fun a => i (f a)))
      (Set.range (fun b => i (g b))) := by
  apply Set.disjoint_left.mpr
  intro z hzF hzG
  obtain ⟨a, ha⟩ := hzF
  obtain ⟨b, hb⟩ := hzG
  have hfg : f a = g b := hi (ha.trans hb.symm)
  exact (Set.disjoint_left.mp h)
    ⟨a, rfl⟩ ⟨b, hfg.symm⟩

end GluingEPPA.Steiner.ChainValuation

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

/-- The genuine common-interface images of every consecutive
historical boundary pair are disjoint in the LITERAL original
quotient. These are sets of points, not merely source-mask labels. -/
def HistoricalBoundaryList.AdjacentInterfacesDisjoint
    {M : Proper S} {R : BuildResult D S old L} :
    List (AlignedNamedBoundary D S old L M R) → Prop
  | [] => True
  | [_] => True
  | P :: Q :: tail =>
      Disjoint
        (Set.range (P.boundary.interfaceMap D S old L))
        (Set.range (Q.boundary.interfaceMap D S old L)) ∧
      HistoricalBoundaryList.AdjacentInterfacesDisjoint
        D S old L (Q :: tail)

/-- Transporting a genuine old historical interface through one
later literal LinkChain.step composes the interface point map
with the SAME injective old-side pushout embedding. -/
theorem AlignedNamedBoundary.transport_interface_map
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (k : (old (common S P.boundary.leftMask
      P.boundary.rightMask)).Carrier) :
    ((P.transport D S old L y hsep hcoset).boundary.interfaceMap
      D S old L k) =
      oldEmbed (block S old R.current.1) (block S old y.1)
        R.state R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1)
        (P.boundary.interfaceMap D S old L k) := rfl

/-- Injectivity of the genuine old-side inclusion preserves the
disjointness of two REAL historical interface images. -/
theorem alignedBoundary_transport_interface_disjoint
    {M : Proper S} {R : BuildResult D S old L}
    (P Q : AlignedNamedBoundary D S old L M R)
    (hdisj : Disjoint
      (Set.range (P.boundary.interfaceMap D S old L))
      (Set.range (Q.boundary.interfaceMap D S old L)))
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    Disjoint
      (Set.range
        ((P.transport D S old L y hsep hcoset).boundary.interfaceMap
          D S old L))
      (Set.range
        ((Q.transport D S old L y hsep hcoset).boundary.interfaceMap
          D S old L)) := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hi := left_injective D S old L R.current.1 y.1
  let hj := right_injective D S old L R.current.1 y.1
  change Disjoint
    (Set.range (fun k => oldEmbed A B R.state R.current.2
      i j hi hj (P.boundary.interfaceMap D S old L k)))
    (Set.range (fun k => oldEmbed A B R.state R.current.2
      i j hi hj (Q.boundary.interfaceMap D S old L k)))
  exact disjoint_ranges_comp_of_injective
    (oldEmbed A B R.state R.current.2 i j hi hj)
    (oldEmbed_injective A B R.state R.current.2 i j hi hj)
    (P.boundary.interfaceMap D S old L)
    (Q.boundary.interfaceMap D S old L) hdisj

/-- Every earlier consecutive interface disjointness remains true
after an additional actual LinkChain attachment. -/
theorem historicalBoundaryList_transport_adjacentDisjoint
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R))
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L hist →
    HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L
      (hist.map (fun P =>
        P.transport D S old L y hsep hcoset)) := by
  induction hist with
  | nil =>
      intro _
      trivial
  | cons P rest ih =>
      intro hOld
      cases rest with
      | nil =>
          trivial
      | cons Q tail =>
          have hpair : Disjoint
              (Set.range (P.boundary.interfaceMap D S old L))
              (Set.range (Q.boundary.interfaceMap D S old L)) :=
            hOld.1
          have htail :
              HistoricalBoundaryList.AdjacentInterfacesDisjoint
                D S old L (Q :: tail) :=
            hOld.2
          change
            Disjoint
              (Set.range
                ((P.transport D S old L y hsep hcoset).boundary.interfaceMap
                  D S old L))
              (Set.range
                ((Q.transport D S old L y hsep hcoset).boundary.interfaceMap
                  D S old L)) ∧
            HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L
              ((Q :: tail).map (fun T =>
                T.transport D S old L y hsep hcoset))
          exact ⟨alignedBoundary_transport_interface_disjoint
            D S old L P Q hpair y hsep hcoset, ih htail⟩

/-- Appending one genuine fresh historical boundary to a list
whose earlier adjacent interfaces are disjoint preserves the
whole-list invariant, provided the previous last interface and
the fresh interface are themselves disjoint. -/
theorem historicalBoundaryList_append_fresh
    {M : Proper S} {R : BuildResult D S old L}
    (pre : List (AlignedNamedBoundary D S old L M R))
    (P Q : AlignedNamedBoundary D S old L M R)
    (hOld : HistoricalBoundaryList.AdjacentInterfacesDisjoint
      D S old L (pre ++ [P]))
    (hCross : Disjoint
      (Set.range (P.boundary.interfaceMap D S old L))
      (Set.range (Q.boundary.interfaceMap D S old L))) :
    HistoricalBoundaryList.AdjacentInterfacesDisjoint
      D S old L (pre ++ [P, Q]) := by
  induction pre with
  | nil =>
      exact ⟨hCross, trivial⟩
  | cons a rest ih =>
      cases rest with
      | nil =>
          change Disjoint
            (Set.range (a.boundary.interfaceMap D S old L))
            (Set.range (P.boundary.interfaceMap D S old L)) ∧ True
            at hOld
          change Disjoint
            (Set.range (a.boundary.interfaceMap D S old L))
            (Set.range (P.boundary.interfaceMap D S old L)) ∧
            (Disjoint
              (Set.range (P.boundary.interfaceMap D S old L))
              (Set.range (Q.boundary.interfaceMap D S old L)) ∧ True)
          exact ⟨hOld.1, ⟨hCross, trivial⟩⟩
      | cons b tail =>
          change Disjoint
            (Set.range (a.boundary.interfaceMap D S old L))
            (Set.range (b.boundary.interfaceMap D S old L)) ∧
            HistoricalBoundaryList.AdjacentInterfacesDisjoint
              D S old L ((b :: tail) ++ [P]) at hOld
          change Disjoint
            (Set.range (a.boundary.interfaceMap D S old L))
            (Set.range (b.boundary.interfaceMap D S old L)) ∧
            HistoricalBoundaryList.AdjacentInterfacesDisjoint
              D S old L ((b :: tail) ++ [P, Q])
          exact ⟨hOld.1, ih hOld.2⟩

/-- In one literal separated LinkChain.step, all earlier historical
interface separations persist, and the fresh final pair is disjoint
because its previous member lies in the old last-block entry set.

This step uses the ACTUAL old/fresh pushout separation theorem,
not a normalized separation assumed by the induction. -/
theorem coveredNamedAlignedStep_adjacentInterfacesDisjoint
    (M : Proper S)
    (H : CoveredNamedAlignedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.named.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
          H.named.data.chain.current y)
    (hOld : HistoricalBoundaryList.AdjacentInterfacesDisjoint
      D S old L H.aligned)
    (hLast : H.LastInterfaceIsEntry D S old L) :
    HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L
      (coveredNamedAlignedStep D S old L M H y hsep).aligned := by
  let R := H.named.data.chain
  let hcoset := H.named.data.lastInv
  let fresh := alignedNamedBoundaryFresh
    D S old L M R y hsep hcoset
  let trans := fun P : AlignedNamedBoundary D S old L M R =>
    P.transport D S old L y hsep hcoset
  have hTrans : HistoricalBoundaryList.AdjacentInterfacesDisjoint
      D S old L (H.aligned.map trans) :=
    historicalBoundaryList_transport_adjacentDisjoint
      D S old L H.aligned y hsep hcoset hOld
  change HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L
    (H.aligned.map trans ++ [fresh])
  rcases hLast with hEmpty | ⟨pre, P, hList, hEntry⟩
  · rw [hEmpty]
    trivial
  · have hMap :
        H.aligned.map trans = pre.map trans ++ [trans P] := by
      rw [hList]
      simp only [List.map_append, List.map_singleton]
    have hCross : Disjoint
        (Set.range ((trans P).boundary.interfaceMap D S old L))
        (Set.range (fresh.boundary.interfaceMap D S old L)) := by
      let A := block S old R.current.1
      let B := block S old y.1
      let i := left D S old L R.current.1 y.1
      let j := right D S old L R.current.1 y.1
      let hi := left_injective D S old L R.current.1 y.1
      let hj := right_injective D S old L R.current.1 y.1
      change Disjoint
        (Set.range (fun k => oldEmbed A B R.state R.current.2
          i j hi hj (P.boundary.interfaceMap D S old L k)))
        (Set.range (fresh.boundary.interfaceMap D S old L))
      have hRight :
          (fresh.boundary.interfaceMap D S old L) =
          (fun k => newEmbed A B R.state R.current.2
            i j hi hj (j k)) := by
        funext k
        exact fresh.boundary.interfaceMap_eq_right D S old L k
      rw [hRight]
      exact step_historical_entry_disjoint_fresh_interface
        D S old L M R y hsep P.boundary hEntry
    rw [hMap] at hTrans ⊢
    exact historicalBoundaryList_append_fresh D S old L
      (pre.map trans) (trans P) fresh hTrans hCross

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
