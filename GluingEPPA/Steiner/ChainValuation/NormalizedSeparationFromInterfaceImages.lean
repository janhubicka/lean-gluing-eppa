import GluingEPPA.Steiner.ChainValuation.ActualNormalizedTripleSeparation

/-!
# Normalized interface cosets inherit disjointness of actual interface images

The missing all-interval chain restriction proof has two separate
inputs. The ORIGINAL finite separated LinkChain supplies disjoint
genuine interface images at consecutive historical boundaries.
The normalized component chart supplies translated subgroups
K_(M ∩ A) and full restricted common-interface cosets.

This module isolates their exact algebraic combination. Two
different original interface maps may take values in one actual
quotient point type X, and need not themselves be injective.
If their image sets are disjoint and the ORIGINAL common-parameter
groups commute with the normalized inclusions, then the two
normalized interface cosets are disjoint.

The proof is valid for arbitrary NONCOMMUTATIVE groups. It does
not assume an ambient group K_S, an abstract replacement quotient,
or any unverified preservation of normalized separation. No
additional hypothesis of disjoint original source GROUP cosets
is necessary: that follows from the disjoint point images under
the real original Cayley chart.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w x a b c
variable {G : Type u} {P : Type v}
variable {H : Type w} {K : Type x}
variable {C : Type a} {D : Type b}
variable {X : Type c}
variable [Group G] [Group P] [Group H] [Group K]
variable [Group C] [Group D]

/-- A translated original subgroup coset maps wholly into the
image of its genuine historical interface map. The map F
need not be injective: only its exact value on original
attachment coordinates is needed. -/
theorem translated_coset_maps_into_interface_image
    (i : H →* G) (F : G → X) (interface : H → X)
    (h : G)
    (hChart : ∀ k : H, F (h * i k) = interface k)
    (z : G) (hz : z ∈ leftCoset i.range h) :
    F z ∈ Set.range interface := by
  change h⁻¹ * z ∈ i.range at hz
  obtain ⟨k, hk⟩ := hz
  have hpoint : z = h * i k := by
    calc
      z = h * (h⁻¹ * z) := by group
      _ = h * i k := by rw [← hk]
  rw [hpoint]
  exact ⟨k, (hChart k).symm⟩

/-- The original genuine incoming and outgoing interface images
being DISJOINT implies that the two normalized interface cosets
are disjoint in the actual smaller Cayley group.

The translated base equations may be different on the two sides.
All products are in their original NONCOMMUTATIVE word order.
Neither the original common groups H,K nor their restricted
subgroups C,D have to coincide. -/
theorem normalized_interface_cosets_disjoint_of_images
    (p : P →* G)
    (iIn : H →* G) (iOut : K →* G)
    (aIn : C →* P) (aOut : D →* P)
    (rIn : C →* H) (rOut : D →* K)
    (hcommIn : p.comp aIn = iIn.comp rIn)
    (hcommOut : p.comp aOut = iOut.comp rOut)
    (g hIn hOut : G) (kIn : H) (kOut : K)
    (uIn uOut : P)
    (hbaseIn : g * p uIn = hIn * iIn kIn)
    (hbaseOut : g * p uOut = hOut * iOut kOut)
    (F : G → X) (interfaceIn : H → X)
    (interfaceOut : K → X)
    (hChartIn : ∀ k : H,
      F (hIn * iIn k) = interfaceIn k)
    (hChartOut : ∀ k : K,
      F (hOut * iOut k) = interfaceOut k)
    (hImagesDisjoint :
      Disjoint (Set.range interfaceIn) (Set.range interfaceOut)) :
    Disjoint
      (leftCoset aIn.range uIn)
      (leftCoset aOut.range uOut) := by
  apply Set.disjoint_left.mpr
  intro t htIn htOut
  have hOrigIn : g * p t ∈ leftCoset iIn.range hIn :=
    normalized_interface_coset_maps_into
      iIn p rIn aIn hcommIn
      g hIn kIn uIn hbaseIn t htIn
  have hOrigOut : g * p t ∈ leftCoset iOut.range hOut :=
    normalized_interface_coset_maps_into
      iOut p rOut aOut hcommOut
      g hOut kOut uOut hbaseOut t htOut
  have hImageIn : F (g * p t) ∈ Set.range interfaceIn :=
    translated_coset_maps_into_interface_image
      iIn F interfaceIn hIn hChartIn (g * p t) hOrigIn
  have hImageOut : F (g * p t) ∈ Set.range interfaceOut :=
    translated_coset_maps_into_interface_image
      iOut F interfaceOut hOut hChartOut (g * p t) hOrigOut
  exact (Set.disjoint_left.mp hImagesDisjoint) hImageIn hImageOut

end GluingEPPA.Steiner.ChainValuation
