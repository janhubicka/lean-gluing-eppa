import GluingEPPA.Steiner.ChainValuation.ActualNormalizedSeparation

/-!
# The actual normalized triple interfaces are separated

For three consecutive historical Link blocks Aprev, A, Anext,
the original separation condition is disjointness of the true
incoming and outgoing attaching cosets in K_A.

A normalized M-component uses a translated K_(M∩A) coset
whose entry and exit interfaces are *full cosets* of the
corresponding images of K_(M∩Aprev∩A) and K_(M∩A∩Anext).

If the selected entry and exit have actual attaching witnesses
(the precise shift equations), then the two normalized interface
cosets are disjoint. The proof uses genuine Link commutation
squares and the actual tripleSeparated assumption, not merely
an abstract preimage subset or a presumed normalized diagram.

The choice of these representatives along an arbitrary component
remains part of the all-length chart induction.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u
variable {H P G C : Type u}
variable [Group H] [Group P] [Group G] [Group C]

/-- A normalized interface coset maps wholly into the original
attaching coset whenever the translated base points agree.
This is valid in arbitrary noncommutative groups. -/
theorem normalized_interface_coset_maps_into
    (i : H →* G) (p : P →* G)
    (r : C →* H) (a : C →* P)
    (hcomm : p.comp a = i.comp r)
    (g h : G) (k : H) (shift : P)
    (hbase : g * p shift = h * i k)
    (t : P) (ht : t ∈ leftCoset a.range shift) :
    g * p t ∈ leftCoset i.range h := by
  change shift⁻¹ * t ∈ a.range at ht
  obtain ⟨c, hc⟩ := ht
  have ht' : t = shift * a c := by
    have eq : shift * (shift⁻¹ * t) = t := by group
    rw [hc] at eq
    exact eq.symm
  rw [ht']
  have hpoint : g * p (shift * a c) = h * i (k * r c) :=
    normalized_old_boundary i p r a hcomm g h k shift hbase c
  change h⁻¹ * (g * p (shift * a c)) ∈ i.range
  rw [hpoint]
  have hi : i (k * r c) ∈ i.range := ⟨k * r c, rfl⟩
  simpa only [inv_mul_cancel_left] using hi

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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- Concrete normalized separation at an actual interior Link
block. The entry base lies in the literal original entry coset,
and the exit base lies in the literal original outgoing attachment.
Therefore *the entire* normalized entry and exit cosets are disjoint.

No normalization operation is assumed to preserve separation:
it is proved from the two genuine subgroup-inclusion squares. -/
theorem actual_normalizedTripleSeparated
    (M : Proper S) (x y z : Atom S old)
    (g : (old y.1).Carrier)
    (kIn : (old (common S x.1 y.1)).Carrier)
    (kOut : (old (common S y.1 z.1)).Carrier)
    (uIn uOut : (old (Step.meet S M y.1)).Carrier)
    (hIn :
      g * (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl uIn =
        right D S old L x.1 y.1 kIn)
    (hOut :
      g * (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl uOut =
        y.2 * left D S old L y.1 z.1 kOut)
    (hsep : tripleSeparated D S old L x y z) :
    Disjoint
      (leftCoset
        (normalizedCommonRight D S old L M x.1 y.1).range uIn)
      (leftCoset
        (normalizedCommonLeft D S old L M y.1 z.1).range uOut) := by
  let p := (L (Step.meet S M y.1) y.1
    Finset.inter_subset_right).incl
  apply Set.disjoint_left.mpr
  intro t htIn htOut
  have hin : g * p t ∈
      leftCoset (right D S old L x.1 y.1).range 1 := by
    apply normalized_interface_coset_maps_into
      (right D S old L x.1 y.1) p
      (normalizedCommonInterface D S old L M x.1 y.1)
      (normalizedCommonRight D S old L M x.1 y.1)
      (normalizedCommon_right_square D S old L M x.1 y.1)
      g 1 kIn uIn
    · simpa only [one_mul] using hIn
    · exact htIn
  have hout : g * p t ∈
      leftCoset (left D S old L y.1 z.1).range y.2 := by
    apply normalized_interface_coset_maps_into
      (left D S old L y.1 z.1) p
      (normalizedCommonInterface D S old L M y.1 z.1)
      (normalizedCommonLeft D S old L M y.1 z.1)
      (normalizedCommon_left_square D S old L M y.1 z.1)
      g y.2 kOut uOut
    · exact hOut
    · exact htOut
  exact (Set.disjoint_left.mp hsep) hin hout

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
