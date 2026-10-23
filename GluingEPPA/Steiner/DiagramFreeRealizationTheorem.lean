import GluingEPPA.Steiner.DiagramRealizationConsequences

/-!
# General finite free realization of closed Steiner gluing diagrams

This is the direct theorem corresponding to the main manuscript's
free-realization lemma. It applies to ANY finite labelled gluing diagram
whose overlaps are closed and whose local systems are partial Steiner
triple systems, not merely to the specially constructed EPPA input graph.

The quotient is finite and again a partial Steiner triple system;
every canonical copy is injective, induced, and closed. The result
packages previous independent proofs of exact component intersection,
triple transport and closure, with no new axioms.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- The full free-realization conclusion for a finite diagram with
point-labelled closed Steiner overlaps. -/
structure FreeRealizationCertificate (L : LabelledSteiner D Ω) where
  finite : Finite (realizedPoint D L)
  triple_unique : ∀ p q r s : realizedPoint D L,
    realizedTriple D L p q r → realizedTriple D L p q s → r = s
  triple_swap : ∀ p q r : realizedPoint D L,
    realizedTriple D L p q r → realizedTriple D L q p r
  triple_rotate : ∀ p q r : realizedPoint D L,
    realizedTriple D L p q r → realizedTriple D L q r p
  triple_distinct : ∀ p q r : realizedPoint D L,
    realizedTriple D L p q r → p ≠ q ∧ p ≠ r ∧ q ≠ r
  local_injective :
    ∀ (u : V) (g : (family D Finset.univ).Carrier),
      Function.Injective (fun x : {x : Ω // L.present u x} =>
        canonicalPoint D L u g x.val x.property)
  local_induced :
    ∀ (u : V) (g : (family D Finset.univ).Carrier)
      (x y z : Ω) (hx : L.present u x)
      (hy : L.present u y) (hz : L.present u z),
      realizedTriple D L
        (canonicalPoint D L u g x hx)
        (canonicalPoint D L u g y hy)
        (canonicalPoint D L u g z hz) ↔ L.triple u x y z
  local_closed :
    ∀ (u : V) (g : (family D Finset.univ).Carrier)
      (x y : Ω) (hx : L.present u x) (hy : L.present u y)
      (q : realizedPoint D L),
      realizedTriple D L
        (canonicalPoint D L u g x hx)
        (canonicalPoint D L u g y hy) q →
      ∃ (z : Ω) (hz : L.triple u x y z),
        q = canonicalPoint D L u g z
          ((L.triple_present u x y z hz).2.2)

/-- Exact general free realization: finite partial Steiner quotient
with all canonical local copies closed and induced. -/
noncomputable def closedSteinerFreeRealization
    (L : LabelledSteiner D Ω) [Finite Ω] :
    FreeRealizationCertificate D L where
  finite := by infer_instance
  triple_unique := by
    intro p q r s hr hs
    exact realizedTriple_unique D L p q r s hr hs
  triple_swap := by
    intro p q r h
    exact realizedTriple_swap D L p q r h
  triple_rotate := by
    intro p q r h
    exact realizedTriple_rotate D L p q r h
  triple_distinct := by
    intro p q r h
    exact realizedTriple_distinct D L p q r h
  local_injective := by
    intro u g x y h
    apply Subtype.ext
    exact canonicalPoint_eq_label D L u u g g
      x.val y.val x.property y.property h
  local_induced := by
    intro u g x y z hx hy hz
    exact canonicalPoint_triple_iff D L u g x y z hx hy hz
  local_closed := by
    intro u g x y hx hy q h
    exact realizedTriple_closed D L u g x y hx hy q h

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
