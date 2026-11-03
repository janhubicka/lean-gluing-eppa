import GluingEPPA.Steiner.ChainValuation.RegularComponentCover
import GluingEPPA.Steiner.ChainValuation.ChainWordTransport

/-!
# Regular restricted components at the final Cayley block

Fix a previously constructed smaller-mask group K_M embedded in the last
block K_A of a chain state, with its named generators preserved. A translated
K_M coset at that block carries the literal M-letter transitions of the
whole chain. Its image therefore equals an entire restricted word component.

This discharges the regular-block case of the geometric covering
classification for the last block. The remaining case is components
containing only proper restricted block alphabets.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u}
variable {M : Finset E}
variable (A : EdgeGraph.RecursiveRecord.Data E M)
variable (B : GroupBlock E) (C : ChainState E B)
variable (i : A.Carrier →* B.Carrier)
variable (hM : ∀ e ∈ M, e ∈ B.active)
variable (hi : ∀ e ∈ M, i (A.edge e) = B.edge e)

/-- The inclusion of a translated smaller-mask coset is equivariant
for every M-letter in the complete chain test. -/
theorem lastBlock_regular_coset_letter
    (g : B.Carrier) (e : E) (he : e ∈ M) (k : A.Carrier) :
    C.lastEmbed (g * i (k * A.edge e)) =
      (C.matching e).perm (C.lastEmbed (g * i k)) := by
  have hstep := (C.matching e).perm_eq_of_rel
    (C.last_active e (hM e he) (g * i k))
  calc
    C.lastEmbed (g * i (k * A.edge e)) =
        C.lastEmbed ((g * i k) * B.edge e) := by
          rw [map_mul, hi e he, mul_assoc]
    _ = (C.matching e).perm (C.lastEmbed (g * i k)) := hstep.symm

/-- Every M-word component that meets this translated regular Cayley coset
is already covered by the coset. This does not assume the embedding is
injective and does not require the surrounding chain to have one block. -/
theorem lastBlock_regular_coset_component
    (g : B.Carrier) (k : A.Carrier) :
    Set.range (fun t : A.Carrier => C.lastEmbed (g * i t)) =
      EdgeGraph.RecursiveRecord.ChainValuation.wordReach
        (fun e => (C.matching e).perm) (S := M)
        (C.lastEmbed (g * i k)) := by
  exact EdgeGraph.RecursiveRecord.ChainValuation.regular_cover_is_component
    (fun e => (C.matching e).perm) A
    (fun t => C.lastEmbed (g * i t))
    (fun e he t =>
      lastBlock_regular_coset_letter A B C i hM hi g e he t)
    k

end GluingEPPA.Steiner.ChainValuation
