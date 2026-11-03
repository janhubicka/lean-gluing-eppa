import GluingEPPA.Steiner.ChainValuation.ChainAttach
import GluingEPPA.Steiner.ChainValuation.WordAction

/-!
# Transporting words along a chain's embedded Cayley blocks

A word in the alphabet of the last block follows that block's right Cayley
action, even when the block is part of a longer chain. Every genuine old
matching edge survives one further exact attachment. This is the local
word-action input needed for unrolling a coset cycle through its chain test.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u}
variable (B : GroupBlock E) (C : ChainState E B)

/-- Read the completed matching permutations of a chain from left to right. -/
noncomputable def chainWordPerm (w : List E) : Equiv.Perm C.Space :=
  GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
    (fun e => (C.matching e).perm) w

/-- Every word in the last block's alphabet transports precisely by its
right Cayley value on the embedded last block. -/
theorem lastBlock_word (w : List E)
    (hw : ∀ e ∈ w, e ∈ B.active) (g : B.Carrier) :
    chainWordPerm B C w (C.lastEmbed g) =
      C.lastEmbed (g * (w.map B.edge).prod) := by
  induction w generalizing g with
  | nil =>
      simp [chainWordPerm,
        GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm]
  | cons e w ih =>
      have he : e ∈ B.active := hw e (by simp)
      have htail : ∀ f ∈ w, f ∈ B.active :=
        fun f hf => hw f (by simp [hf])
      have hstep : (C.matching e).perm (C.lastEmbed g) =
          C.lastEmbed (g * B.edge e) :=
        (C.matching e).perm_eq_of_rel (C.last_active e he g)
      change chainWordPerm B C w
        ((C.matching e).perm (C.lastEmbed g)) =
          C.lastEmbed (g * ((e :: w).map B.edge).prod)
      rw [hstep, ih htail (g * B.edge e)]
      simp only [List.map_cons, List.prod_cons, mul_assoc]

variable {K : Type v} [Group K]
variable (A : GroupBlock E) (D : ChainState E A)
variable (h : A.Carrier)
variable (left : K →* A.Carrier) (right : K →* B.Carrier)
variable (hleft : Function.Injective left) (hright : Function.Injective right)
variable (hsep : Disjoint D.entry (exitSet A h left))
variable (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
  ∃ k : K, left k = A.edge e ∧ right k = B.edge e)

/-- A genuine old labelled edge is still a labelled edge after extending
the chain. Its endpoints are the images under the old-block injection. -/
theorem old_edge_survives (e : E) {x y : D.Space}
    (hxy : (D.matching e).Rel x y) :
    ((extend A B D h left right hleft hright hsep hshared).matching e).Rel
      (oldEmbed A B D h left right hleft hright x)
      (oldEmbed A B D h left right hleft hright y) := by
  exact Or.inl ⟨x, y, hxy, rfl, rfl⟩

/-- The completed new letter permutation follows every old existing edge. -/
theorem old_edge_survives_perm (e : E) {x y : D.Space}
    (hxy : (D.matching e).Rel x y) :
    ((extend A B D h left right hleft hright hsep hshared).matching e).perm
      (oldEmbed A B D h left right hleft hright x) =
      oldEmbed A B D h left right hleft hright y := by
  exact ((extend A B D h left right hleft hright hsep hshared).matching e).perm_eq_of_rel
    (old_edge_survives B A D h left right hleft hright hsep hshared e hxy)

end GluingEPPA.Steiner.ChainValuation
