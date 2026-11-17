import GluingEPPA.Steiner.ChainValuation.NormalizedTwoBlockComponent
import GluingEPPA.Steiner.ChainValuation.NormalizedProperRawChain

/-!
# Construction traces for the exact normalized source chain states

An arbitrary `ChainState` is not sufficient evidence that a component
chart comes from a finite earlier chain test. A normalized construction
trace starts at one actual restricted Cayley block and attaches one
further actual restricted block at a time, with the literal normalized
Link maps and a proof of separation. It is indexed by the exact resulting
`ChainState`, so the source state cannot be replaced by an unrelated graph.

The trace remembers every original mask and outgoing shift. Supplying
the unused last shift recursively produces the ordered source list
without changing a previously built quotient. This supplies source
provenance and exact block counts for the component-chart induction.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- An actual finite succession of separated normalized attachments,
indexed by its resulting source state. -/
inductive NormalizedChainTrace (M : Proper S) :
    (A : Proper S) → ChainState.{u,u} E (block S old (Step.meet S M A)) →
      Type (u + 1)
  | single (A : Proper S) :
      NormalizedChainTrace M A (ChainState.first (block S old (Step.meet S M A)))
  | attach {A : Proper S}
      {C : ChainState.{u,u} E (block S old (Step.meet S M A))}
      (previous : NormalizedChainTrace M A C) (B : Proper S)
      (shift : (old (Step.meet S M A)).Carrier)
      (hsep : Disjoint C.entry
        (exitSet (block S old (Step.meet S M A)) shift
          (normalizedCommonLeft D S old L M A B)))
      (hshared : ∀ e,
        e ∈ (block S old (Step.meet S M A)).active →
        e ∈ (block S old (Step.meet S M B)).active →
        ∃ t : (old (Step.meet S M (common S A B))).Carrier,
          normalizedCommonLeft D S old L M A B t =
            (block S old (Step.meet S M A)).edge e ∧
          normalizedCommonRight D S old L M A B t =
            (block S old (Step.meet S M B)).edge e) :
      NormalizedChainTrace M B
        (GluingEPPA.Steiner.ChainValuation.extend
          (block S old (Step.meet S M A)) (block S old (Step.meet S M B))
          C shift
          (normalizedCommonLeft D S old L M A B)
          (normalizedCommonRight D S old L M A B)
          (normalizedCommonLeft_injective D S old L M A B)
          (normalizedCommonRight_injective D S old L M A B) hsep hshared)

namespace NormalizedChainTrace

variable {D S old L}
variable {M A : Proper S}
variable {C : ChainState.{u,u} E (block S old (Step.meet S M A))}

def masks {A : Proper S}
    {C : ChainState.{u,u} E (block S old (Step.meet S M A))}
    (T : NormalizedChainTrace D S old L M A C) : List (Proper S) :=
  match T with
  | .single B => [B]
  | .attach previous B _ _ _ => previous.masks ++ [B]

def length (T : NormalizedChainTrace D S old L M A C) : Nat := T.masks.length

@[simp] theorem masks_single (B : Proper S) :
    (single (D := D) (S := S) (old := old) (L := L) (M := M) B).masks = [B] := rfl

theorem last_mem_masks (T : NormalizedChainTrace D S old L M A C) :
    A ∈ T.masks := by
  cases T with
  | single A => simp [masks]
  | attach previous B shift hsep hshared => simp [masks]

theorem masks_ne_nil (T : NormalizedChainTrace D S old L M A C) :
    T.masks ≠ [] := by
  intro h
  have hmem := T.last_mem_masks
  rw [h] at hmem
  exact List.not_mem_nil hmem

theorem length_pos (T : NormalizedChainTrace D S old L M A C) : 0 < T.length :=
  List.length_pos_iff.mpr T.masks_ne_nil

/-- The exact ordered proper source list. The terminal shift is unused
in the current quotient; when another block is attached, the recursion
sets it to that attachment's chosen outgoing shift. -/
def sources {A : Proper S}
    {C : ChainState.{u,u} E (block S old (Step.meet S M A))}
    (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (terminalShift : (old (Step.meet S M A)).Carrier) :
    List (NormalizedProperSource S old M) :=
  match T with
  | .single B =>
      [⟨B, hproper B (by simp [masks]), terminalShift⟩]
  | .attach previous B shift _ _ =>
      previous.sources
        (fun A hA => hproper A (by simp [masks, hA])) shift ++
      [⟨B, hproper B (by simp [masks]), terminalShift⟩]

theorem sources_masks (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (terminalShift : (old (Step.meet S M A)).Carrier) :
    (T.sources hproper terminalShift).map NormalizedProperSource.mask = T.masks := by
  induction T with
  | single B => rfl
  | attach previous B shift hsep hshared ih =>
      simp only [sources, List.map_append, List.map_cons, List.map_nil, masks]
      rw [ih]

theorem sources_length (T : NormalizedChainTrace D S old L M A C)
    (hproper : ∀ B ∈ T.masks, ¬ M.val ⊆ B.val)
    (terminalShift : (old (Step.meet S M A)).Carrier) :
    (T.sources hproper terminalShift).length = T.length := by
  have h := congrArg List.length (T.sources_masks hproper terminalShift)
  simpa only [List.length_map, length] using h

end NormalizedChainTrace

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
