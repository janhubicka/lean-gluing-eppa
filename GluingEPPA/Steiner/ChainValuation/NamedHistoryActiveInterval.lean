import GluingEPPA.Steiner.ChainValuation.NamedHistoryConsecutiveSupport

/-!
# Extract an actual nonempty interval of named historical Cayley blocks

The consecutive-support theorem initially yields a list of truth
values, not a list of the original source-named Cayley blocks.
Lifting a decomposition of the Boolean/Prop support through List.map
is necessary: repeated source masks represent different historical
OCCURRENCES and cannot be deduplicated.

For every point q of the original finite separated LinkChain,
we construct a nonempty consecutive SUBLIST of its original named
historical charts, with all and only the blocks met by q's
actual M-component. The blocks before and after are not met.
The result uses actual historical chart coverage to prove
nonemptiness, and no arbitrary isomorphism of earlier groups.

This gives the exact block interval which the remaining normalized
proper-M chain must reconstruct.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {α : Type u} {β : Type v}

/-- Split a list at an explicitly given prefix of its mapped
list. The original elements and their occurrences are preserved. -/
private theorem map_append_split
    (f : α → β) (xs : List α) (pre rest : List β)
    (h : xs.map f = pre ++ rest) :
    ∃ front tail : List α,
      xs = front ++ tail ∧
      front.map f = pre ∧ tail.map f = rest := by
  induction pre generalizing xs with
  | nil =>
      refine ⟨[], xs, ?_, rfl, ?_⟩
      · simp
      · simpa using h
  | cons b bs ih =>
      cases xs with
      | nil =>
          simp at h
      | cons x xs =>
          have hcons :
              f x :: xs.map f = b :: (bs ++ rest) := by
            simpa only [List.map_cons, List.cons_append] using h
          have hhead : f x = b := (List.cons.inj hcons).1
          have htail : xs.map f = bs ++ rest :=
            (List.cons.inj hcons).2
          obtain ⟨front, tail, hxs, hfront, htailmap⟩ :=
            ih xs htail
          refine ⟨x :: front, tail, ?_, ?_, htailmap⟩
          · simp only [List.cons_append, hxs]
          · simp only [List.map_cons, hhead, hfront]

/-- An interval of true support bits lifts to an interval of the
original list, preserving positions, source identities and repetition.
The active sublist is nonempty as soon as some support bit is true. -/
theorem list_active_interval_of_consecutive_map
    (xs : List α) (P : α → Prop)
    (hconsecutive : IsConsecutiveSupport (xs.map P))
    (hsome : ∃ p : Prop, p ∈ xs.map P ∧ p) :
    ∃ front active back : List α,
      xs = front ++ active ++ back ∧
      active ≠ [] ∧
      (∀ x ∈ front, ¬ P x) ∧
      (∀ x ∈ active, P x) ∧
      (∀ x ∈ back, ¬ P x) := by
  obtain ⟨preBits, activeBits, postBits,
    hbits, hpre, hact, hpost⟩ := hconsecutive
  have hactiveNonempty : activeBits ≠ [] := by
    intro hempty
    obtain ⟨p, hp, htrue⟩ := hsome
    rw [hbits] at hp
    have hp' : p ∈ preBits ++ postBits := by
      simpa [hempty] using hp
    rcases List.mem_append.mp hp' with hmem | hmem
    · exact (hpre p hmem) htrue
    · exact (hpost p hmem) htrue
  have hsplit :
      xs.map P = preBits ++ (activeBits ++ postBits) := by
    simpa only [List.append_assoc] using hbits
  obtain ⟨front, tail, hxs, hfront, htail⟩ :=
    map_append_split P xs preBits (activeBits ++ postBits) hsplit
  obtain ⟨active, back, hrest, hactive, hback⟩ :=
    map_append_split P tail activeBits postBits htail
  have hne : active ≠ [] := by
    intro hempty
    apply hactiveNonempty
    rw [← hactive, hempty]
    rfl
  refine ⟨front, active, back, ?_, hne, ?_, ?_, ?_⟩
  · calc
      xs = front ++ tail := hxs
      _ = front ++ (active ++ back) := by rw [hrest]
      _ = front ++ active ++ back := by simp only [List.append_assoc]
  · intro x hx
    apply hpre (P x)
    rw [← hfront]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  · intro x hx
    apply hact (P x)
    rw [← hactive]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  · intro x hx
    apply hpost (P x)
    rw [← hback]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

/-- Coverage ensures some historical support bit is true:
q itself lies in a recorded source-block chart. -/
theorem historicalSupport_has_active_of_cover
    {E : Type u}
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E)
    (history : List (HistoricalBlock A C M))
    (hcover : HistoricalBlocksCover A C M history)
    (q : C.Space) :
    ∃ p : Prop, p ∈ historicalSupport A C M history q ∧ p := by
  obtain ⟨T, hT, x, hx⟩ := hcover q
  let p : Prop := T.Meets A C M q
  have hp : p := by
    refine ⟨x, ?_⟩
    rw [hx]
    exact LabelReach.refl q
  refine ⟨p, ?_, hp⟩
  change p ∈ history.map (fun T => T.Meets A C M q)
  exact List.mem_map.mpr ⟨T, hT, rfl⟩

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

/-- The true M-component support of EVERY q can be extracted as
a nonempty consecutive interval of the actual source-named
historical K_A block OCCURRENCES in LinkChain.buildNonempty.

Each block in active is reached from q by an M-labelled path,
and no block before/after active is. No repeated original mask
or distinct original attachment is collapsed. -/
theorem namedHistoryBuildNonempty_active_interval
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := namedHistoryBuildNonempty D S old L M atoms hne hsep
    ∀ q : H.data.chain.state.Space,
      ∃ front active back :
          List (NamedHistoricalBlock D S old L M H.data.chain),
        H.named = front ++ active ++ back ∧
        active ≠ [] ∧
        (∀ T ∈ front,
          ¬ ((T.toHistorical D S old L).Meets
            (block S old H.data.chain.current.1)
            H.data.chain.state M.val q)) ∧
        (∀ T ∈ active,
          (T.toHistorical D S old L).Meets
            (block S old H.data.chain.current.1)
            H.data.chain.state M.val q) ∧
        (∀ T ∈ back,
          ¬ ((T.toHistorical D S old L).Meets
            (block S old H.data.chain.current.1)
            H.data.chain.state M.val q)) := by
  intro H q
  let A := block S old H.data.chain.current.1
  let C := H.data.chain.state
  let P : NamedHistoricalBlock D S old L M H.data.chain → Prop :=
    fun T => (T.toHistorical D S old L).Meets A C M.val q
  have hmap :
      H.named.map P =
        historicalSupport A C M.val
          (H.named.map (fun T => T.toHistorical D S old L)) q := by
    simp only [historicalSupport, List.map_map, Function.comp_def, P]
  have hconsecutive : IsConsecutiveSupport (H.named.map P) := by
    rw [hmap]
    exact namedHistoryBuildNonempty_allConsecutive
      D S old L M atoms hne hsep q
  have hcover : HistoricalBlocksCover A C M.val
      (H.named.map (fun T => T.toHistorical D S old L)) :=
    H.covers D S old L M
  have hsome : ∃ p : Prop, p ∈ H.named.map P ∧ p := by
    rw [hmap]
    exact historicalSupport_has_active_of_cover A C M.val
      (H.named.map (fun T => T.toHistorical D S old L)) hcover q
  exact list_active_interval_of_consecutive_map
    H.named P hconsecutive hsome

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
