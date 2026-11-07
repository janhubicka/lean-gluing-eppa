import GluingEPPA.Steiner.ChainValuation.HistoricalNewRootSupport

/-!
# The complete one-step consecutive-support induction

Assume every M-component of the old actual chain meets a
consecutive interval of historical blocks, and the recorded
history ends with its true last-block chart.

After an injective separated attachment with compatible M-component
pullbacks, every component of the new actual chain likewise has
consecutive support. The proof handles all three possibilities:
- an old-root component, using the verified last-chart transition;
- a new root matched to an old component by one attachment;
- a new root which meets no attachment parameter, whose whole
  support consists of the single newly appended last block.

No global K_S is used, and no unsupported blanket assumption that
all new components meet the old chain is made.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- All M-components of a historical chain have consecutive block support. -/
def AllComponentsConsecutive
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (history : List (HistoricalBlock A C M)) : Prop :=
  ∀ q : C.Space, IsConsecutiveSupport (historicalSupport A C M history q)

/-- One genuine separated attachment preserves the consecutive support
of every M-component, including those rooted in the new Cayley block. -/
theorem historicalBlocks_extend_allConsecutive
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (Q : Subgroup B.Carrier)
    (hnew : LastBlockCosetInvariant B
      (extend A B C h left right hl hr hsep hshared) M Q)
    (history : List (HistoricalBlock A C M))
    (hOld : AllComponentsConsecutive A C M history)
    (hLast : HasLastHistoricalChart A C M history) :
    AllComponentsConsecutive B
      (extend A B C h left right hl hr hsep hshared) M
      (historicalBlocks_extend A B C h left right hl hr
        hsep hshared M hpull Q hnew history) := by
  let C' := extend A B C h left right hl hr hsep hshared
  let hist' := historicalBlocks_extend
    A B C h left right hl hr hsep hshared M hpull Q hnew history
  intro q
  refine Quotient.inductionOn q ?_
  intro s
  cases s with
  | inl x =>
      exact historicalSupport_extend_old_consecutive_of_lastChart
        A B C h left right hl hr hsep hshared M hpull Q hnew
        history x (hOld x) hLast
  | inr y =>
      change IsConsecutiveSupport
        (historicalSupport B C' M hist'
          (newEmbed A B C h left right hl hr y))
      by_cases hmatch :
          ∃ k : K, LabelReach (fun e => (B.matching e).Rel) M y (right k)
      · obtain ⟨k, hyk⟩ := hmatch
        have hreach := extended_newRoot_reach_old_interface
          A B C h left right hl hr hsep hshared M y k hyk
        have hsame := historicalSupport_eq_of_reach
          B C' M hist'
          (newEmbed A B C h left right hl hr y)
          (oldEmbed A B C h left right hl hr
            (attachInto C.lastEmbed h left k))
          hreach
        rw [hsame]
        exact historicalSupport_extend_old_consecutive_of_lastChart
          A B C h left right hl hr hsep hshared M hpull Q hnew
          history (attachInto C.lastEmbed h left k)
          (hOld (attachInto C.lastEmbed h left k)) hLast
      · have hnomatch : ∀ k : K,
            ¬ LabelReach (fun e => (B.matching e).Rel) M y (right k) := by
          intro k hk
          exact hmatch ⟨k, hk⟩
        let oldHist := history.map (fun T =>
          T.transport A B C h left right hl hr hsep hshared M hpull)
        let pref := historicalSupport B C' M oldHist
          (newEmbed A B C h left right hl hr y)
        have hInactive : AllInactive pref := by
          unfold AllInactive pref oldHist
          induction history with
          | nil =>
              intro p hp
              simp [historicalSupport] at hp
          | cons T ts ih =>
              intro p hp
              change p ∈
                ((T.transport A B C h left right hl hr hsep hshared M hpull).Meets
                   B C' M (newEmbed A B C h left right hl hr y)) ::
                  historicalSupport B C' M
                    (ts.map (fun T => T.transport A B C h left right
                      hl hr hsep hshared M hpull))
                    (newEmbed A B C h left right hl hr y) at hp
              rcases List.mem_cons.mp hp with heq | htail
              · subst p
                exact T.transport_new_unmatched
                  A B C h left right hl hr hsep hshared M hpull y hnomatch
              · exact ih p htail
        let lastP : Prop :=
          (historicalBlock_last B C' M Q hnew).Meets
            B C' M (newEmbed A B C h left right hl hr y)
        have hLastP : lastP := ⟨y, LabelReach.refl _⟩
        have hsplit :
            historicalSupport B C' M hist'
              (newEmbed A B C h left right hl hr y) =
            pref ++ [lastP] := by
          simp [historicalSupport, historicalBlocks_extend, pref, oldHist, hist']
        have hEq : lastP = True := propext
          ⟨fun _ => True.intro, fun _ => hLastP⟩
        rw [hsplit, hEq]
        exact activeSuffix_isConsecutive
          (pref ++ [True]) (inactivePrefix_append_active pref hInactive)

end GluingEPPA.Steiner.ChainValuation
