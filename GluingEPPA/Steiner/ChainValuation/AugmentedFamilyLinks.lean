import GluingEPPA.Steiner.ChainValuation.AugmentedFamilyActions

/-!
# Links for the actual chain-augmented recursive family

Strong induction supplies all proper-target Links.  Every proper group
already records its own bounded chain tests, by the same stage equation.
The checked component restriction transfers those recorded actions to
the current stage's tests.  Thus `AugmentedStep.link` has all its premises
discharged for this particular recursive family.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace AugmentedFamily

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- The actual augmented family has inclusion, deletion, and exact
replacement for every inclusion of edge subsets. -/
theorem family_links (N : Nat) (S : Finset E) :
    ∀ M : Finset E, M ⊆ S → Nonempty (Link D (family D N M) (family D N S)) := by
  refine Finset.strongInductionOn S ?_
  intro S ih M hMS
  by_cases heq : M = S
  · subst M
    exact ⟨Link.refl D S (family D N S)⟩
  · have hM : M ⊂ S := lt_of_le_of_ne hMS heq
    let old : ∀ i : Proper S, Data E i.val := fun i => family D N i.val
    let L : EarlierLinks D S old :=
      fun m t h => Classical.choice (ih t.val t.property m.val h)
    let A : ∀ n m : Proper S, n.val ⊂ m.val →
        RightAction (old m).Carrier (Step.components D S old n) :=
      fun n m h => Classical.choose (family_component_action D N n.val m.val h)
    have hA : ∀ (n m : Proper S) (h : n.val ⊂ m.val) e, e ∈ m.val → ∀ c,
        (A n m h).act c ((old m).edge e) =
          D.componentEdgePerm (Step.sets S n) (Step.edges S old n)
            (Step.involutions S old n) e c := by
      intro n m h
      exact Classical.choose_spec (family_component_action D N n.val m.val h)
    let smallActions : ∀ k : Proper S,
        ∀ d : LinkChain.SeparatedChains D N k.val (LinkChain.smallerOld S old k)
          (LinkChain.smallerLinks D S old L k),
        RightAction (old k).Carrier
          (LinkChain.chainSpace D N k.val (LinkChain.smallerOld S old k)
            (LinkChain.smallerLinks D S old L k) d) :=
      fun k d => recordedAction D N k.val (LinkChain.smallerLinks D S old L k) d
    have hsmall : ∀ k : Proper S,
        ∀ d : LinkChain.SeparatedChains D N k.val (LinkChain.smallerOld S old k)
          (LinkChain.smallerLinks D S old L k),
        ∀ e ∈ k.val, ∀ x, (smallActions k d).act x ((old k).edge e) =
          LinkChain.chainPerm D N k.val (LinkChain.smallerOld S old k)
            (LinkChain.smallerLinks D S old L k) d e x := by
      intro k d e he x
      exact recordedAction_edge D N k.val (LinkChain.smallerLinks D S old L k) d e he x
    let B : ∀ k : Proper S, ∀ c : LinkChain.SeparatedChains D N S old L,
        RightAction (old k).Carrier (LinkChain.chainSpace D N S old L c) :=
      fun k c => LinkChain.chainTestRightAction D N S old L k (smallActions k) (hsmall k) c
    have hB : ∀ k c e, e ∈ k.val → ∀ x,
        (B k c).act x ((old k).edge e) = LinkChain.chainPerm D N S old L c e x := by
      intro k c e he x
      exact LinkChain.chainTestRightAction_edge D N S old L k
        (smallActions k) (hsmall k) c e he x
    have hlink : Nonempty (Link D (family D N M)
        (AugmentedStep.data D S old (LinkChain.chainSpace D N S old L)
          (LinkChain.chainPerm D N S old L) (LinkChain.chainPerm_square D N S old L))) :=
      ⟨AugmentedStep.link D S old L A hA (LinkChain.chainSpace D N S old L)
        (LinkChain.chainPerm D N S old L) (LinkChain.chainPerm_square D N S old L)
        B hB ⟨M, hM⟩⟩
    rw [← family_eq_augmented D N S L] at hlink
    exact hlink

noncomputable def familyLink (N : Nat) (M S : Finset E) (hMS : M ⊆ S) :
    Link D (family D N M) (family D N S) :=
  Classical.choice (family_links D N S M hMS)

/-- The proper-stage Link family used by the actual all-chain package. -/
noncomputable def earlierLinks (N : Nat) (S : Finset E) :
    EarlierLinks D S (fun i => family D N i.val) :=
  fun m t h => familyLink D N m.val t.val h

/-- Every actual recursive stage records all genuine bounded tests.
The fallback branch of the total package function is never used here. -/
theorem family_record_eq (N : Nat) (S : Finset E) :
    family D N S =
      AugmentedStep.data D S (fun i => family D N i.val)
        (LinkChain.chainSpace D N S (fun i => family D N i.val) (earlierLinks D N S))
        (LinkChain.chainPerm D N S (fun i => family D N i.val) (earlierLinks D N S))
        (LinkChain.chainPerm_square D N S (fun i => family D N i.val) (earlierLinks D N S)) :=
  family_eq_augmented D N S (earlierLinks D N S)

theorem actual_tests_eq (N : Nat) (S : Finset E) :
    tests D N S (fun i => family D N i.val) =
      LinkChain.testPackage D N S (fun i => family D N i.val) (earlierLinks D N S) :=
  tests_eq D N S (fun i => family D N i.val) (earlierLinks D N S)

/-- An actual family Link into the literal augmented stage for any
presentation of its unique earlier Links.  This is the stage-local
inclusion interface used by the chain traversal and cycle theorems. -/
noncomputable def stageLink (N : Nat) (S : Finset E)
    (L : EarlierLinks D S (fun i => family D N i.val)) (k : Proper S) :
    Link D (family D N k.val)
      (AugmentedStep.data D S (fun i => family D N i.val)
        (LinkChain.chainSpace D N S (fun i => family D N i.val) L)
        (LinkChain.chainPerm D N S (fun i => family D N i.val) L)
        (LinkChain.chainPerm_square D N S (fun i => family D N i.val) L)) := by
  rw [← family_eq_augmented D N S L]
  exact familyLink D N k.val S k.property.1

noncomputable def inclusion (N : Nat) (M S : Finset E) (hMS : M ⊆ S) :
    (family D N M).Carrier →* (family D N S).Carrier :=
  (familyLink D N M S hMS).incl

noncomputable def deletion (N : Nat) (M S : Finset E) (hMS : M ⊆ S) :
    (family D N S).Carrier →* (family D N M).Carrier :=
  (familyLink D N M S hMS).delete

theorem inclusion_edge (N : Nat) (M S : Finset E) (hMS : M ⊆ S) (e : E) (he : e ∈ M) :
    inclusion D N M S hMS ((family D N M).edge e) = (family D N S).edge e :=
  (familyLink D N M S hMS).incl_edge e he

theorem deletion_edge (N : Nat) (M S : Finset E) (hMS : M ⊆ S) (e : E) (he : e ∈ S) :
    deletion D N M S hMS ((family D N S).edge e) =
      if e ∈ M then (family D N M).edge e else 1 := by
  by_cases hm : e ∈ M
  · simpa only [deletion, ite_eq_left hm] using (familyLink D N M S hMS).delete_edge e he
  · simpa only [deletion, ite_eq_right hm] using (familyLink D N M S hMS).delete_edge e he

theorem retraction (N : Nat) (M S : Finset E) (hMS : M ⊆ S) :
    (deletion D N M S hMS).comp (inclusion D N M S hMS) = MonoidHom.id _ :=
  Link.left_inverse D (family D N M) (family D N S) hMS (familyLink D N M S hMS)

theorem inclusion_injective (N : Nat) (M S : Finset E) (hMS : M ⊆ S) :
    Function.Injective (inclusion D N M S hMS) :=
  Link.injective D (family D N M) (family D N S) hMS (familyLink D N M S hMS)

theorem replacement (N : Nat) (M S : Finset E) (hMS : M ⊆ S)
    (u v : V) (g : (family D N M).Carrier)
    (p : D.WalkValue (S : Set E) (family D N S).edge u v (inclusion D N M S hMS g)) :
    D.WalkValue (M : Set E) (family D N M).edge u v g :=
  (familyLink D N M S hMS).replace u v g p

theorem inclusion_comp (N : Nat) (K M S : Finset E) (hKM : K ⊆ M) (hMS : M ⊆ S) :
    (inclusion D N M S hMS).comp (inclusion D N K M hKM) =
      inclusion D N K S (fun _ he => hMS (hKM he)) := by
  apply (family D N K).hom_ext
  intro e he
  change inclusion D N M S hMS (inclusion D N K M hKM ((family D N K).edge e)) = _
  rw [inclusion_edge D N K M hKM e he, inclusion_edge D N M S hMS e (hKM he),
    inclusion_edge D N K S _ e he]

theorem deletion_comp (N : Nat) (K M S : Finset E) (hKM : K ⊆ M) (hMS : M ⊆ S) :
    (deletion D N K M hKM).comp (deletion D N M S hMS) =
      deletion D N K S (fun _ he => hMS (hKM he)) := by
  apply (family D N S).hom_ext
  intro e he
  change deletion D N K M hKM (deletion D N M S hMS ((family D N S).edge e)) = _
  rw [deletion_edge D N M S hMS e he, deletion_edge D N K S _ e he]
  by_cases hm : e ∈ M
  · rw [ite_eq_left hm, deletion_edge D N K M hKM e hm]
  · have hk : e ∉ K := fun h => hm (hKM h)
    rw [ite_eq_right hm, ite_eq_right hk, map_one]

end AugmentedFamily
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
