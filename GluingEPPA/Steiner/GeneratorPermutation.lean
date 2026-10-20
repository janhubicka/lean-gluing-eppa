import GluingEPPA.Steiner.WordLift

/-!
# Permuting named involutive generators

If a permutation of the edge names preserves exactly the identity words,
it extends to a group automorphism. This allows the symmetry of the
recursive finite construction to be formulated as invariance of its
relations, rather than as a choice of group-element representatives.
-/

namespace GluingEPPA.Steiner

universe u v
variable {E : Type u} {G : Type v} [Group G]

variable (a : E → G)
variable (ha : ∀ e, a e * a e = 1)
variable (hgen : ∀ g, ∃ w : List E, wordValue a w = g)

theorem perm_word (π : E ≃ E) (w : List E) :
    wordValue (fun e => a (π e)) w = wordValue a (w.map π) := by
  simp only [wordValue, List.map_map, Function.comp_def]

/-- The inverse name permutation also preserves identity relations. -/
theorem perm_relations_inverse (π : E ≃ E)
    (hrel : ∀ w : List E,
      wordValue a w = 1 ↔ wordValue a (w.map π) = 1)
    (w : List E) (hw : wordValue a w = 1) :
    wordValue a (w.map π.symm) = 1 := by
  have h := (hrel (w.map π.symm)).mpr
  have hp : wordValue a ((w.map π.symm).map π) = 1 := by
    simpa only [List.map_map, Equiv.apply_symm_apply, List.map_id] using hw
  exact h hp

noncomputable def permHom (π : E ≃ E)
    (hrel : ∀ w : List E,
      wordValue a w = 1 ↔ wordValue a (w.map π) = 1) : G →* G :=
  involutiveWordLift a (fun e => a (π e)) ha hgen (by
    intro w hw
    rw [perm_word]
    exact (hrel w).mp hw)

theorem permHom_generator (π : E ≃ E)
    (hrel : ∀ w : List E,
      wordValue a w = 1 ↔ wordValue a (w.map π) = 1)
    (e : E) :
    permHom a ha hgen π hrel (a e) = a (π e) :=
  involutiveWordLift_generator a (fun e => a (π e)) ha hgen
    (by intro w hw; rw [perm_word]; exact (hrel w).mp hw) e

/-- Every relation-preserving edge permutation has an inverse induced
by its inverse permutation, so the resulting map is an automorphism. -/
noncomputable def permEquiv (π : E ≃ E)
    (hrel : ∀ w : List E,
      wordValue a w = 1 ↔ wordValue a (w.map π) = 1) : G ≃* G := by
  let forward := permHom a ha hgen π hrel
  have hInv : ∀ w : List E, wordValue a w = 1 ↔
      wordValue a (w.map π.symm) = 1 := by
    intro w
    constructor
    · exact perm_relations_inverse a π hrel w
    · intro hw
      have h := (hrel (w.map π.symm)).mp hw
      simpa only [List.map_map, Equiv.symm_apply_apply, List.map_id] using h
  let backward := permHom a ha hgen π.symm hInv
  have hback : backward.comp forward = MonoidHom.id G := by
    apply hom_ext_of_words a hgen
    intro e
    change backward (forward (a e)) = a e
    rw [permHom_generator a ha hgen π hrel e,
      permHom_generator a ha hgen π.symm hInv (π e)]
    exact π.symm_apply_apply e ▸ rfl
  have hforward : forward.comp backward = MonoidHom.id G := by
    apply hom_ext_of_words a hgen
    intro e
    change forward (backward (a e)) = a e
    rw [permHom_generator a ha hgen π.symm hInv e,
      permHom_generator a ha hgen π hrel (π.symm e)]
    exact π.apply_symm_apply e ▸ rfl
  exact
    { toFun := forward
      invFun := backward
      left_inv := fun g => DFunLike.congr_fun hback g
      right_inv := fun g => DFunLike.congr_fun hforward g
      map_mul' := forward.map_mul }

theorem permEquiv_generator (π : E ≃ E)
    (hrel : ∀ w : List E,
      wordValue a w = 1 ↔ wordValue a (w.map π) = 1)
    (e : E) :
    permEquiv a ha hgen π hrel (a e) = a (π e) :=
  permHom_generator a ha hgen π hrel e

end GluingEPPA.Steiner
