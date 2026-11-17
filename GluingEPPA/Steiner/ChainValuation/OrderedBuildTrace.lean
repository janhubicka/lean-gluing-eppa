import GluingEPPA.Steiner.ChainValuation.LinkChain

/-!
# Ordered initial/step traces agree with the literal finite builder

A source certificate built by appending actual `LinkChain.step` operations
must determine the same state as `buildNonempty` on its recorded atom list.
This file proves that correspondence, including the separated-list proof.
The temporary full result retains the previous atom that `SomeState`
forgets; no quotient or graph is replaced by an unrelated construction.
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

inductive OrderedBuildTrace : List (Atom S old) → BuildResult D S old L → Prop
  | single (x : Atom S old) : OrderedBuildTrace [x] (initial D S old L x)
  | attach {xs : List (Atom S old)} {R : BuildResult D S old L}
      (previous : OrderedBuildTrace xs R) (y : Atom S old)
      (hsep : match R.previous with
        | none => True
        | some p => tripleSeparated D S old L p R.current y) :
      OrderedBuildTrace (xs ++ [y]) (step D S old L R y hsep)

namespace OrderedBuildTrace

theorem last_prefix {xs : List (Atom S old)} {R : BuildResult D S old L}
    (T : OrderedBuildTrace D S old L xs R) :
    ∃ pre, xs = pre ++ [R.current] := by
  cases T with
  | single x => exact ⟨[], rfl⟩
  | attach previous y hsep => exact ⟨_, rfl⟩

theorem nonempty {xs : List (Atom S old)} {R : BuildResult D S old L}
    (T : OrderedBuildTrace D S old L xs R) : xs ≠ [] := by
  obtain ⟨pre, hpre⟩ := T.last_prefix D S old L
  rw [hpre]
  simp

theorem end_spec {xs : List (Atom S old)} {R : BuildResult D S old L}
    (T : OrderedBuildTrace D S old L xs R) :
    (xs = [R.current] ∧ R.previous = none) ∨
    (∃ pre p, xs = pre ++ [p, R.current] ∧ R.previous = some p) := by
  cases T with
  | single x => exact Or.inl ⟨rfl, rfl⟩
  | @attach xs R previous y hsep =>
      obtain ⟨pre, hpre⟩ := previous.last_prefix D S old L
      right
      refine ⟨pre, R.current, ?_, rfl⟩
      change xs ++ [y] = pre ++ [R.current, y]
      simp only [hpre, List.append_assoc, List.cons_append, List.nil_append]

end OrderedBuildTrace

private theorem separatedList_append_last
    (pre : List (Atom S old)) (p c y : Atom S old)
    (hpre : separatedList D S old L (pre ++ [p, c]))
    (hnew : tripleSeparated D S old L p c y) :
    separatedList D S old L (pre ++ [p, c, y]) := by
  induction pre with
  | nil => exact ⟨hnew, trivial⟩
  | cons a pre ih =>
      cases pre with
      | nil => exact ⟨hpre.1, hnew, trivial⟩
      | cons b pre =>
          cases pre with
          | nil => exact ⟨hpre.1, ih hpre.2⟩
          | cons z pre => exact ⟨hpre.1, ih hpre.2⟩

theorem OrderedBuildTrace.separated
    {xs : List (Atom S old)} {R : BuildResult D S old L}
    (T : OrderedBuildTrace D S old L xs R) : separatedList D S old L xs := by
  induction T with
  | single x => trivial
  | @attach xs R previous y hsep ih =>
      rcases previous.end_spec D S old L with ⟨hxs, hp⟩ | ⟨pre, p, hxs, hp⟩
      · rw [hxs]
        trivial
      · have hnew : tripleSeparated D S old L p R.current y := by
          simpa only [hp] using hsep
        rw [hxs] at ih ⊢
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          separatedList_append_last D S old L pre p R.current y ih hnew

/-- The original tail recursion retaining its previous atom. -/
noncomputable def orderedResultTail (p c : Atom S old)
    (R : PairResult D S old L p c) (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) : BuildResult D S old L := by
  induction rest generalizing p c with
  | nil => exact ⟨some p, c, R.state, R.entry_spec⟩
  | cons z rest ih => exact ih c z (next D S old L R z hsep.1) hsep.2

theorem orderedResultTail_state (p c : Atom S old)
    (R : PairResult D S old L p c) (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (⟨(orderedResultTail D S old L p c R rest hsep).current,
      (orderedResultTail D S old L p c R rest hsep).state⟩ : SomeState S old) =
      buildTail D S old L p c R rest hsep := by
  induction rest generalizing p c with
  | nil => rfl
  | cons z rest ih => exact ih c z (next D S old L R z hsep.1) hsep.2

theorem orderedResultTail_snoc (p c : Atom S old)
    (R : PairResult D S old L p c) (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) (y : Atom S old)
    (hsepAll : separatedList D S old L (p :: c :: (rest ++ [y])))
    (hstep : match (orderedResultTail D S old L p c R rest hsep).previous with
      | none => True
      | some a => tripleSeparated D S old L a
          (orderedResultTail D S old L p c R rest hsep).current y) :
    orderedResultTail D S old L p c R (rest ++ [y]) hsepAll =
      step D S old L (orderedResultTail D S old L p c R rest hsep) y hstep := by
  induction rest generalizing p c with
  | nil => rfl
  | cons z rest ih => exact ih c z (next D S old L R z hsep.1) hsep.2 hsepAll.2 hstep

noncomputable def orderedResultNonempty (xs : List (Atom S old)) (hne : xs ≠ [])
    (hsep : separatedList D S old L xs) : BuildResult D S old L := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x rest =>
      cases rest with
      | nil => exact initial D S old L x
      | cons y rest => exact orderedResultTail D S old L x y (pair D S old L x y) rest hsep

theorem orderedResultNonempty_state (xs : List (Atom S old)) (hne : xs ≠ [])
    (hsep : separatedList D S old L xs) :
    (⟨(orderedResultNonempty D S old L xs hne hsep).current,
      (orderedResultNonempty D S old L xs hne hsep).state⟩ : SomeState S old) =
      buildNonempty D S old L xs hne hsep := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x rest =>
      cases rest with
      | nil => rfl
      | cons y rest => exact orderedResultTail_state D S old L x y (pair D S old L x y) rest hsep

theorem orderedResultNonempty_snoc (xs : List (Atom S old)) (hne : xs ≠ [])
    (hsep : separatedList D S old L xs) (y : Atom S old)
    (hneAll : xs ++ [y] ≠ []) (hsepAll : separatedList D S old L (xs ++ [y]))
    (hstep : match (orderedResultNonempty D S old L xs hne hsep).previous with
      | none => True
      | some a => tripleSeparated D S old L a
          (orderedResultNonempty D S old L xs hne hsep).current y) :
    orderedResultNonempty D S old L (xs ++ [y]) hneAll hsepAll =
      step D S old L (orderedResultNonempty D S old L xs hne hsep) y hstep := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x rest =>
      cases rest with
      | nil => rfl
      | cons z rest =>
          exact orderedResultTail_snoc D S old L x z
            (pair D S old L x z) rest hsep y hsepAll hstep

private theorem step_congr_result
    (R T : BuildResult D S old L) (hRT : R = T) (y : Atom S old)
    (hR : match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hT : match T.previous with
      | none => True
      | some p => tripleSeparated D S old L p T.current y) :
    step D S old L R y hR = step D S old L T y hT := by
  subst T
  rfl

theorem OrderedBuildTrace.result_eq
    {xs : List (Atom S old)} {R : BuildResult D S old L}
    (T : OrderedBuildTrace D S old L xs R) :
    R = orderedResultNonempty D S old L xs
      (T.nonempty D S old L) (T.separated D S old L) := by
  induction T with
  | single x => rfl
  | @attach xs R previous y hsep ih =>
      let R' := orderedResultNonempty D S old L xs
        (previous.nonempty D S old L) (previous.separated D S old L)
      have hstep : match R'.previous with
          | none => True
          | some p => tripleSeparated D S old L p R'.current y := by
        change (match (orderedResultNonempty D S old L xs
          (previous.nonempty D S old L) (previous.separated D S old L)).previous with
          | none => True
          | some p => tripleSeparated D S old L p
              (orderedResultNonempty D S old L xs
                (previous.nonempty D S old L) (previous.separated D S old L)).current y)
        rw [← ih]
        exact hsep
      exact (step_congr_result D S old L R R' ih y hsep hstep).trans
        (orderedResultNonempty_snoc D S old L xs
          (previous.nonempty D S old L) (previous.separated D S old L) y
          _ _ hstep).symm

/-- An ordered source trace gives the very same dependent current/state
pair as the literal finite builder, not just an isomorphic quotient. -/
theorem OrderedBuildTrace.state_eq
    {xs : List (Atom S old)} {R : BuildResult D S old L}
    (T : OrderedBuildTrace D S old L xs R) :
    (⟨R.current, R.state⟩ : SomeState S old) =
      buildNonempty D S old L xs (T.nonempty D S old L) (T.separated D S old L) := by
  have hR := T.result_eq D S old L
  have h := congrArg (fun R : BuildResult D S old L =>
    (⟨R.current, R.state⟩ : SomeState S old)) hR
  exact h.trans (orderedResultNonempty_state D S old L xs _ _)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
