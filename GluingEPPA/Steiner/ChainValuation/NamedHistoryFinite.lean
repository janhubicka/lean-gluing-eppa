import GluingEPPA.Steiner.ChainValuation.NamedHistoryStepBridge

/-!
# Actual finite separated Link history with source-mask provenance

This is the same one-, two- and many-block recursion as the
manuscript's LinkChain.buildNonempty, decorated with the original
earlier masks. At each step the checked generic chart history is
preserved by the forgetful certificate.

The result's source mask list is *exactly* the source masks of the
input atoms, in their original order. The next task is to compare
the resulting chain state to the literal original buildNonempty and
align the named blocks with the exact historical boundary records.

No normalized M-component equivalence is asserted here.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

/-- Attach every remaining atom of an actual separated chain to a
named history. Its generic quotient and chart list are retained by
NamedHistoryBuildResult, and no source mask is forgotten. -/
noncomputable def namedHistoryBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : NamedHistoryBuildResult D S old L M)
    (hp : H.data.chain.previous = some p)
    (hc : H.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    NamedHistoryBuildResult D S old L M := by
  induction rest generalizing p c H with
  | nil =>
      exact H
  | cons z zs ih =>
      have hstep :
          (match H.data.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous H.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := namedHistoryStep D S old L M H z hstep
      have hnp : HN.data.chain.previous = some c := by
        change some H.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- Forgetting the input names of the tail yields exactly the
original prefix masks followed by the masks of every new atom. -/
theorem namedHistoryBuildTail_sources
    (M : Proper S) (p c : Atom S old)
    (H : NamedHistoryBuildResult D S old L M)
    (hp : H.data.chain.previous = some p)
    (hc : H.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (namedHistoryBuildTail D S old L M p c H hp hc rest hsep).sourceMasks =
      H.sourceMasks ++ rest.map (fun T => T.1) := by
  induction rest generalizing p c H with
  | nil =>
      simp only [namedHistoryBuildTail, List.map_nil, List.append_nil]
  | cons z zs ih =>
      have hstep :
          (match H.data.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous H.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := namedHistoryStep D S old L M H z hstep
      have hnp : HN.data.chain.previous = some c := by
        change some H.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.chain.current = z := rfl
      change
        (namedHistoryBuildTail D S old L M c z HN hnp hnc zs hsep.2).sourceMasks =
          H.sourceMasks ++ (z :: zs).map (fun T => T.1)
      rw [ih c z HN hnp hnc hsep.2]
      have hHN : HN.sourceMasks = H.sourceMasks ++ [z.1] := rfl
      rw [hHN]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-- A genuinely finite nonempty separated Link list now has a
source-named generic historical chart family, with its original
component-coverage invariant. -/
noncomputable def namedHistoryBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    NamedHistoryBuildResult D S old L M := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact namedHistoryInitial D S old L M x
      | cons y ys =>
          let H0 := namedHistoryInitial D S old L M x
          let H1 := namedHistoryStep D S old L M H0 y trivial
          have hp : H1.data.chain.previous = some x := rfl
          have hc : H1.data.chain.current = y := rfl
          exact namedHistoryBuildTail D S old L M x y H1 hp hc ys hsep

/-- All source masks have the same order as the original finite input
atoms, including repeated original masks when their atoms differ. -/
theorem namedHistoryBuildNonempty_sources
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (namedHistoryBuildNonempty D S old L M atoms hne hsep).sourceMasks =
      atoms.map (fun T => T.1) := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          rfl
      | cons y ys =>
          let H0 := namedHistoryInitial D S old L M x
          let H1 := namedHistoryStep D S old L M H0 y trivial
          have hp : H1.data.chain.previous = some x := rfl
          have hc : H1.data.chain.current = y := rfl
          change
            (namedHistoryBuildTail D S old L M x y H1 hp hc ys hsep).sourceMasks =
              (x :: y :: ys).map (fun T => T.1)
          rw [namedHistoryBuildTail_sources
            D S old L M x y H1 hp hc ys hsep]
          have hfirst : H1.sourceMasks = [x.1, y.1] := rfl
          rw [hfirst]
          simp only [List.map_cons, List.cons_append, List.singleton_append,
            List.nil_append]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
