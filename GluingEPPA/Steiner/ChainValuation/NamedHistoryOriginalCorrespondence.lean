import GluingEPPA.Steiner.ChainValuation.CoupledHistoryOriginalCorrespondence
import GluingEPPA.Steiner.ChainValuation.NamedHistoryLetterEdgesFinite

/-!
# The standalone source-named history is exactly the original LinkChain

The coupled finite history is known to give the original
LinkChain.buildNonempty state, but the standalone named-history
recursor has its own dependent package. We identify that entire
named package with the named half of the checked coupled builder.

Consequently ALL genuine historical source-letter edge certificates
proved by NamedHistoryLetterEdgesFinite refer to the literal
original finite-chain quotient, not a similar auxiliary quotient.
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

/-- The named half of the coupled tail builder is literally the
standalone named tail, with no source-block reindexing. -/
theorem coupledHistoryBuildTail_named_eq
    (M : Proper S) (p c : Atom S old)
    (H : CoupledNamedBoundaryHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (coupledHistoryBuildTail D S old L M p c H hp hc rest hsep).named =
      namedHistoryBuildTail D S old L M p c H.named hp hc rest hsep := by
  induction rest generalizing p c H with
  | nil =>
      rfl
  | cons z zs ih =>
      have hstep :
          (match H.named.data.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous
                 H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coupledHistoryStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      change
        (coupledHistoryBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).named =
        namedHistoryBuildTail D S old L M c z
          HN.named hnp hnc zs hsep.2
      exact ih c z HN hnp hnc hsep.2

/-- Both source-named constructions produce the IDENTICAL dependent
record, including its original Cayley charts and source masks. -/
theorem coupledHistoryBuildNonempty_named_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coupledHistoryBuildNonempty D S old L M atoms hne hsep).named =
      namedHistoryBuildNonempty D S old L M atoms hne hsep := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          rfl
      | cons y ys =>
          let H0 := coupledHistoryInitial D S old L M x
          let H1 := coupledHistoryStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          change
            (coupledHistoryBuildTail D S old L M x y H1
              hp hc ys hsep).named =
            namedHistoryBuildTail D S old L M x y
              H1.named hp hc ys hsep
          exact coupledHistoryBuildTail_named_eq
            D S old L M x y H1 hp hc ys hsep

/-- The standalone historical source-named builder gives EXACTLY
the original LinkChain.buildNonempty dependent SomeState, not
merely an isomorphic chain. Hence all named historical source-edge
certificates hold in the actual manuscript construction. -/
theorem namedHistoryBuildNonempty_original
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (⟨(namedHistoryBuildNonempty D S old L M
        atoms hne hsep).data.chain.current,
       (namedHistoryBuildNonempty D S old L M
        atoms hne hsep).data.chain.state⟩ : SomeState S old) =
      buildNonempty D S old L atoms hne hsep := by
  let H := coupledHistoryBuildNonempty D S old L M atoms hne hsep
  have hnamed : H.named = namedHistoryBuildNonempty
      D S old L M atoms hne hsep :=
    coupledHistoryBuildNonempty_named_eq
      D S old L M atoms hne hsep
  have heq :
      (⟨(namedHistoryBuildNonempty D S old L M
          atoms hne hsep).data.chain.current,
         (namedHistoryBuildNonempty D S old L M
          atoms hne hsep).data.chain.state⟩ : SomeState S old) =
      (⟨H.named.data.chain.current,
         H.named.data.chain.state⟩ : SomeState S old) :=
    (congrArg
      (fun N : NamedHistoryBuildResult D S old L M =>
        (⟨N.data.chain.current, N.data.chain.state⟩ : SomeState S old))
      hnamed).symm
  exact heq.trans
    (coupledHistoryBuildNonempty_named_original
      D S old L M atoms hne hsep)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
