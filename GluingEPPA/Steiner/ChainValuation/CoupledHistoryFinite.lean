import GluingEPPA.Steiner.ChainValuation.CoupledNamedBoundaryStep

/-!
# One genuine finite Link chain with both certified histories

The source-named restricted-coset block history and the witnessed
exact-boundary history are advanced together by the *same*
LinkChain.step, retaining literal equality of their BuildResult
states. This file iterates that construction on any finite
nonempty separated list of original Link atoms.

The resulting common quotient has complete historical Cayley
coverage and an ordered list of genuine earlier interfaces.
The next task is to construct the full normalized M-component
equivalence, including edge/fixed-point reflection.
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

/-- Iteration along the literal remaining list, using the original
separation hypothesis for every new middle triple. -/
noncomputable def coupledHistoryBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : CoupledNamedBoundaryHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    CoupledNamedBoundaryHistory D S old L M := by
  induction rest generalizing p c H with
  | nil =>
      exact H
  | cons z zs ih =>
      have hstep :
          (match H.named.data.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coupledHistoryStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- The complete witnessed finite chain, with each original Cayley
block named and every true interface retained, both referring to
the same original quotient state. -/
noncomputable def coupledHistoryBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    CoupledNamedBoundaryHistory D S old L M := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact coupledHistoryInitial D S old L M x
      | cons y ys =>
          let H0 := coupledHistoryInitial D S old L M x
          let H1 := coupledHistoryStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          exact coupledHistoryBuildTail D S old L M x y H1 hp hc ys hsep

/-- No point-set isomorphism is needed to compare the two independent
certifications: the entire finite construction stores a proof that
their dependent original LinkChain states agree *literally*. -/
theorem coupledHistoryBuildNonempty_sameChain
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coupledHistoryBuildNonempty D S old L M atoms hne hsep).
        named.data.chain =
      (coupledHistoryBuildNonempty D S old L M atoms hne hsep).
        boundary.chain :=
  (coupledHistoryBuildNonempty D S old L M atoms hne hsep).sameChain

/-- The *same* final state is covered by named genuine historical
Cayley blocks; the two histories cannot silently switch quotients. -/
theorem coupledHistoryBuildNonempty_namedCover
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coupledHistoryBuildNonempty D S old L M atoms hne hsep
    GluingEPPA.Steiner.ChainValuation.HistoricalBlocksCover
      (block S old H.named.data.chain.current.1)
      H.named.data.chain.state M.val
      (H.named.named.map (fun T => T.toHistorical D S old L)) := by
  intro H
  exact H.named.covers D S old L M

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
