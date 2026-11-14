import GluingEPPA.Steiner.ChainValuation.CoupledHistoryFinite
import GluingEPPA.Steiner.ChainValuation.BoundaryHistoryOriginalCorrespondence

/-!
# The coupled finite histories are the original LinkChain realization

The source-named history and the exact witnessed-boundary history are
advanced together through the literal LinkChain.step. The finite-list
builder is not a substitute quotient. This module compares its complete
boundary-history record with the earlier checked finite-boundary builder
and therefore with LinkChain.buildNonempty itself.

The conclusion is equality of the original dependent SomeState,
including its point carrier, last atom and actual partial matchings;
no arbitrary equivalence of points is inserted.

It remains to assemble the normalized proper-M component charts
along the now compatible named and witnessed histories, including
reflection of completed letter actions.
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

/-- Iterating the synchronized construction forgets to exactly the
old witnessed-boundary tail, with all of its genuine interface
certificates and their order unchanged. -/
theorem coupledHistoryBuildTail_boundary_eq
    (M : Proper S) (p c : Atom S old)
    (H : CoupledNamedBoundaryHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (hbp : H.boundary.chain.previous = some p)
    (hbc : H.boundary.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (coupledHistoryBuildTail D S old L M p c H hp hc rest hsep).boundary =
      boundaryHistoryBuildTail D S old L M p c H.boundary hbp hbc
        rest hsep := by
  induction rest generalizing p c H with
  | nil =>
      rfl
  | cons z zs ih =>
      have hs :
          (match H.named.data.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coupledHistoryStep D S old L M H z hs
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      have hnbp : HN.boundary.chain.previous = some c := by
        change some H.boundary.chain.current = some c
        rw [hbc]
      have hnbc : HN.boundary.chain.current = z := rfl
      change
        (coupledHistoryBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).boundary =
          boundaryHistoryBuildTail D S old L M c z HN.boundary
            hnbp hnbc zs hsep.2
      exact ih c z HN hnp hnc hnbp hnbc hsep.2

/-- The whole boundary half of the coupled finite history is equal
to the previously certified original boundary-history builder,
rather than merely carrying isomorphic or similarly indexed data. -/
theorem coupledHistoryBuildNonempty_boundary_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coupledHistoryBuildNonempty D S old L M atoms hne hsep).boundary =
      boundaryHistoryBuildNonempty D S old L M atoms hne hsep := by
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
          have hbp : H1.boundary.chain.previous = some x := rfl
          have hbc : H1.boundary.chain.current = y := rfl
          change
            (coupledHistoryBuildTail D S old L M x y H1
              hp hc ys hsep).boundary =
              boundaryHistoryBuildTail D S old L M x y H1.boundary
                hbp hbc ys hsep
          exact coupledHistoryBuildTail_boundary_eq
            D S old L M x y H1 hp hc hbp hbc ys hsep

/-- The final boundary state of the coupled history is literally
the original LinkChain.buildNonempty dependent SomeState. -/
theorem coupledHistoryBuildNonempty_original
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (⟨(coupledHistoryBuildNonempty D S old L M
        atoms hne hsep).boundary.chain.current,
       (coupledHistoryBuildNonempty D S old L M
        atoms hne hsep).boundary.chain.state⟩ : SomeState S old) =
      buildNonempty D S old L atoms hne hsep := by
  let H := coupledHistoryBuildNonempty D S old L M atoms hne hsep
  have hrecords : H.boundary =
      boundaryHistoryBuildNonempty D S old L M atoms hne hsep :=
    coupledHistoryBuildNonempty_boundary_eq
      D S old L M atoms hne hsep
  have hpoints :
      (⟨H.boundary.chain.current, H.boundary.chain.state⟩ : SomeState S old) =
      (⟨(boundaryHistoryBuildNonempty D S old L M
          atoms hne hsep).chain.current,
         (boundaryHistoryBuildNonempty D S old L M
          atoms hne hsep).chain.state⟩ : SomeState S old) :=
    congrArg
      (fun B : BoundaryHistoryBuildResult D S old L M =>
        (⟨B.chain.current, B.chain.state⟩ : SomeState S old))
      hrecords
  exact hpoints.trans
    (boundaryHistoryBuildNonempty_original D S old L M atoms hne hsep)

/-- The source-named historical chart side also describes the
*same* original quotient, by the literal coupled-state equality.
No additional comparison of point realizations is needed. -/
theorem coupledHistoryBuildNonempty_named_original
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (⟨(coupledHistoryBuildNonempty D S old L M
        atoms hne hsep).named.data.chain.current,
       (coupledHistoryBuildNonempty D S old L M
        atoms hne hsep).named.data.chain.state⟩ : SomeState S old) =
      buildNonempty D S old L atoms hne hsep := by
  let H := coupledHistoryBuildNonempty D S old L M atoms hne hsep
  have heq : H.named.data.chain = H.boundary.chain := H.sameChain
  have hp :
      (⟨H.named.data.chain.current, H.named.data.chain.state⟩ : SomeState S old) =
      (⟨H.boundary.chain.current, H.boundary.chain.state⟩ : SomeState S old) :=
    congrArg
      (fun R : BuildResult D S old L =>
        (⟨R.current, R.state⟩ : SomeState S old)) heq
  exact hp.trans
    (coupledHistoryBuildNonempty_original D S old L M atoms hne hsep)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
