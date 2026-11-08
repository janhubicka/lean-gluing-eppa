import GluingEPPA.Steiner.ChainValuation.FiniteBoundaryCertificates
import GluingEPPA.Steiner.ChainValuation.LinkChain

/-!
# Forgetting witnessed Link boundaries recovers the original finite builder

The witnessed-boundary recursor is a dependent decoration of the
manuscript's actual LinkChain.step, not a substitute realization.
This module compares it with LinkChain.pair/next/buildTail and the
unmodified LinkChain.buildNonempty.
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

/-- Extract the exact original two-block state from a witnessed history
whose last two atoms are p and c. No new quotient is constructed. -/
noncomputable def BoundaryHistoryBuildResult.asPair
    (M : Proper S) (H : BoundaryHistoryBuildResult D S old L M)
    (p c : Atom S old)
    (hp : H.chain.previous = some p)
    (hc : H.chain.current = c) :
    PairResult D S old L p c := by
  subst c
  refine ⟨H.chain.state, ?_⟩
  simpa only [hp] using H.chain.entry_spec

/-- The original two-block transition is exactly the transition
computed by the boundary-enriched builder after forgetting witnesses. -/
theorem boundaryHistoryStep_asPair
    (M : Proper S) (H : BoundaryHistoryBuildResult D S old L M)
    (p c z : Atom S old)
    (hp : H.chain.previous = some p)
    (hc : H.chain.current = c)
    (htriple : tripleSeparated D S old L p c z)
    (hstep :
      match H.chain.previous with
      | none => True
      | some previous => tripleSeparated D S old L previous H.chain.current z)
    (hnprev :
      (boundaryHistoryStep D S old L M H z hstep).chain.previous = some c)
    (hncurr :
      (boundaryHistoryStep D S old L M H z hstep).chain.current = z) :
    (boundaryHistoryStep D S old L M H z hstep).asPair
       D S old L M c z hnprev hncurr =
      next D S old L (H.asPair D S old L M p c hp hc) z htriple := by
  subst c
  cases hp
  rfl

/-- Forgetting every remembered boundary and mask-coset invariant
during a true tail construction yields the *original* buildTail state. -/
theorem boundaryHistoryBuildTail_asOriginal
    (M : Proper S) (p c : Atom S old)
    (H : BoundaryHistoryBuildResult D S old L M)
    (hp : H.chain.previous = some p)
    (hc : H.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (⟨(boundaryHistoryBuildTail D S old L M p c H hp hc rest hsep).chain.current,
       (boundaryHistoryBuildTail D S old L M p c H hp hc rest hsep).chain.state⟩ :
       SomeState S old) =
      buildTail D S old L p c
        (H.asPair D S old L M p c hp hc) rest hsep := by
  induction rest generalizing p c H with
  | nil =>
      subst c
      rfl
  | cons z zs ih =>
      have hs :
          (match H.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous H.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := boundaryHistoryStep D S old L M H z hs
      have hnp : HN.chain.previous = some c := by
        change some H.chain.current = some c
        rw [hc]
      have hnc : HN.chain.current = z := rfl
      have htransition :
          HN.asPair D S old L M c z hnp hnc =
            next D S old L
              (H.asPair D S old L M p c hp hc) z hsep.1 :=
        boundaryHistoryStep_asPair D S old L M H p c z
          hp hc hsep.1 hs hnp hnc
      change
        (⟨(boundaryHistoryBuildTail D S old L M c z HN
            hnp hnc zs hsep.2).chain.current,
           (boundaryHistoryBuildTail D S old L M c z HN
            hnp hnc zs hsep.2).chain.state⟩ : SomeState S old) =
          buildTail D S old L c z
            (next D S old L
              (H.asPair D S old L M p c hp hc) z hsep.1)
            zs hsep.2
      rw [← htransition]
      exact ih c z HN hnp hnc hsep.2

/-- The witnessed historical-boundary construction has exactly the
same current atom and quotient state as the manuscript's
LinkChain.buildNonempty, not merely an isomorphic state. -/
theorem boundaryHistoryBuildNonempty_original
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (⟨(boundaryHistoryBuildNonempty D S old L M
        atoms hne hsep).chain.current,
       (boundaryHistoryBuildNonempty D S old L M
        atoms hne hsep).chain.state⟩ : SomeState S old) =
      buildNonempty D S old L atoms hne hsep := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          rfl
      | cons y ys =>
          let H0 := boundaryHistoryInitial D S old L M x
          let H1 := boundaryHistoryStep D S old L M H0 y trivial
          have hp : H1.chain.previous = some x := rfl
          have hc : H1.chain.current = y := rfl
          have hpair :
              H1.asPair D S old L M x y hp hc =
                pair D S old L x y := rfl
          change
            (⟨(boundaryHistoryBuildTail D S old L M
                x y H1 hp hc ys hsep).chain.current,
               (boundaryHistoryBuildTail D S old L M
                x y H1 hp hc ys hsep).chain.state⟩ : SomeState S old) =
              buildTail D S old L x y (pair D S old L x y) ys hsep
          rw [← hpair]
          exact boundaryHistoryBuildTail_asOriginal
            D S old L M x y H1 hp hc ys hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
