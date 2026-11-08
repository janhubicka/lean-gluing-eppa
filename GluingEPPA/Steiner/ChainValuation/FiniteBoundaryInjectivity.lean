import GluingEPPA.Steiner.ChainValuation.HistoricalBoundaryInjectivity

/-!
# Every boundary chart of a finite true Link history is injective

The previous theorem proves injectivity for the freshly attached
pair and preservation under any additional separated Link step.
This module carries that invariant through the literal
BoundaryHistoryBuildResult recursion.

Consequently, every historical interface chart constructed from
any nonempty separated finite list injects each of its original
Cayley blocks into the *actual* final quotient. It cannot silently
identify distinct vertices in the same source group, a requirement
for the later edge-reflecting normalization equivalence.
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

/-- Every stored historical boundary of this actual prefix chain
is embedded on both its genuine earlier Cayley source groups. -/
def BoundaryHistoryBuildResult.AllEmbedded
    (M : Proper S) (H : BoundaryHistoryBuildResult D S old L M) : Prop :=
  HistoricalBoundariesEmbedded D S old L M H.chain H.boundaries

/-- The original single-block history has no boundaries. -/
theorem boundaryHistoryInitial_allEmbedded
    (M : Proper S) (x : Atom S old) :
    (boundaryHistoryInitial D S old L M x).AllEmbedded D S old L := by
  intro T hT
  simp [BoundaryHistoryBuildResult.AllEmbedded,
    HistoricalBoundariesEmbedded, boundaryHistoryInitial] at hT

/-- One genuine separated Link step preserves injectivity of
every original boundary and appends a fresh injective pair. -/
theorem boundaryHistoryStep_allEmbedded
    (M : Proper S) (H : BoundaryHistoryBuildResult D S old L M)
    (y : Atom S old)
    (hsep :
      match H.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.chain.current y)
    (hEmb : H.AllEmbedded D S old L) :
    (boundaryHistoryStep D S old L M H y hsep).AllEmbedded
      D S old L := by
  exact historicalBoundaries_step_embedded
    D S old L M H.chain y hsep H.lastInv
    H.boundaries hEmb

/-- Recursive transport of injectivity over all later Link
attachments, with the actual previous/current mask witnesses
used by the manuscript's separated chain builder. -/
theorem boundaryHistoryBuildTail_allEmbedded
    (M : Proper S) (p c : Atom S old)
    (H : BoundaryHistoryBuildResult D S old L M)
    (hprev : H.chain.previous = some p)
    (hcurr : H.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest))
    (hEmb : H.AllEmbedded D S old L) :
    (boundaryHistoryBuildTail D S old L M p c H hprev hcurr
      rest hsep).AllEmbedded D S old L := by
  induction rest generalizing p c H with
  | nil =>
      exact hEmb
  | cons z zs ih =>
      have hstep :
          (match H.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous H.chain.current z) := by
        rw [hprev, hcurr]
        exact hsep.1
      let HN := boundaryHistoryStep D S old L M H z hstep
      have hnprev : HN.chain.previous = some c := by
        change some H.chain.current = some c
        rw [hcurr]
      have hncurr : HN.chain.current = z := rfl
      change
        (boundaryHistoryBuildTail D S old L M c z HN
          hnprev hncurr zs hsep.2).AllEmbedded D S old L
      exact ih c z HN hnprev hncurr hsep.2
        (boundaryHistoryStep_allEmbedded
          D S old L M H z hstep hEmb)

/-- The fully built original finite boundary history has
injective charts for *every* recorded consecutive interface. -/
theorem boundaryHistoryBuildNonempty_allEmbedded
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (boundaryHistoryBuildNonempty D S old L M atoms hne hsep).AllEmbedded
      D S old L := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact boundaryHistoryInitial_allEmbedded D S old L M x
      | cons y ys =>
          let H0 := boundaryHistoryInitial D S old L M x
          let H1 := boundaryHistoryStep D S old L M H0 y trivial
          have hp : H1.chain.previous = some x := rfl
          have hc : H1.chain.current = y := rfl
          change
            (boundaryHistoryBuildTail D S old L M x y H1 hp hc
              ys hsep).AllEmbedded D S old L
          exact boundaryHistoryBuildTail_allEmbedded D S old L M
            x y H1 hp hc ys hsep
            (boundaryHistoryStep_allEmbedded D S old L M
              H0 y trivial (boundaryHistoryInitial_allEmbedded
                D S old L M x))

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
