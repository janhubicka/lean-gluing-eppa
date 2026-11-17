import GluingEPPA.Steiner.ChainValuation.HistoricalBoundaryNamedBridge

/-!
# Pointwise original Cayley coordinates at a witnessed Link boundary

For the final normalized proper-M chain, mere equality of the
ranges of the two historical source charts is not sufficient:
it leaves their group coordinates undetermined and cannot be
used in the translated separation equations.

At each actual boundary we have a stronger assertion: after
the canonical dependent cast along equality of the *actual
source masks*, the historical boundary chart is pointwise
identical to its named original Cayley source chart.

We prove this at the literal new LinkChain attachment and
transport it through every later genuine separated step.
The only coordinate transports are proof-irrelevant casts of
equal original mask indices; no group isomorphism or ambient
K_S is introduced.
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

/-- Transport an element of one original source group along an
EQUALITY of its mask index. This is not a choice of group
isomorphism, and it reduces to the identity for a reflexive
index equality. -/
def sourceMaskCast
    {A B : Proper S} (h : A = B)
    (x : (old A).Carrier) : (old B).Carrier :=
  cast (congrArg (fun T : Proper S => (old T).Carrier) h) x

@[simp] theorem sourceMaskCast_rfl (A : Proper S)
    (x : (old A).Carrier) :
    sourceMaskCast S old (rfl : A = A) x = x := rfl

/-- Pointwise identification of an exact original Link boundary's
two Cayley maps with the corresponding original named charts.
Unlike the weaker range agreement, this retains both literal
group coordinates and their noncommutative translation order. -/
def HistoricalLinkBoundary.PointwiseNamed
    {M : Proper S} {R : BuildResult D S old L}
    (B : HistoricalLinkBoundary D S old L M R)
    (T U : NamedHistoricalBlock D S old L M R)
    (h : B.AgreesWithNamed D S old L T U) : Prop :=
  (∀ x : (old B.leftMask).Carrier,
    B.leftChart x = T.chart.embed
      (sourceMaskCast S old h.1 x)) ∧
  (∀ y : (old B.rightMask).Carrier,
    B.rightChart y = U.chart.embed
      (sourceMaskCast S old h.2.1 y))

/-- The actual fresh boundary agrees POINTWISE with its original
named Cayley blocks, not only on the ranges of their embeddings. -/
theorem historicalStep_boundary_named_pointwise
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (historicalLinkBoundary_step D S old L M R y hsep hcoset).PointwiseNamed
      D S old L
      (namedHistoricalTransport D S old L M R y hsep hcoset
        (namedHistoricalLast D S old L M R hcoset))
      (namedHistoricalLast D S old L M
        (step D S old L R y hsep)
        (step_lastMaskCoset D S old L M R y hsep hcoset))
      (historicalStep_boundary_named_agree
        D S old L M R y hsep hcoset) := by
  constructor
  · intro x
    rfl
  · intro y0
    rfl

/-- Every later actual LinkChain attachment composes both
historical and named charts with the same old pushout embedding.
Therefore pointwise equality of their original coordinates is
transported unchanged, including all dependent source-mask casts. -/
theorem HistoricalLinkBoundary.transport_pointwiseNamed
    {M : Proper S} {R : BuildResult D S old L}
    (B : HistoricalLinkBoundary D S old L M R)
    (T U : NamedHistoricalBlock D S old L M R)
    (h : B.AgreesWithNamed D S old L T U)
    (hpoint : B.PointwiseNamed D S old L T U h)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (B.transport D S old L y hsep hcoset).PointwiseNamed
      D S old L
      (namedHistoricalTransport D S old L M R y hsep hcoset T)
      (namedHistoricalTransport D S old L M R y hsep hcoset U)
      (B.transport_agreesWithNamed D S old L
        T U h y hsep hcoset) := by
  let A := block S old R.current.1
  let C := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hi := left_injective D S old L R.current.1 y.1
  let hj := right_injective D S old L R.current.1 y.1
  let emb := GluingEPPA.Steiner.ChainValuation.oldEmbed
    A C R.state R.current.2 i j hi hj
  constructor
  · intro x
    change emb (B.leftChart x) =
      emb (T.chart.embed (sourceMaskCast S old h.1 x))
    exact congrArg emb (hpoint.1 x)
  · intro y0
    change emb (B.rightChart y0) =
      emb (U.chart.embed (sourceMaskCast S old h.2.1 y0))
    exact congrArg emb (hpoint.2 y0)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
