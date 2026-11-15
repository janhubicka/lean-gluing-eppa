import GluingEPPA.Steiner.ChainValuation.HistoricalConsecutiveBoundaryCharts
import GluingEPPA.Steiner.ChainValuation.NamedHistoricalForgetful

/-!
# Connect genuine historical boundary charts to named block charts

The coupled finite history retains two independent pieces of actual
data: all source-named historical Cayley charts, and the witnessed
exact interfaces between consecutive Cayley blocks. Equality of
their source-mask lists alone does NOT identify the embedding of the
same historical block in the original quotient.

Here the actual fresh boundary is matched to the transported old
last-block chart and the new last-block chart. The two sides have
the correct original masks and their embedded point images agree
*exactly*. Subsequent original separated attachments transport
that agreement because all three charts compose with the same
injective old-chain embedding.

This is a local geometric bridge required before selecting the
normalized M-coset parameters coherently over a whole interval.
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

/-- Agreement between a real recorded historical interface and the
source-named Cayley charts on its two sides. All three maps live in
the same literal final quotient, and the *complete ranges* coincide,
not just the selected M-component's point sets. -/
def HistoricalLinkBoundary.AgreesWithNamed
    {M : Proper S} {R : BuildResult D S old L}
    (B : HistoricalLinkBoundary D S old L M R)
    (T U : NamedHistoricalBlock D S old L M R) : Prop :=
  B.leftMask = T.source ∧
  B.rightMask = U.source ∧
  Set.range B.leftChart = Set.range T.chart.embed ∧
  Set.range B.rightChart = Set.range U.chart.embed

/-- Composing two source charts with the SAME map preserves equality
of their complete images, regardless of the source carrier types. -/
private theorem range_comp_of_range_eq
    {X Y A B : Type u}
    (f : A → X) (g : B → X) (h : Set.range f = Set.range g)
    (k : X → Y) :
    Set.range (fun a => k (f a)) =
      Set.range (fun b => k (g b)) := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    have ha : f a ∈ Set.range g := by
      rw [← h]
      exact ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, by rw [← hb]⟩
  · rintro ⟨b, rfl⟩
    have hb : g b ∈ Set.range f := by
      rw [h]
      exact ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, by rw [← ha]⟩

/-- For the literal new Link attachment, the boundary's left
Cayley chart is the transported *previous last named chart*, and
its right chart is the *new last named chart*. The agreement of
whole source-block images follows definitionally from the same
original ChainState.extend construction. -/
theorem historicalStep_boundary_named_agree
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (historicalLinkBoundary_step D S old L M R y hsep hcoset).AgreesWithNamed
      D S old L
      (namedHistoricalTransport D S old L M R y hsep hcoset
        (namedHistoricalLast D S old L M R hcoset))
      (namedHistoricalLast D S old L M
        (step D S old L R y hsep)
        (step_lastMaskCoset D S old L M R y hsep hcoset)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Agreement between original historical boundary charts and
named block charts is invariant under *every* later genuine
separated LinkChain attachment. This does not assume that the
two source masks or groups are equal. -/
theorem HistoricalLinkBoundary.transport_agreesWithNamed
    {M : Proper S} {R : BuildResult D S old L}
    (B : HistoricalLinkBoundary D S old L M R)
    (T U : NamedHistoricalBlock D S old L M R)
    (hAgree : B.AgreesWithNamed D S old L T U)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (B.transport D S old L y hsep hcoset).AgreesWithNamed
      D S old L
      (namedHistoricalTransport D S old L M R y hsep hcoset T)
      (namedHistoricalTransport D S old L M R y hsep hcoset U) := by
  rcases hAgree with ⟨hLeft, hRight, hRangeL, hRangeR⟩
  let A := block S old R.current.1
  let C := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hi := left_injective D S old L R.current.1 y.1
  let hj := right_injective D S old L R.current.1 y.1
  let emb := GluingEPPA.Steiner.ChainValuation.oldEmbed
    A C R.state R.current.2 i j hi hj
  refine ⟨hLeft, hRight, ?_, ?_⟩
  · change Set.range (fun x => emb (B.leftChart x)) =
      Set.range (fun x => emb (T.chart.embed x))
    exact range_comp_of_range_eq B.leftChart T.chart.embed hRangeL emb
  · change Set.range (fun x => emb (B.rightChart x)) =
      Set.range (fun x => emb (U.chart.embed x))
    exact range_comp_of_range_eq B.rightChart U.chart.embed hRangeR emb

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
