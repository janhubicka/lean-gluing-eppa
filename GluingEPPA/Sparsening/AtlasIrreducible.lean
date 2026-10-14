import GluingEPPA.Sparsening.IrreducibleBridge

/-!
# Actual irreducibles are captured by a lifted chart

Consumes the verified intrinsic quotient-record and separator lemmas.
The only irreducibility definition is the unary specialization of the
public AllThoseEPPA.Structure.IsIrreducible API, with no extra connectivity
assumption. This lemma covers disconnected, empty and cyclic unary fibres;
the carrier X itself must be nonempty for the common-chart conclusion.
-/
namespace GluingEPPA.Sparsening.ChartAtlas

universe u v w z t
variable {V : Type u} {E : Type v} {A : Type w}
variable {L : Nat → Type z} {F : Type t}
variable (G : GluingEPPA.EdgeGraph V E) (support : A → V → Prop)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (R : RelStructure L A) (out : F → A → Set A)
variable (closed : ∀ f x y s, support x s → y ∈ out f x → support y s)

/-- Each induced relation tuple and each whole unary fibre has constant
pointed boundary charge. Irreducibility therefore forces ONE charge value
throughout the test, without postulating chart connectivity. -/
theorem charge_constant_of_irreducible (X : Set (Vertex G support))
    (hirr : IsIrreducible
      (inducedAtlas G support R X)
      (inducedOutput G support out closed X)) :
    ∀ p q : X, atlasCharge G support p.val = atlasCharge G support q.val := by
  intro p q
  apply color_constant_of_irreducible
    (inducedAtlas G support R X) (inducedOutput G support out closed X)
    (fun q : X => atlasCharge G support q.val)
  · intro n r xs hx i j
    exact coChart_charge G support
      (relation_coChart G support R r (fun k => (xs k).val) hx i j)
  · intro f p q h
    exact coChart_charge G support
      (output_coChart G support out closed f p.val q.val h)
  · exact hirr

/-- In an irreducible closed test, the concrete chart-or-cut alternative
cannot take the cut branch. The result contains an actual single valuation
shared by ALL points, not a pointwise choice of charts. -/
theorem irreducible_lies_in_chart
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (X : Set (Vertex G support)) [Nonempty X]
    (hclosed : UnaryClosed (liftOutput G support out closed) (fun q => q ∈ X))
    (hirr : IsIrreducible
      (inducedAtlas G support R X)
      (inducedOutput G support out closed X)) :
    ∃ (s : V) (chi : E → ZMod 2), ∀ q : X,
      ∃ hx : support (project G support q.val) s,
        copy G support s chi (project G support q.val) hx = q.val := by
  rcases atlas_chart_or_closed_cut G support R out closed complete X
      (charge_constant_of_irreducible G support R out closed X hirr) with h | h
  · exact h
  · obtain ⟨e, ⟨cut⟩⟩ := h
    exact (no_closed_cut_of_irreducible
      (inducedAtlas G support R X)
      (inducedOutput G support out closed X) hirr cut).elim

/-- The exact analogue of
AllThoseEPPA.Structure.Homomorphism.IsEmbeddingOn, for the canonical
projection from our unary chart quotient to the old structure.
It checks injection, relational reflection (not just preservation), and
EQUALITY of entire unary output images. -/
def ProjectionIsEmbeddingOn (X : Set (Vertex G support)) : Prop :=
  Set.InjOn (project G support) X ∧
  (∀ {n} (r : L n) (xs : Fin n → Vertex G support),
    (∀ i, xs i ∈ X) →
      ((quotientStructure G support R).rel r xs ↔
        R.rel r (fun i => project G support (xs i)))) ∧
  (∀ f q, q ∈ X →
    project G support '' liftOutput G support out closed f q =
      out f (project G support q))

/-- Consequently the projection is a homomorphism-embedding on EVERY
irreducible closed induced test, in the survey's precise sense. -/
theorem project_embeds_irreducible
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (X : Set (Vertex G support)) [Nonempty X]
    (hclosed : UnaryClosed (liftOutput G support out closed) (fun q => q ∈ X))
    (hirr : IsIrreducible
      (inducedAtlas G support R X)
      (inducedOutput G support out closed X)) :
    ProjectionIsEmbeddingOn G support R out closed X := by
  obtain ⟨s, chi, hchart⟩ :=
    irreducible_lies_in_chart G support R out closed complete X hclosed hirr
  refine ⟨?_, ?_, ?_⟩
  · intro p hp q hq heq
    obtain ⟨hps, hpe⟩ := hchart ⟨p, hp⟩
    obtain ⟨hqs, hqe⟩ := hchart ⟨q, hq⟩
    have hc : copy G support s chi (project G support p) hps =
        copy G support s chi (project G support q) hqs := by
      cases heq
      rfl
    exact hpe.symm.trans (hc.trans hqe)
  · intro n r xs hxs
    constructor
    · rintro ⟨t, psi, ys, hrel, hys⟩
      have hproject : (fun i => (ys i).val) =
          (fun i => project G support (xs i)) := by
        funext i
        exact congrArg (project G support) (hys i)
      simpa only [hproject] using hrel
    · intro hrel
      refine ⟨s, chi,
        (fun i => ⟨project G support (xs i),
          (hchart ⟨xs i, hxs i⟩).1⟩), hrel, ?_⟩
      intro i
      exact (hchart ⟨xs i, hxs i⟩).2
  · intro f q hq
    exact liftOutput_projection G support out closed f q

end GluingEPPA.Sparsening.ChartAtlas
