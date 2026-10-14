import GluingEPPA.Sparsening.RecordInvariance

/-!
Complete records classify supported Boolean walks. We construct actual walks:
each supported edge gives a rooted excursion, and boundary cancellation removes
all unwanted spokes. This also covers disconnected parity support, loops,
parallel edges, empty paths and singleton allowed sets.
-/
namespace GluingEPPA.Sparsening
universe u v w
variable {V : Type u} {E : Type v}
variable (G : GluingEPPA.EdgeGraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma vector_add_self (c : E → ZMod 2) : c + c = 0 := by
  funext e
  exact bit_add_self (c e)

/-- An actual supported walk with prescribed parity, from every initial
valuation. No quotient equality or record completeness is assumed. -/
def Realizes (K : V → Prop) (s t : V) (d : E → ZMod 2) : Prop :=
  ∀ chi : E → ZMod 2,
    Relation.ReflTransGen (restrictedLift G K) (s, chi) (t, chi + d)

lemma realizes_zero (K : V → Prop) (s : V) : G.Realizes K s s 0 := by
  intro chi
  simpa only [add_zero] using
    (Relation.ReflTransGen.refl :
      Relation.ReflTransGen (restrictedLift G K) (s, chi) (s, chi))

lemma realizes_add {K : V → Prop} {s t z : V} {a b : E → ZMod 2}
    (ha : G.Realizes K s t a) (hb : G.Realizes K t z b) :
    G.Realizes K s z (a + b) := by
  intro chi
  simpa only [add_assoc] using (ha chi).trans (hb (chi + a))

lemma realizes_edge {K : V → Prop} (s t : V) (e : E)
    (inc : G.Inc e s t) (hs : K s) (ht : K t) :
    G.Realizes K s t (edgeUnit e) := by
  intro chi
  exact Relation.ReflTransGen.single ⟨⟨e, inc, rfl⟩, hs, ht⟩

lemma realizes_sum {T : Type*} (K : V → Prop) (s : V)
    (F : Finset T) (c : T → E → ZMod 2)
    (each : ∀ t ∈ F, G.Realizes K s s (c t)) :
    G.Realizes K s s (∑ t ∈ F, c t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using G.realizes_zero K s
  | @insert t F ht ih =>
    rw [Finset.sum_insert ht]
    exact G.realizes_add (each t (Finset.mem_insert_self t F))
      (ih (fun r hr => each r (Finset.mem_insert_of_mem hr)))

/-- Choose one spoke, or the zero walk for equal endpoints. -/
lemma exists_spoke
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b) (s t : V) :
    ∃ c : E → ZMod 2, (s = t → c = 0) ∧
      ∀ K : V → Prop, K s → K t →
        G.Realizes K s t c ∧ G.Realizes K t s c := by
  classical
  by_cases hst : s = t
  · subst t
    exact ⟨0, fun _ => rfl, fun K _ _ =>
      ⟨G.realizes_zero K s, G.realizes_zero K s⟩⟩
  · obtain ⟨e, he⟩ := complete s t hst
    exact ⟨edgeUnit e, fun h => (hst h).elim, fun K hs ht =>
      ⟨G.realizes_edge s t e he hs ht,
       G.realizes_edge t s e (G.inc_symm he) ht hs⟩⟩

/-- Pairing with the boundary counts the two endpoints of every edge. -/
lemma boundary_pairing (d : E → ZMod 2) (w : V → ZMod 2) :
    (∑ a, boundary G d a * w a) =
      ∑ e, d e * (w (G.left e) + w (G.right e)) := by
  simp only [boundary, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [mul_add, add_mul, mul_ite, ite_mul, Finset.sum_add_distrib]

/-- Sum of all rooted excursions: the correction is exactly the boundary
paired with the chosen spokes. No connected-support hypothesis is needed. -/
lemma cone_sum (c : V → E → ZMod 2) (d : E → ZMod 2) (f : E) :
    (∑ e, d e * (c (G.left e) f + edgeUnit e f + c (G.right e) f)) =
      d f + ∑ a, boundary G d a * c a f := by
  rw [G.boundary_pairing d (fun a => c a f)]
  have hu : (∑ e, d e * edgeUnit e f) = d f := by
    simp [edgeUnit, mul_ite]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hu]
  abel

/-- Internal edge vectors with the endpoint boundary are realized by an
actual walk. Rooted excursions handle every connected component of support. -/
theorem realizes_of_boundary
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (K : V → Prop) (s t : V) (hs : K s) (ht : K t)
    (d : E → ZMod 2)
    (supported : ∀ e, d e ≠ 0 → K (G.left e) ∧ K (G.right e))
    (ends : ∀ a, boundary G d a =
      (if s = a then 1 else 0) + (if t = a then 1 else 0)) :
    G.Realizes K s t d := by
  classical
  choose c hzero hwalk using (fun a : V => G.exists_spoke complete s a)
  have hz : c s = 0 := hzero s rfl
  let loop : E → E → ZMod 2 := fun e f =>
    d e * (c (G.left e) f + edgeUnit e f + c (G.right e) f)
  have hloops : ∀ e, G.Realizes K s s (loop e) := by
    intro e
    have bits : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases bits (d e) with he | he
    · have hloop : loop e = 0 := by funext f; simp [loop, he]
      rw [hloop]
      exact G.realizes_zero K s
    · have hn : d e ≠ 0 := by rw [he]; exact one_ne_zero
      obtain ⟨hl, hr⟩ := supported e hn
      have hpath := G.realizes_add
        (G.realizes_add (hwalk (G.left e) K hs hl).1
          (G.realizes_edge (G.left e) (G.right e) e (Or.inl ⟨rfl, rfl⟩) hl hr))
        (hwalk (G.right e) K hs hr).2
      simpa only [loop, he, one_mul, Pi.add_apply] using hpath
  have hsum : (∑ e, loop e) = d + c t := by
    funext f
    change (∑ e, loop e) f = d f + c t f
    rw [Finset.sum_apply]
    change (∑ e, d e * (c (G.left e) f + edgeUnit e f + c (G.right e) f)) = _
    rw [G.cone_sum, ends]
    simp [add_mul, ite_mul, Finset.sum_add_distrib, hz]
  have whole := G.realizes_add
    (G.realizes_sum K s Finset.univ loop (fun e _ => hloops e))
    (hwalk t K hs ht).1
  simpa only [hsum, add_assoc, vector_add_self, add_zero] using whole

lemma bit_shift_eq {a b c d : ZMod 2} (h : a + c = b + d) : a + b = c + d := by
  calc
    a + b = ((a + c) + c) + b := by rw [add_assoc a c c, bit_add_self, add_zero]
    _ = ((b + d) + c) + b := by rw [h]
    _ = (b + b) + (c + d) := by abel
    _ = c + d := by rw [bit_add_self, zero_add]

/-- The missing converse in the manuscript: equal pointed boundary charges
and exterior coordinates imply a supported Boolean walk. -/
theorem supported_walk_of_records
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (K : V → Prop) (s t : V) (hs : K s) (ht : K t)
    (chi psi : E → ZMod 2)
    (hcharge : charge G (s, chi) = charge G (t, psi))
    (exterior : ∀ e, ¬ (K (G.left e) ∧ K (G.right e)) → chi e = psi e) :
    Relation.ReflTransGen (restrictedLift G K) (s, chi) (t, psi) := by
  have hb : ∀ a, boundary G (chi + psi) a =
      (if s = a then 1 else 0) + (if t = a then 1 else 0) := by
    intro a
    rw [boundary_add]
    exact bit_shift_eq (congrFun hcharge a)
  have hi : ∀ e, (chi + psi) e ≠ 0 → K (G.left e) ∧ K (G.right e) := by
    intro e he
    by_contra hn
    apply he
    change chi e + psi e = 0
    rw [exterior e hn, bit_add_self]
  have hwalk := G.realizes_of_boundary complete K s t hs ht (chi + psi) hi hb chi
  have hv : chi + (chi + psi) = psi := by
    rw [← add_assoc, vector_add_self, zero_add]
  simpa only [hv] using hwalk

/-- Full classification of path components on valid occurrences. -/
theorem supported_walk_iff_records
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (K : V → Prop) (s t : V) (hs : K s) (ht : K t)
    (chi psi : E → ZMod 2) :
    Relation.ReflTransGen (restrictedLift G K) (s, chi) (t, psi) ↔
      charge G (s, chi) = charge G (t, psi) ∧
        ∀ e, ¬ (K (G.left e) ∧ K (G.right e)) → chi e = psi e := by
  constructor
  · intro h
    have hp : Relation.ReflTransGen G.LiftEdge (s, chi) (t, psi) := by
      induction h with
      | refl => exact .refl
      | tail _ step ih => exact ih.tail step.1
    exact ⟨charge_path G hp, fun e he => exterior_path G K e he h⟩
  · rintro ⟨hc, he⟩
    exact G.supported_walk_of_records complete K s t hs ht chi psi hc he

/-- The common lifted record is now reached by genuine supported paths
for every point, not merely a solution of the record equations. -/
theorem common_supported_representative {P : Type w}
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (support : P → V → Prop) (origin : P → V)
    (chi : P → E → ZMod 2) (alpha : V → ZMod 2)
    (origin_mem : ∀ p, support p (origin p))
    (odd : (∑ v, alpha v) = 1)
    (record : ∀ p v,
      boundary G (chi p) v + (if origin p = v then 1 else 0) = alpha v)
    (consistent : ∀ p q e, ¬ internal G support p e →
      ¬ internal G support q e → chi p e = chi q e) :
    ∃ s c, (∀ p, support p s) ∧
      ∀ p, Relation.ReflTransGen (restrictedLift G (support p))
        (origin p, chi p) (s, c) := by
  obtain ⟨s, c, hs, hext, hb⟩ := common_lifted_record G complete support origin chi alpha
    origin_mem odd record consistent
  refine ⟨s, c, hs, ?_⟩
  intro p
  apply G.supported_walk_of_records complete (support p) (origin p) s
    (origin_mem p) (hs p) (chi p) c
  · funext v
    exact (record p v).trans (hb v).symm
  · intro e he
    exact (hext p e he).symm

end GluingEPPA.Sparsening
