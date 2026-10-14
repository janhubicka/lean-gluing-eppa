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

lemma restricted_path_forget {K : V → Prop} {p q : V × (E → ZMod 2)}
    (h : Relation.ReflTransGen (restrictedLift G K) p q) :
    Relation.ReflTransGen G.LiftEdge p q := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.1

/-- An actual supported walk with prescribed parity, from every initial
valuation. No quotient equality or record completeness is assumed. -/
def Realizes (K : V → Prop) (s t : V) (d : E → ZMod 2) : Prop :=
  ∀ chi : E → ZMod 2,
    Relation.ReflTransGen (restrictedLift G K) (s, chi) (t, chi + d)

lemma realizes_zero (K : V → Prop) (s : V) : Realizes G K s s 0 := by
  intro chi
  simpa only [add_zero] using
    (Relation.ReflTransGen.refl :
      Relation.ReflTransGen (restrictedLift G K) (s, chi) (s, chi))

lemma realizes_add {K : V → Prop} {s t z : V} {a b : E → ZMod 2}
    (ha : Realizes G K s t a) (hb : Realizes G K t z b) :
    Realizes G K s z (a + b) := by
  intro chi
  simpa only [add_assoc] using (ha chi).trans (hb (chi + a))

lemma realizes_edge {K : V → Prop} (s t : V) (e : E)
    (inc : G.Inc e s t) (hs : K s) (ht : K t) :
    Realizes G K s t (edgeUnit e) := by
  intro chi
  exact Relation.ReflTransGen.single ⟨⟨e, inc, rfl⟩, hs, ht⟩

lemma realizes_sum {T : Type*} (K : V → Prop) (s : V)
    (F : Finset T) (c : T → E → ZMod 2)
    (each : ∀ t ∈ F, Realizes G K s s (c t)) :
    Realizes G K s s (∑ t ∈ F, c t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using realizes_zero G K s
  | @insert t F ht ih =>
    rw [Finset.sum_insert ht]
    exact realizes_add G (each t (Finset.mem_insert_self t F))
      (ih (fun r hr => each r (Finset.mem_insert_of_mem hr)))

/-- Choose one spoke, or the zero walk for equal endpoints. -/
lemma exists_spoke
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b) (s t : V) :
    ∃ c : E → ZMod 2, (s = t → c = 0) ∧
      ∀ K : V → Prop, K s → K t →
        Realizes G K s t c ∧ Realizes G K t s c := by
  classical
  by_cases hst : s = t
  · subst t
    exact ⟨0, fun _ => rfl, fun K _ _ =>
      ⟨realizes_zero G K s, realizes_zero G K s⟩⟩
  · obtain ⟨e, he⟩ := complete s t hst
    exact ⟨edgeUnit e, fun h => (hst h).elim, fun K hs ht =>
      ⟨realizes_edge G s t e he hs ht,
       realizes_edge G t s e (G.inc_symm he) ht hs⟩⟩

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
  rw [boundary_pairing G d (fun a => c a f)]
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
    Realizes G K s t d := by
  classical
  choose c hzero hwalk using (fun a : V => exists_spoke G complete s a)
  have hz : c s = 0 := hzero s rfl
  let loop : E → E → ZMod 2 := fun e f =>
    d e * (c (G.left e) f + edgeUnit e f + c (G.right e) f)
  have hloops : ∀ e, Realizes G K s s (loop e) := by
    intro e
    have bits : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases bits (d e) with he | he
    · have hloop : loop e = 0 := by funext f; simp [loop, he]
      rw [hloop]
      exact realizes_zero G K s
    · have hn : d e ≠ 0 := by rw [he]; exact one_ne_zero
      obtain ⟨hl, hr⟩ := supported e hn
      have hpath := realizes_add G
        (realizes_add G (hwalk (G.left e) K hs hl).1
          (realizes_edge G (G.left e) (G.right e) e (Or.inl ⟨rfl, rfl⟩) hl hr))
        (hwalk (G.right e) K hs hr).2
      have hloop : loop e = c (G.left e) + edgeUnit e + c (G.right e) := by
        funext f
        simp [loop, he]
      rw [hloop]
      exact hpath
  have hsum : (∑ e, loop e) = d + c t := by
    funext f
    change (∑ e, loop e) f = d f + c t f
    rw [Finset.sum_apply]
    change (∑ e, d e * (c (G.left e) f + edgeUnit e f + c (G.right e) f)) = _
    rw [cone_sum G]
    simp_rw [ends]
    simp [add_mul, ite_mul, Finset.sum_add_distrib, hz]
  have whole := realizes_add G
    (realizes_sum G K s Finset.univ loop (fun e _ => hloops e))
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
  have hwalk := realizes_of_boundary G complete K s t hs ht (chi + psi) hi hb chi
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
    have hp := restricted_path_forget G h
    exact ⟨charge_path G hp, fun e he => exterior_path G K e he h⟩
  · rintro ⟨hc, he⟩
    exact supported_walk_of_records G complete K s t hs ht chi psi hc he

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
  apply supported_walk_of_records G complete (support p) (origin p) s
    (origin_mem p) (hs p) (chi p) c
  · funext v
    exact (record p v).trans (hb v).symm
  · intro e he
    exact (hext p e he).symm

end GluingEPPA.Sparsening
