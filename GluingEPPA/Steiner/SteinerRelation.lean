import GluingEPPA.Steiner.PresentLabels

/-!
# The unordered partial Steiner property of the genuine realization

The preceding gluing theorem proves third-point uniqueness for the
first two ordered entries. A partial Steiner triple system needs the
corresponding symmetric, irreflexive three-element relation. These
elementary lemmas show that symmetric, distinct local triples retain
all these properties in the finite free realization.
-/

namespace GluingEPPA.Steiner

universe u v
variable {V E : Type u} {A : Type v}
variable [Fintype E] [DecidableEq E] [Finite V]

structure LocalSteinerAxioms (D : LabelledGraph V E A) where
  swap : ∀ {s x y z}, D.triple s x y z → D.triple s y x z
  cycle : ∀ {s x y z}, D.triple s x y z → D.triple s y z x
  distinct : ∀ {s x y z}, D.triple s x y z → x ≠ y ∧ y ≠ z ∧ z ≠ x

namespace LocalSteinerAxioms

variable {D : LabelledGraph V E A}
variable (H : LocalSteinerAxioms D) (P : PresentLabels D)

theorem realized_swap {b c d : P.Actual}
    (ht : P.triple b c d) : P.triple c b d := by
  obtain ⟨s, x, y, z, h, hb, hc, hd⟩ := ht
  exact ⟨s, y, x, z, H.swap h, hc, hb, hd⟩

theorem realized_cycle {b c d : P.Actual}
    (ht : P.triple b c d) : P.triple c d b := by
  obtain ⟨s, x, y, z, h, hb, hc, hd⟩ := ht
  exact ⟨s, y, z, x, H.cycle h, hc, hd, hb⟩

theorem realized_distinct_first {b c d : P.Actual}
    (ht : P.triple b c d) : b ≠ c := by
  obtain ⟨s, x, y, z, h, hb, hc, hd⟩ := ht
  intro heq
  have hbig : (D.lifted).copy s x = (D.lifted).copy s y :=
    hb.trans ((congrArg Subtype.val heq).trans hc.symm)
  exact (H.distinct h).1 ((D.lifted).copy_injective s hbig)

theorem realized_distinct {b c d : P.Actual}
    (ht : P.triple b c d) : b ≠ c ∧ c ≠ d ∧ d ≠ b := by
  refine ⟨H.realized_distinct_first P ht, ?_, ?_⟩
  · exact H.realized_distinct_first P (H.realized_cycle P ht)
  · exact H.realized_distinct_first P (H.realized_cycle P
      (H.realized_cycle P ht))

/-- The symmetric triple relation has unique completion of any ordered pair. -/
theorem realized_unique {b c d e : P.Actual}
    (h : P.triple b c d) (k : P.triple b c e) : d = e :=
  P.triple_unique h k

/-- An elementary relational presentation of a partial Steiner triple system. -/
structure PartialSteiner (B : Type*) where
  triple : B → B → B → Prop
  swap : ∀ {x y z}, triple x y z → triple y x z
  cycle : ∀ {x y z}, triple x y z → triple y z x
  distinct : ∀ {x y z}, triple x y z → x ≠ y ∧ y ≠ z ∧ z ≠ x
  unique : ∀ {x y z z'}, triple x y z → triple x y z' → z = z'

noncomputable def realizedStructure : PartialSteiner P.Actual where
  triple := P.triple
  swap := H.realized_swap P
  cycle := H.realized_cycle P
  distinct := H.realized_distinct P
  unique := P.triple_unique

end LocalSteinerAxioms
end GluingEPPA.Steiner
