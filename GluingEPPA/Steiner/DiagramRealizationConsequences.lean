import GluingEPPA.Steiner.DiagramRealizedSTS

/-!
# Finite Steiner realization and closed local copies

The quotient triples are exactly the images of local triples. The original
point-label criterion makes their points distinct, and the already proved
uniqueness of the third point gives the partial Steiner condition.
Moreover, each local canonical map reflects triples and has closed image.
These are the remaining combinatorial statements of Lemma 5.1.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- Different labels cannot become equal in the free quotient. -/
theorem canonicalPoint_eq_label (L : LabelledSteiner D Ω)
    (u v : V) (g h : (family D Finset.univ).Carrier)
    (x y : Ω) (hx : L.present u x) (hy : L.present v y)
    (hp : canonicalPoint D L u g x hx = canonicalPoint D L v h y hy) :
    x = y :=
  ((canonicalPoint_eq_iff D L u v g h x y hx hy).mp hp).1

/-- The points of every quotient triple are distinct. -/
theorem realizedTriple_distinct (L : LabelledSteiner D Ω)
    (p q r : realizedPoint D L) (h : realizedTriple D L p q r) :
    p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  rcases h with ⟨u,g,x,y,z,ht,hp,hq,hr⟩
  obtain ⟨hxy,hxz,hyz⟩ := L.triple_distinct u x y z ht
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hxy
    exact canonicalPoint_eq_label D L u u g g x y
      ((L.triple_present u x y z ht).1)
      ((L.triple_present u x y z ht).2.1)
      (hp.symm.trans (h.trans hq))
  · intro h
    apply hxz
    exact canonicalPoint_eq_label D L u u g g x z
      ((L.triple_present u x y z ht).1)
      ((L.triple_present u x y z ht).2.2)
      (hp.symm.trans (h.trans hr))
  · intro h
    apply hyz
    exact canonicalPoint_eq_label D L u u g g y z
      ((L.triple_present u x y z ht).2.1)
      ((L.triple_present u x y z ht).2.2)
      (hq.symm.trans (h.trans hr))

/-- A triple on three vertices of one local copy is local, not an extra
    triple created by identifications elsewhere. -/
theorem canonicalPoint_triple_iff (L : LabelledSteiner D Ω)
    (u : V) (g : (family D Finset.univ).Carrier)
    (x y z : Ω) (hx : L.present u x)
    (hy : L.present u y) (hz : L.present u z) :
    realizedTriple D L (canonicalPoint D L u g x hx)
        (canonicalPoint D L u g y hy) (canonicalPoint D L u g z hz) ↔
      L.triple u x y z := by
  constructor
  · intro h
    obtain ⟨w, hw, heq⟩ :=
      realizedTriple_closed D L u g x y hx hy
        (canonicalPoint D L u g z hz) h
    have hzw : z = w := canonicalPoint_eq_label D L u u g g z w hz
      ((L.triple_present u x y w hw).2.2) heq
    simpa only [← hzw] using hw
  · intro ht
    exact ⟨u,g,x,y,z,ht,rfl,rfl,rfl⟩

/-- Local point occurrences are finite whenever their sites, sheets and
    point labels are finite. -/
instance pointOccurrence_finite (L : LabelledSteiner D Ω)
    {G : Type u} [Finite G] [Finite Ω] :
    Finite (PointOccurrence D L G) := by
  classical
  apply Finite.of_injective
    (fun p : PointOccurrence D L G => (p.site,p.sheet,p.label))
  intro p q heq
  cases p with
  | mk pu pg px ph =>
    cases q with
    | mk qu qg qx qh =>
      have hsite : pu = qu := congrArg (fun z => z.1) heq
      have hsheet : pg = qg := congrArg (fun z => z.2.1) heq
      have hlabel : px = qx := congrArg (fun z => z.2.2) heq
      subst qu
      subst qg
      subst qx
      rfl

/-- The free quotient of a finite diagram with finite local labels
    has finitely many points. -/
instance realizedPoint_finite (L : LabelledSteiner D Ω) [Finite Ω] :
    Finite (realizedPoint D L) := by
  unfold realizedPoint FreePoint
  infer_instance

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
