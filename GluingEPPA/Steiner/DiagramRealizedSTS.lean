import GluingEPPA.Steiner.DiagramCompletion

/-!
# The partial Steiner condition in the free realization

A quotient triple is the image of a triple in one lifted local system.
Exact intersection of the walks identifying its first two points forces
the third points of two competing triples to agree. The same argument,
reversed, shows that canonical local copies are closed: if two vertices
of a quotient triple lie in the copy, its third vertex lies there too.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- A quotient triple comes from some triple in an actual lifted copy. -/
def realizedTriple (L : LabelledSteiner D Ω)
    (p q r : realizedPoint D L) : Prop :=
  ∃ (u : V) (g : (family D Finset.univ).Carrier) (x y z : Ω)
    (ht : L.triple u x y z),
    p = canonicalPoint D L u g x ((L.triple_present u x y z ht).1) ∧
    q = canonicalPoint D L u g y ((L.triple_present u x y z ht).2.1) ∧
    r = canonicalPoint D L u g z ((L.triple_present u x y z ht).2.2)

/-- In the quotient, two triples sharing the same first two vertices
    have equal third vertices. -/
theorem realizedTriple_unique (L : LabelledSteiner D Ω)
    (p q r s : realizedPoint D L)
    (hr : realizedTriple D L p q r) (hs : realizedTriple D L p q s) :
    r = s := by
  rcases hr with ⟨u, g, x, y, z, ht, hp, hq, hr⟩
  rcases hs with ⟨v, h, x', y', z', ht', hp', hq', hs⟩
  have hx : x = x' := ((canonicalPoint_eq_iff D L u v g h x x'
    ((L.triple_present u x y z ht).1)
    ((L.triple_present v x' y' z' ht').1)).mp (hp.symm.trans hp')).1
  have hy : y = y' := ((canonicalPoint_eq_iff D L u v g h y y'
    ((L.triple_present u x y z ht).2.1)
    ((L.triple_present v x' y' z' ht').2.1)).mp (hq.symm.trans hq')).1
  subst x'
  subst y'
  have hpx := hp.symm.trans hp'
  have hpy := hq.symm.trans hq'
  obtain ⟨_, hz⟩ := completion_agrees_across_copies D L
    u v g h x y z z' ht ht' hpx hpy
  exact hr.trans (hz.trans hs.symm)

/-- Symmetry of triples is inherited from each local system. -/
theorem realizedTriple_swap (L : LabelledSteiner D Ω)
    (p q r : realizedPoint D L) (h : realizedTriple D L p q r) :
    realizedTriple D L q p r := by
  rcases h with ⟨u,g,x,y,z,ht,hp,hq,hr⟩
  refine ⟨u,g,y,x,z,L.triple_swap u x y z ht, ?_, ?_, ?_⟩
  · exact hq
  · exact hp
  · exact hr

theorem realizedTriple_rotate (L : LabelledSteiner D Ω)
    (p q r : realizedPoint D L) (h : realizedTriple D L p q r) :
    realizedTriple D L q r p := by
  rcases h with ⟨u,g,x,y,z,ht,hp,hq,hr⟩
  refine ⟨u,g,y,z,x,L.triple_rotate u x y z ht, ?_, ?_, ?_⟩
  · exact hq
  · exact hr
  · exact hp

/-- If the first two quotient points are in one canonical local copy,
    the triple and its third point also have representatives there. -/
theorem realizedTriple_closed (L : LabelledSteiner D Ω)
    (u : V) (g : (family D Finset.univ).Carrier)
    (x y : Ω) (hx : L.present u x) (hy : L.present u y)
    (q : realizedPoint D L)
    (ht : realizedTriple D L
      (canonicalPoint D L u g x hx) (canonicalPoint D L u g y hy) q) :
    ∃ (z : Ω) (hz : L.triple u x y z),
      q = canonicalPoint D L u g z ((L.triple_present u x y z hz).2.2) := by
  rcases ht with ⟨v,h,x',y',z,t,px,py,pz⟩
  have xe : x = x' := ((canonicalPoint_eq_iff D L u v g h x x'
    hx ((L.triple_present v x' y' z t).1)).mp px).1
  have ye : y = y' := ((canonicalPoint_eq_iff D L u v g h y y'
    hy ((L.triple_present v x' y' z t).2.1)).mp py).1
  subst x'
  subst y'
  have wx := ((canonicalPoint_eq_iff D L v u h g x x
    ((L.triple_present v x y z t).1) hx).mp px.symm).2
  have wy := ((canonicalPoint_eq_iff D L v u h g y y
    ((L.triple_present v x y z t).2.1) hy).mp py.symm).2
  obtain ⟨tnew, wz⟩ := two_walks_carry_triple D
    L.overlap L.triple L.overlap_closed x y z v u h g wx wy t
  refine ⟨z,tnew,?_⟩
  calc
    q = canonicalPoint D L v h z ((L.triple_present v x y z t).2.2) := pz
    _ = canonicalPoint D L u g z
          ((L.triple_present u x y z tnew).2.2) :=
      (canonicalPoint_eq_iff D L v u h g z z
        ((L.triple_present v x y z t).2.2)
        ((L.triple_present u x y z tnew).2.2)).mpr ⟨rfl,wz⟩

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
