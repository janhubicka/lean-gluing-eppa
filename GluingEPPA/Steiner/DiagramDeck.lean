import GluingEPPA.Steiner.DiagramRealizationConsequences

/-!
# The automorphisms of the free quotient induced by valuation translations

Right transitions follow edges of the valuation diagram. Prefixing a
word is a different operation: on its valuation group it is left
multiplication. This commutes with every edge transition, therefore it
descends to the quotient of point occurrences. The induced bijection
preserves all quotient triples.

The action is constructed from the actual recursive family, not an
abstract group supplying EPPA.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w} (D : EdgeGraph V E)

/-- Left multiplication changes only the valuation coordinate of an occurrence. -/
def occurrenceLeft (L : LabelledSteiner D Ω)
    {G : Type u} [Group G] (k : G)
    (p : PointOccurrence D L G) : PointOccurrence D L G :=
  ⟨p.site, k * p.sheet, p.label, p.valid⟩

/-- Left multiplication respects the exact point-identification relation. -/
theorem occurrenceLeft_respects (L : LabelledSteiner D Ω)
    {G : Type u} [Group G] (a : E → G)
    (ha : ∀ e, a e * a e = 1)
    (k : G) {p q : PointOccurrence D L G}
    (h : (pointSetoid D L a ha).r p q) :
    (pointSetoid D L a ha).r
      (occurrenceLeft D L k p) (occurrenceLeft D L k q) := by
  change p.label = q.label ∧
    D.CayleyWalk (edgesCarrying L.overlap p.label)
      a p.site p.sheet q.site q.sheet at h
  change p.label = q.label ∧
    D.CayleyWalk (edgesCarrying L.overlap p.label)
      a p.site (k * p.sheet) q.site (k * q.sheet)
  exact ⟨h.1, (D.cayleyWalk_left_mul
    (edgesCarrying L.overlap p.label) a k
    p.site q.site p.sheet q.sheet).2 h.2⟩

/-- Translation is well defined on quotient points. -/
def freePointLeft (L : LabelledSteiner D Ω)
    {G : Type u} [Group G] (a : E → G)
    (ha : ∀ e, a e * a e = 1) (k : G) :
    FreePoint D L a ha → FreePoint D L a ha :=
  Quotient.map (occurrenceLeft D L k)
    (fun _ _ h => occurrenceLeft_respects D L a ha k h)

@[simp] theorem freePointLeft_at (L : LabelledSteiner D Ω)
    {G : Type u} [Group G] (a : E → G)
    (ha : ∀ e, a e * a e = 1)
    (k : G) (u : V) (g : G) (x : Ω) (hx : L.present u x) :
    freePointLeft D L a ha k (pointAt D L a ha u g x hx) =
      pointAt D L a ha u (k * g) x hx := rfl

theorem freePointLeft_comp (L : LabelledSteiner D Ω)
    {G : Type u} [Group G] (a : E → G)
    (ha : ∀ e, a e * a e = 1)
    (k l : G) (p : FreePoint D L a ha) :
    freePointLeft D L a ha k (freePointLeft D L a ha l p) =
      freePointLeft D L a ha (k * l) p := by
  induction p using Quotient.inductionOn with
  | _ p =>
      cases p with
      | mk site sheet label valid =>
          change
            pointAt D L a ha site (k * (l * sheet)) label valid =
              pointAt D L a ha site ((k * l) * sheet) label valid
          rw [mul_assoc]

@[simp] theorem freePointLeft_one (L : LabelledSteiner D Ω)
    {G : Type u} [Group G] (a : E → G)
    (ha : ∀ e, a e * a e = 1)
    (p : FreePoint D L a ha) :
    freePointLeft D L a ha 1 p = p := by
  induction p using Quotient.inductionOn with
  | _ p =>
      cases p with
      | mk site sheet label valid =>
          change pointAt D L a ha site (1 * sheet) label valid =
            pointAt D L a ha site sheet label valid
          simp

/-- Each valuation-group element induces a quotient automorphism. -/
def freePointLeftEquiv (L : LabelledSteiner D Ω)
    {G : Type u} [Group G] (a : E → G)
    (ha : ∀ e, a e * a e = 1) (k : G) :
    Equiv.Perm (FreePoint D L a ha) where
  toFun := freePointLeft D L a ha k
  invFun := freePointLeft D L a ha k⁻¹
  left_inv p := by
    calc
      freePointLeft D L a ha k⁻¹ (freePointLeft D L a ha k p) =
          freePointLeft D L a ha (k⁻¹ * k) p :=
        freePointLeft_comp D L a ha k⁻¹ k p
      _ = p := by simp
  right_inv p := by
    calc
      freePointLeft D L a ha k (freePointLeft D L a ha k⁻¹ p) =
          freePointLeft D L a ha (k * k⁻¹) p :=
        freePointLeft_comp D L a ha k k⁻¹ p
      _ = p := by simp

variable [Finite V] [Fintype E] [DecidableEq E]

/-- The concrete deck automorphism on the Steiner free quotient. -/
noncomputable def realizedDeck (L : LabelledSteiner D Ω)
    (k : (family D Finset.univ).Carrier) :
    Equiv.Perm (realizedPoint D L) :=
  freePointLeftEquiv D L (family D Finset.univ).edge
    (fun e => family_square D Finset.univ e) k

/-- Deck automorphisms preserve all triples of the realized Steiner system. -/
theorem realizedDeck_preserves_triple (L : LabelledSteiner D Ω)
    (k : (family D Finset.univ).Carrier)
    (p q r : realizedPoint D L)
    (ht : realizedTriple D L p q r) :
    realizedTriple D L ((realizedDeck D L k) p)
      ((realizedDeck D L k) q) ((realizedDeck D L k) r) := by
  rcases ht with ⟨u,g,x,y,z,t,hp,hq,hr⟩
  refine ⟨u,k*g,x,y,z,t,?_,?_,?_⟩
  · rw [hp]
    rfl
  · rw [hq]
    rfl
  · rw [hr]
    rfl

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
