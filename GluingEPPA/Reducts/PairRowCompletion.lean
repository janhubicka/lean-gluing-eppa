import GluingEPPA.Reducts.PairValuationConjugation

/-!
Explicit incidence completion for Boolean cross-pair valuations.
The auxiliary table q is input here; MultipartiteReplication constructs it.
Prescribed rows are entire rows. No upstairs extension or coherence law is
assumed: the actual conjugation maps are used in the two final endpoints.
-/
namespace GluingEPPA.Reducts.PairRowCompletion
open GluingEPPA.Reducts.PairValuationConjugation
universe u
variable {W : Type u}

def fill (dx dy selector defect source target : Bool) : Bool :=
  if dx then source else if dy then Bool.xor defect target
  else if selector then false else defect

theorem fill_pair (dx dy s d a b : Bool)
    (h : dx = true → dy = true → Bool.xor a b = d) :
    Bool.xor (fill dx dy s d a b) (fill dy dx (Bool.not s) d b a) = d := by
  cases dx <;> cases dy <;> cases s <;> cases d <;> cases a <;> cases b <;>
    simp_all [fill]

theorem xor_negations (a b : Bool) :
    Bool.xor (Bool.not a) (Bool.not b) = Bool.xor a b := by
  cases a <;> cases b <;> rfl

def completeRows (inside : W → Bool) (b q rows : W → W → Bool)
    (x y : W) : Bool :=
  fill (inside x) (inside y) (b x y) (Bool.xor (q x y) (b x y))
    (rows x y) (rows y x)

theorem completeRows_on_domain (inside : W → Bool) (b q rows : W → W → Bool)
    (x : W) (hx : inside x = true) :
    ∀ y, completeRows inside b q rows x y = rows x y := by
  intro y
  simp [completeRows, fill, hx]

theorem completeRows_pair (inside : W → Bool) (b q rows : W → W → Bool)
    (x y : W)
    (hb : b y x = Bool.not (b x y))
    (hq : q y x = Bool.not (q x y))
    (hrows : inside x = true → inside y = true →
      Bool.xor (rows x y) (rows y x) = Bool.xor (q x y) (b x y)) :
    Bool.xor (completeRows inside b q rows x y)
      (completeRows inside b q rows y x) = Bool.xor (q x y) (b x y) := by
  unfold completeRows
  rw [hb, hq, xor_negations]
  exact fill_pair (inside x) (inside y) (b x y)
    (Bool.xor (q x y) (b x y)) (rows x y) (rows y x) hrows

theorem undo_defect (b q a c : Bool) (h : Bool.xor a c = Bool.xor q b) :
    Bool.xor (Bool.xor b a) c = q := by
  cases b <;> cases q <;> cases a <;> cases c <;> simp_all

theorem twisted_completion (inside : W → Bool) (b q rows : W → W → Bool)
    (x y : W)
    (hb : b y x = Bool.not (b x y))
    (hq : q y x = Bool.not (q x y))
    (hrows : inside x = true → inside y = true →
      Bool.xor (rows x y) (rows y x) = Bool.xor (q x y) (b x y)) :
    twistedBase b (completeRows inside b q rows) x y = q x y := by
  exact undo_defect (b x y) (q x y)
    (completeRows inside b q rows x y) (completeRows inside b q rows y x)
    (completeRows_pair inside b q rows x y hb hq hrows)

/-- The completed rows give actual automorphisms of the supported relation. -/
theorem completed_lift_preserves_edge (inside : W → Bool)
    (cross : W → W → Prop) (b q rows : W → W → Bool) (p : BasePerm W)
    (hb : ∀ x y, cross x y → b y x = Bool.not (b x y))
    (hq : ∀ x y, cross x y → q y x = Bool.not (q x y))
    (hrows : ∀ x y, cross x y → inside x = true → inside y = true →
      Bool.xor (rows x y) (rows y x) = Bool.xor (q x y) (b x y))
    (hc : ∀ x y, cross (p.forward x) (p.forward y) ↔ cross x y)
    (hinv : ∀ x y, cross x y → q (p.forward x) (p.forward y) = q x y)
    (u v : Vertex W) :
    Edge cross b (lift (completeRows inside b q rows) p u)
      (lift (completeRows inside b q rows) p v) ↔ Edge cross b u v := by
  apply lift_preserves_edge cross b (completeRows inside b q rows) p hc
  intro x y hxy
  have hnew := (hc x y).2 hxy
  rw [twisted_completion inside b q rows (p.forward x) (p.forward y)
        (hb _ _ hnew) (hq _ _ hnew) (hrows _ _ hnew),
      twisted_completion inside b q rows x y (hb _ _ hxy) (hq _ _ hxy)
        (hrows _ _ hxy)]
  exact hinv x y hxy

/-- Full distinguished rows, including coordinates outside the domain, extend. -/
theorem completed_lift_extends (inside : W → Bool) (b q rows : W → W → Bool)
    (p : BasePerm W) (x : W) (hx : inside x = true)
    (hpx : inside (p.forward x) = true) :
    lift (completeRows inside b q rows) p (embed rows x) =
      embed rows (p.forward x) := by
  exact lift_extends_rows (completeRows inside b q rows) rows p x
    (completeRows_on_domain inside b q rows x hx)
    (completeRows_on_domain inside b q rows (p.forward x) hpx)

end GluingEPPA.Reducts.PairRowCompletion
