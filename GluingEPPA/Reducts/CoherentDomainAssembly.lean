import GluingEPPA.Reducts.FixedCarrierTransport

/-!
Matching-domain assembly on one connected component of the domain groupoid.
The inputs are local automorphism extensions and individual transports in one
fixed carrier. Only local admissible automorphisms are assumed to lift
homomorphically; coherence for arrows between different domains is proved.
Constructing these inputs for all induced substructures remains separate.
-/
namespace GluingEPPA.Reducts.CoherentDomainAssembly
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.FixedCarrierTransport
universe u v w
variable {O : Type u} {C : O → Type v} {R : Type v} {V : Type w}

/-- Express an arrow in the coordinates of the chosen representative. -/
def normalize (t : ∀ o, Atlas R (C o)) {i j : O} (p : Atlas (C i) (C j)) :
    BasePerm R where
  forward x := (t j).backward (p.forward ((t i).forward x))
  backward x := (t i).backward (p.backward ((t j).forward x))
  left_inv := by intro x; rw [(t j).right_inv, p.left_inv, (t i).left_inv]
  right_inv := by intro x; rw [(t i).right_inv, p.right_inv, (t j).left_inv]

theorem normalize_identity (t : ∀ o, Atlas R (C o)) (i : O) :
    normalize t (Atlas.identity (C i)) = BasePerm.identity R := by
  apply basePerm_ext
  intro x
  exact (t i).left_inv x

theorem normalize_comp (t : ∀ o, Atlas R (C o)) {i j k : O}
    (q : Atlas (C j) (C k)) (p : Atlas (C i) (C j)) :
    normalize t (q.comp p) = (normalize t q).comp (normalize t p) := by
  apply basePerm_ext
  intro x
  change (t k).backward (q.forward (p.forward ((t i).forward x))) =
    (t k).backward (q.forward ((t j).forward
      ((t j).backward (p.forward ((t i).forward x)))))
  rw [(t j).right_inv]

def assemble (t : ∀ o, Atlas R (C o)) (U : O → BasePerm V)
    (L : BasePerm R → BasePerm V) {i j : O} (p : Atlas (C i) (C j)) : BasePerm V :=
  (U j).comp ((L (normalize t p)).comp (U i).inverse)

theorem assemble_identity (t : ∀ o, Atlas R (C o)) (U : O → BasePerm V)
    (L : BasePerm R → BasePerm V) (hL : L (BasePerm.identity R) = BasePerm.identity V)
    (i : O) : assemble t U L (Atlas.identity (C i)) = BasePerm.identity V := by
  apply basePerm_ext
  intro x
  change (U i).forward ((L (normalize t (Atlas.identity (C i)))).forward
    ((U i).backward x)) = x
  rw [normalize_identity, hL]
  exact (U i).right_inv x

/-- No composition law for arrows between different objects is an input. -/
theorem assemble_comp (t : ∀ o, Atlas R (C o)) (U : O → BasePerm V)
    (L : BasePerm R → BasePerm V) (allowed : BasePerm R → Prop)
    (hL : ∀ f g, allowed f → allowed g → L (g.comp f) = (L g).comp (L f))
    {i j k : O} (q : Atlas (C j) (C k)) (p : Atlas (C i) (C j))
    (hp : allowed (normalize t p)) (hq : allowed (normalize t q)) :
    assemble t U L (q.comp p) = (assemble t U L q).comp (assemble t U L p) := by
  apply basePerm_ext
  intro x
  change (U k).forward ((L (normalize t (q.comp p))).forward ((U i).backward x)) =
    (U k).forward ((L (normalize t q)).forward ((U j).backward
      ((U j).forward ((L (normalize t p)).forward ((U i).backward x)))))
  rw [normalize_comp, hL _ _ hp hq, (U j).left_inv]
  rfl

theorem inverse_transport_on_input (t : ∀ o, Atlas R (C o)) (U : O → BasePerm V)
    (e0 : R → V) (e : ∀ o, C o → V)
    (hU : ∀ o r, (U o).forward (e0 r) = e o ((t o).forward r))
    (i : O) (x : C i) : (U i).backward (e i x) = e0 ((t i).backward x) := by
  have h := hU i ((t i).backward x)
  rw [(t i).right_inv] at h
  rw [← h, (U i).left_inv]

theorem assemble_extends (t : ∀ o, Atlas R (C o)) (U : O → BasePerm V)
    (L : BasePerm R → BasePerm V) (allowed : BasePerm R → Prop)
    (e0 : R → V) (e : ∀ o, C o → V)
    (hU : ∀ o r, (U o).forward (e0 r) = e o ((t o).forward r))
    (hL : ∀ f, allowed f → ∀ r, (L f).forward (e0 r) = e0 (f.forward r))
    {i j : O} (p : Atlas (C i) (C j)) (hp : allowed (normalize t p)) (x : C i) :
    (assemble t U L p).forward (e i x) = e j (p.forward x) := by
  change (U j).forward ((L (normalize t p)).forward ((U i).backward (e i x))) = _
  rw [inverse_transport_on_input t U e0 e hU i x, hL _ hp, hU]
  change e j ((t j).forward ((t j).backward
    (p.forward ((t i).forward ((t i).backward x))))) = e j (p.forward x)
  rw [(t i).right_inv, (t j).right_inv]

/-- The assembled maps preserve the actual witness relation when their local
and transport constituents do; no new completion is assumed. -/
theorem assemble_preserves_relation (t : ∀ o, Atlas R (C o)) (U : O → BasePerm V)
    (L : BasePerm R → BasePerm V) (allowed : BasePerm R → Prop)
    (rel : V → V → Prop)
    (hU : ∀ o x y, rel ((U o).forward x) ((U o).forward y) ↔ rel x y)
    (hL : ∀ f, allowed f → ∀ x y, rel ((L f).forward x) ((L f).forward y) ↔ rel x y)
    {i j : O} (p : Atlas (C i) (C j)) (hp : allowed (normalize t p)) (x y : V) :
    rel ((assemble t U L p).forward x) ((assemble t U L p).forward y) ↔ rel x y := by
  change rel ((U j).forward ((L (normalize t p)).forward ((U i).backward x)))
    ((U j).forward ((L (normalize t p)).forward ((U i).backward y))) ↔ rel x y
  rw [hU, hL _ hp]
  have h := hU i ((U i).backward x) ((U i).backward y)
  rw [(U i).right_inv, (U i).right_inv] at h
  exact h.symm

end GluingEPPA.Reducts.CoherentDomainAssembly
