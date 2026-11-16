import GluingEPPA.Reducts.AnchorFamily
import GluingEPPA.Reducts.AnchorGroupDescent
import GluingEPPA.Reducts.AnchorGeometry
import GluingEPPA.Reducts.EqualityFreePullback

/-! General relative realization and interpreted-structure transfer.
Raw geometric existence is explicit. The output projection, action,
induced copies, geometry and class membership are not premises. -/
namespace GluingEPPA.Reducts.AnchorGeneralTheorem
open GluingEPPA.Reducts.AnchorExtraction
open GluingEPPA.Reducts.AnchorActions
open GluingEPPA.Reducts.AnchorGroupDescent
open GluingEPPA.Reducts.AnchorGeometry
open GluingEPPA.Reducts.EqualityFreePullback
noncomputable section
universe u
variable {A V Z J : Type u} {e : A ↪ V}
variable {L : Rel A → Prop} {H : Equiv.Perm V → Prop}
variable (S : System e L H Z J)

def CopySymmetry (p : Equiv.Perm Z) : Prop :=
  (∀ j, ∃ k, ∀ x, p (S.copy j x) = S.copy k x) ∧
  (∀ j, ∃ k, ∀ x, p.symm (S.copy j x) = S.copy k x)

/-- Incoming augmented-copy data supplied by the geometric theorem. -/
structure RawData : Prop where
  realizes : Realizes S
  extensions : ∀ r, Allowed e L H r → ∃ p : Equiv.Perm Z,
    CopySymmetry S p ∧ ∀ x y, r x y → p (S.copy S.root x) = S.copy S.root y
  transitive : ∀ j k, ∃ p : Equiv.Perm Z,
    CopySymmetry S p ∧ ∀ x, p (S.copy j x) = S.copy k x

variable [Nonempty V]
theorem pair_lift (raw : RawData S) (f : Rel A) (hf : L f)
    (h : Equiv.Perm V) (hh : H h) (hc : Compatible e f h) :
    ∃ g : Symmetry S,
      g.anchorAction = h ∧ ∀ a b, f a b →
        g.restrict (chart S S.root (root_retained S) a) = chart S S.root (root_retained S) b := by
  obtain ⟨p,hp,he⟩ := raw.extensions (decorated f h) (Or.inr ⟨f,hf,h,hh,hc,rfl⟩)
  have ha : ∀ v, p (S.copy S.root (.inr v)) = S.copy S.root (.inr (h v)) :=
    fun v => he (.inr v) (.inr (h v)) rfl
  have hr : ∀ a b, f a b → p (S.copy S.root (.inl a)) = S.copy S.root (.inl b) :=
    fun a b hab => he (.inl a) (.inl b) hab
  exact ⟨symmetryOfExtension S p hp.1 hp.2 h ha,
    supplied_anchor_action S p hp.1 hp.2 h ha,
    restricted_extension S p hp.1 hp.2 h ha f hr⟩

theorem intended_anchor_range (raw : RawData S) (hzero : L (emptyRel A))
    (h : Equiv.Perm V) : h ∈ (anchorHom S).range ↔ H h := by
  constructor
  · intro hh
    exact anchor_range_allowed S ⟨h,hh⟩
  · intro hh
    obtain ⟨p,hp,he⟩ := raw.extensions (decorated (emptyRel A) h)
      (Or.inr ⟨emptyRel A,hzero,h,hh,by intro a b hab; exact False.elim hab,rfl⟩)
    exact ambient_in_anchor_range S h p hp.1 hp.2 (fun v => he (.inr v) (.inr (h v)) rfl)

theorem extracted_transitive (raw : RawData S) (j k : J)
    (hj : retained S j) (hk : retained S k) :
    ∃ g : (realHom S).range, ∀ a, g.val (chart S j hj a) = chart S k hk a := by
  obtain ⟨p,hp,he⟩ := raw.transitive j k
  exact retained_transporter S j k hj hk p hp.1 hp.2 he

theorem extracted_cover (y : Real S) : ∃ j, ∃ hj : retained S j, ∃ a, chart S j hj a = y := by
  obtain ⟨⟨j,a⟩,hj,ha⟩ := y.property
  exact ⟨j,hj,a,Subtype.ext ha⟩

theorem general_relative_realization [Finite Z] (raw : RawData S)
    (hzero : L (emptyRel A)) (hinv : ∀ h, H h → H h.symm)
    (hlift : ∀ f, L f → ∃ h : Equiv.Perm V, H h ∧ Compatible e f h)
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, H h ∧ ∃ a : A, h (e a) = v)
    (n : Nat) (hconf : Conformal n (sourceEdges S)) (hchord : Chordal n (sourceEdges S)) :
    Finite (Real S) ∧ Function.Surjective (projection S) ∧
    (∀ a, projection S (chart S S.root (root_retained S) a) = e a) ∧
    (∀ y : Real S, ∃ j, ∃ hj : retained S j, ∃ a, chart S j hj a = y) ∧
    (∀ j k (hj : retained S j) (hk : retained S k),
      ∃ f, L f ∧ ∀ a b, chart S j hj a = chart S k hk b ↔ f a b) ∧
    (∀ f, L f → ∃ j, ∃ hj : retained S j, ∀ a b,
      chart S S.root (root_retained S) a = chart S j hj b ↔ f a b) ∧
    (∀ h, h ∈ (anchorHom S).range ↔ H h) ∧
    (∃ theta : (realHom S).range →* (anchorHom S).range,
      Function.Surjective theta ∧ ∀ g y, projection S (g.val y) = (theta g).val (projection S y)) ∧
    (∀ j k (hj : retained S j) (hk : retained S k),
      ∃ g : (realHom S).range, ∀ a, g.val (chart S j hj a) = chart S k hk a) ∧
    (∀ f, L f → ∀ h, H h → Compatible e f h → ∃ g : Symmetry S,
      g.anchorAction = h ∧ ∀ a b, f a b →
        g.restrict (chart S S.root (root_retained S) a) = chart S S.root (root_retained S) b) ∧
    Conformal n (extractedEdges S) ∧ Chordal n (extractedEdges S) := by
  have hs := projection_surjective S raw.realizes hzero hinv horbit
  refine ⟨extracted_finite S,hs,projection_root S,extracted_cover S,full_real_overlap S,?_,
    intended_anchor_range S raw hzero,?_,extracted_transitive S raw,pair_lift S raw,
    conformal_transfer S n hconf,chordal_transfer S n hchord⟩
  · intro f hf
    obtain ⟨h,hh,hc⟩ := hlift f hf
    exact every_real_overlap S raw.realizes f hf h hh hc
  · exact ⟨descent S hs,descent_surjective S hs,descended_equivariant S⟩

variable {R Q : Type u} {arity : R → Nat} {qarity : Q → Nat}
theorem interpreted_copy (M : Table arity V)
    (I : Interpretation (arity := arity) (qarity := qarity)) (B : Table qarity A)
    (hs : Function.Surjective (projection S))
    (he : Induces (interpret I M) B e)
    (hH : ∀ h : Equiv.Perm V, H h → Preserves (interpret I M) h)
    (j : J) (hj : retained S j) :
    Induces (interpret I (pullback M (projection S))) B (chart S j hj) := by
  obtain ⟨h,hh,ha,hp⟩ := chart_has_ambient_label S j hj
  rw [interpretation_pullback I M (projection S) hs]
  intro r t
  change interpret I M r (projection S ∘ (chart S j hj ∘ t)) ↔ B r t
  have ht : projection S ∘ (chart S j hj ∘ t) = h ∘ (e ∘ t) :=
    funext (fun i => hp (t i))
  rw [ht]
  exact (hH h hh r (e ∘ t)).trans (he r t)

theorem interpreted_group_action (M : Table arity V)
    (I : Interpretation (arity := arity) (qarity := qarity))
    (hs : Function.Surjective (projection S))
    (hH : ∀ h : Equiv.Perm V, H h → Preserves (interpret I M) h)
    (g : (realHom S).range) :
    Preserves (interpret I (pullback M (projection S))) g.val := by
  exact interpreted_action I M (projection S) hs g.val (descendedMap S g).val
    (descended_equivariant S g) (hH _ (anchor_range_allowed S (descendedMap S g)))

theorem general_interpreted_transfer [Finite Z] (raw : RawData S)
    (hzero : L (emptyRel A)) (hinv : ∀ h, H h → H h.symm)
    (horbit : ∀ v : V, ∃ h : Equiv.Perm V, H h ∧ ∃ a : A, h (e a) = v)
    (T : Theory (arity := arity)) (M : Table arity V) (hM : Models M T)
    (I : Interpretation (arity := arity) (qarity := qarity)) (B : Table qarity A)
    (he : Induces (interpret I M) B e)
    (hH : ∀ h : Equiv.Perm V, H h → Preserves (interpret I M) h) :
    ∃ N : Table arity (Real S), Models N T ∧
      interpret I N = pullback (interpret I M) (projection S) ∧
      (∀ j (hj : retained S j), Induces (interpret I N) B (chart S j hj)) ∧
      (∀ g : (realHom S).range, Preserves (interpret I N) g.val) := by
  have hs := projection_surjective S raw.realizes hzero hinv horbit
  exact ⟨pullback M (projection S), (models_pullback M (projection S) hs T).2 hM,
    interpretation_pullback I M (projection S) hs,
    interpreted_copy S M I B hs he hH, interpreted_group_action S M I hs hH⟩
end
end GluingEPPA.Reducts.AnchorGeneralTheorem
