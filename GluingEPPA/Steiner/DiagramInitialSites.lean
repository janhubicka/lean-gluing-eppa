import GluingEPPA.Steiner.DiagramOrderedTotalCompletion

/-!
# The finite vertices of the Steiner EPPA gluing diagram

A vertex of the initial diagram is a **labelled closed subsystem**:
its point set and its triples. It is NOT an indexed pair (permutation,
closed subset). Different pairs representing the same labelled system
must give the same vertex; labelled systems with distinct triples must
remain different vertices even if their point sets coincide.

Here the vertex is represented by exactly those two predicates.
A membership certificate says that it is a relabelling of an induced
closed subsystem of the original finite Steiner system. This is the
vertex set used in Section 6 of the manuscript.
-/

namespace GluingEPPA.Steiner.InitialSites

universe u
variable {A : Type u}

/-- The labelled points and ordered triples of a local system. -/
structure SiteData (A : Type u) where
  points : Set A
  triple : A → A → A → Prop

/-- Relabel all points and triples by the same permutation. -/
def SiteData.relabel (σ : Equiv.Perm A) (s : SiteData A) : SiteData A where
  points := fun x => s.points (σ.symm x)
  triple := fun x y z =>
    s.triple (σ.symm x) (σ.symm y) (σ.symm z)

@[simp] theorem SiteData.relabel_refl (s : SiteData A) :
    SiteData.relabel (Equiv.refl A) s = s := by
  cases s
  rfl

theorem SiteData.relabel_trans (s : SiteData A)
    (σ τ : Equiv.Perm A) :
    SiteData.relabel τ (SiteData.relabel σ s) =
      SiteData.relabel (σ.trans τ) s := by
  rfl

/-- A subset is closed when any triple containing two of its points
has its third point there as well. -/
def Closed (R : A → A → A → Prop) (U : Set A) : Prop :=
  ∀ x y z, R x y z → U x → U y → U z

/-- The induced local system on a subset of the input. -/
def induced (R : A → A → A → Prop) (U : Set A) : SiteData A where
  points := U
  triple := fun x y z => R x y z ∧ U x ∧ U y ∧ U z

/-- Vertices are identified whenever their point sets and triples
coincide; the witnesses are not part of their identity. -/
def Site (R : A → A → A → Prop) :=
  {s : SiteData A // ∃ (σ : Equiv.Perm A) (U : Set A),
      Closed R U ∧ s = SiteData.relabel σ (induced R U)}

/-- An explicitly relabelled closed subsystem is a vertex. -/
def siteOf (R : A → A → A → Prop) (U : Set A)
    (hU : Closed R U) (σ : Equiv.Perm A) : Site R :=
  ⟨SiteData.relabel σ (induced R U), ⟨σ, U, hU, rfl⟩⟩

/-- Relabelling a vertex preserves membership in the vertex set. -/
def Site.relabel (R : A → A → A → Prop) (σ : Equiv.Perm A)
    (s : Site R) : Site R :=
  ⟨SiteData.relabel σ s.val, by
    obtain ⟨τ, U, hU, hs⟩ := s.property
    refine ⟨τ.trans σ, U, hU, ?_⟩
    rw [hs, SiteData.relabel_trans]⟩

/-- Relabelling depends on the labelled subsystem, not on its witness. -/
theorem siteOf_relabel (R : A → A → A → Prop) (U : Set A)
    (hU : Closed R U) (σ τ : Equiv.Perm A) :
    Site.relabel R τ (siteOf R U hU σ) =
      siteOf R U hU (σ.trans τ) := by
  apply Subtype.ext
  change SiteData.relabel τ (SiteData.relabel σ (induced R U)) =
    SiteData.relabel (σ.trans τ) (induced R U)
  exact SiteData.relabel_trans _ σ τ

@[simp] theorem Site.relabel_refl (R : A → A → A → Prop) (s : Site R) :
    Site.relabel R (Equiv.refl A) s = s := by
  apply Subtype.ext
  change SiteData.relabel (Equiv.refl A) s.val = s.val
  exact SiteData.relabel_refl s.val

theorem Site.relabel_trans (R : A → A → A → Prop)
    (σ τ : Equiv.Perm A) (s : Site R) :
    Site.relabel R τ (Site.relabel R σ s) =
      Site.relabel R (σ.trans τ) s := by
  apply Subtype.ext
  change SiteData.relabel τ (SiteData.relabel σ s.val) =
    SiteData.relabel (σ.trans τ) s.val
  exact SiteData.relabel_trans s.val σ τ

/-- The action on labelled subsystems is a genuine permutation. -/
def Site.relabelEquiv (R : A → A → A → Prop)
    (σ : Equiv.Perm A) : Equiv.Perm (Site R) where
  toFun := Site.relabel R σ
  invFun := Site.relabel R σ.symm
  left_inv s := by
    rw [Site.relabel_trans]
    simpa using Site.relabel_refl R s
  right_inv s := by
    rw [Site.relabel_trans]
    simpa using Site.relabel_refl R s

/-- The ambient finite set provides only finitely many possible
point sets and triple relations, hence finitely many vertices. -/
instance siteData_finite [Finite A] : Finite (SiteData A) := by
  classical
  apply Finite.of_injective (fun s : SiteData A => (s.points, s.triple))
  intro s t h
  cases s with
  | mk ps ts =>
    cases t with
    | mk pt tt =>
      have hps : ps = pt := congrArg Prod.fst h
      have hts : ts = tt := congrArg Prod.snd h
      cases hps
      cases hts
      rfl

instance site_finite [Finite A] (R : A → A → A → Prop) : Finite (Site R) :=
  Finite.of_injective Subtype.val Subtype.val_injective

end GluingEPPA.Steiner.InitialSites
