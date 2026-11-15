import GluingEPPA.Reducts.AnchorExtraction

/-! n-conformality and n-chordality transfer with no loss of local parameter.
No geometry on the extracted points is assumed. -/
namespace GluingEPPA.Reducts.AnchorGeometry
open GluingEPPA.Reducts.AnchorExtraction
universe u
variable {X C : Type u}
def Adjacent (E : C → X → Prop) (x y : X) : Prop :=
  x ≠ y ∧ ∃ c, E c x ∧ E c y
def Conformal (n : Nat) (E : C → X → Prop) : Prop :=
  ∀ k : Nat, 0 < k → k ≤ n → ∀ v : Fin k → X, Function.Injective v →
    (∀ i j, i ≠ j → Adjacent E (v i) (v j)) → ∃ c, ∀ i, E c (v i)
def Neighbors {k : Nat} (i j : Fin k) : Prop :=
  (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val
def Chordal (n : Nat) (E : C → X → Prop) : Prop :=
  ∀ k : Nat, 4 ≤ k → k ≤ n → ∀ v : Fin k → X, Function.Injective v →
    (∀ i j, i ≠ j → (Adjacent E (v i) (v j) ↔ Neighbors i j)) → False
variable {A V Z J : Type u} {e : A ↪ V}
variable {L : Rel A → Prop} {H : Equiv.Perm V → Prop}
variable (S : System e L H Z J)
abbrev Retained := {j : J // retained S j}
def sourceEdges (j : J) (z : Z) : Prop := ∃ x, S.copy j x = z
def extractedEdges (c : Retained S) (y : Real S) : Prop :=
  ∃ a, chart S c.val c.property a = y

theorem incidence_iff (j : J) (hj : retained S j) (y : Real S) :
    sourceEdges S j y.val ↔ extractedEdges S ⟨j,hj⟩ y := by
  change (∃ x, S.copy j x = y.val) ↔ ∃ a, chart S j hj a = y
  rw [trace_restriction S j hj y]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Subtype.ext ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,congrArg Subtype.val ha⟩

theorem adjacent_iff (x y : Real S) :
    Adjacent (extractedEdges S) x y ↔ Adjacent (sourceEdges S) x.val y.val := by
  constructor
  · rintro ⟨hne,c,hx,hy⟩
    exact ⟨fun h => hne (Subtype.ext h), c.val,
      (incidence_iff S c.val c.property x).2 hx,
      (incidence_iff S c.val c.property y).2 hy⟩
  · rintro ⟨hne,j,hx,hy⟩
    obtain ⟨a,ha⟩ := hx
    have hj := chart_meeting_carrier_retained S j a x ha
    exact ⟨fun h => hne (congrArg Subtype.val h), ⟨j,hj⟩,
      (incidence_iff S j hj x).1 ⟨a,ha⟩,
      (incidence_iff S j hj y).1 hy⟩

theorem conformal_transfer (n : Nat) (hc : Conformal n (sourceEdges S)) :
    Conformal n (extractedEdges S) := by
  intro k hk hkn v hv hcl
  have hvz : Function.Injective (fun i => (v i).val) :=
    fun i j hij => hv (Subtype.ext hij)
  obtain ⟨j,hj⟩ := hc k hk hkn (fun i => (v i).val) hvz
    (fun i l hil => (adjacent_iff S (v i) (v l)).1 (hcl i l hil))
  obtain ⟨x,hx⟩ := hj ⟨0,hk⟩
  have hr := chart_meeting_carrier_retained S j x (v ⟨0,hk⟩) hx
  exact ⟨⟨j,hr⟩,fun i => (incidence_iff S j hr (v i)).1 (hj i)⟩

theorem chordal_transfer (n : Nat) (hc : Chordal n (sourceEdges S)) :
    Chordal n (extractedEdges S) := by
  intro k hk hkn v hv hcycle
  exact hc k hk hkn (fun i => (v i).val)
    (fun i j hij => hv (Subtype.ext hij))
    (fun i j hij => (adjacent_iff S (v i) (v j)).symm.trans (hcycle i j hij))

theorem same_local_parameter (n : Nat)
    (hconf : Conformal n (sourceEdges S)) (hchord : Chordal n (sourceEdges S)) :
    Conformal n (extractedEdges S) ∧ Chordal n (extractedEdges S) :=
  ⟨conformal_transfer S n hconf, chordal_transfer S n hchord⟩
end GluingEPPA.Reducts.AnchorGeometry
