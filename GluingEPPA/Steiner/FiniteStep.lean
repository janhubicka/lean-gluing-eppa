import GluingEPPA.Steiner.FiniteFamily

/-!
# Correctness of the finite-subset construction step

Only edges of the current subset generate the new group. The old coordinates
are supplied by the checked crossing-restriction construction. All new maps
are then constructed, and actual walk replacement is proved for this group.
-/

namespace GluingEPPA.Steiner

namespace EdgeGraph.WalkValue

universe u v w z
variable {V : Type u} {E : Type v} {G : Type w} {H : Type z}
variable [Group G] [Group H] {D : EdgeGraph V E}

/-- A generator-compatible homomorphism carries actual smaller walks to
actual larger walks; no equality of the generators outside the mask is needed. -/
theorem mapOn {R S : Set E} {a : E → G} {b : E → H}
    (f : G →* H) (hRS : R ⊆ S) (hab : ∀ e ∈ R, f (a e) = b e)
    {u v : V} {g : G} (p : D.WalkValue R a u v g) :
    D.WalkValue S b u v (f g) := by
  induction p with
  | nil => simpa only [map_one] using WalkValue.nil (D := D) (S := S) (a := b) _
  | @cons u v w e g he hj p ih =>
      simpa only [map_mul, hab e he] using WalkValue.cons (hRS he) hj ih

end EdgeGraph.WalkValue

namespace FiniteFamily

universe u
variable {V E : Type u} [Fintype E] [DecidableEq E] [Finite V]
attribute [local instance] Classical.propDecidable

/-- The inductive properties, relative to the already fixed smaller groups.
The current group and smaller groups are data, not existential replacements. -/
structure Correct (D : EdgeGraph V E) (S : Finset E) (d : Data E S)
    (old : ∀ R : Proper S, Data E R.val) where
  inc : ∀ r, (old r).Carrier →* d.Carrier
  inc_edge : ∀ r e, e ∈ r.val → inc r ((old r).edge e) = d.edge e
  ret : ∀ r, d.Carrier →* (old r).Carrier
  ret_edge : ∀ r e, e ∈ S →
    ret r (d.edge e) = if e ∈ r.val then (old r).edge e else 1
  left_inverse : ∀ r, Function.LeftInverse (ret r) (inc r)
  replacement : ∀ r (u v : V) (g : (old r).Carrier),
    D.WalkValue (↑S : Set E) d.edge u v (inc r g) →
    D.WalkValue (↑r.val : Set E) (old r).edge u v g
  action : ∀ r, d.Carrier →* Equiv.Perm ((old r).transport D).Space
  action_edge : ∀ r e, e ∈ S →
    action r (d.edge e) =
      ((old r).transport D).edgePerm D (↑r.val : Set E) (old r).edge e

namespace Step

variable (D : EdgeGraph V E) (S : Finset E) (old : ∀ R : Proper S, Data E R.val)
variable (C : RecursiveStep.CompatibleCoordinates
  (Groups S old) (transports D S old) (masks S) (edges S old) D)

def edgeInclusion (r : Proper S) (e : r.val) : S :=
  ⟨e.val, (Finset.ssubset_iff_subset_ne.mp r.property).1 e.property⟩

noncomputable def ambientMap (r : Proper S) : (old r).Carrier →* Ambient D S old :=
  RecursiveStep.coordinateHom (Groups S old) (transports D S old)
    (C.groups r) (C.actions r)

theorem ambientMap_edge (r : Proper S) (e : r.val) :
    ambientMap D S old C r ((old r).edge e.val) = value D S old e.val := by
  exact RecursiveStep.coordinateHom_generator (Groups S old) (transports D S old)
    (C.groups r) (C.actions r) (masks S) (edges S old) D
    (fun e : r.val => (old r).edge e.val) (fun e : r.val => e.val)
    (fun e t => C.groups_on r e t) (fun e t => C.actions_on r e t) e

noncomputable def inc (r : Proper S) : (old r).Carrier →* Group D S old :=
  GeneratedStep.inclusion
    (fun e : S => value D S old e.val)
    (fun e : S => value_involutive D S old e.val)
    (fun e : r.val => (old r).edge e.val) (edgeInclusion S r)
    (old r).generated (ambientMap D S old C r) (ambientMap_edge D S old C r)

noncomputable def ret (r : Proper S) : Group D S old →* (old r).Carrier :=
  GeneratedStep.coordinate
    (fun e : S => value D S old e.val)
    (fun e : S => value_involutive D S old e.val)
    (RecursiveStep.groupProjection (Groups S old) (transports D S old) r)

noncomputable def action (r : Proper S) :
    Group D S old →* Equiv.Perm ((old r).transport D).Space :=
  GeneratedStep.coordinate
    (fun e : S => value D S old e.val)
    (fun e : S => value_involutive D S old e.val)
    (RecursiveStep.actionProjection (Groups S old) (transports D S old) r)

theorem inc_edge (r : Proper S) (e : E) (he : e ∈ r.val) :
    inc D S old C r ((old r).edge e) = edge D S old e := by
  have hs : e ∈ S := (Finset.ssubset_iff_subset_ne.mp r.property).1 he
  rw [edge_of_mem D S old e hs]
  apply Subtype.ext
  exact ambientMap_edge D S old C r ⟨e, he⟩

theorem ret_edge (r : Proper S) (e : E) (he : e ∈ S) :
    ret D S old r (edge D S old e) = if e ∈ r.val then (old r).edge e else 1 := by
  rw [edge_of_mem D S old e he]
  rfl

theorem action_edge (r : Proper S) (e : E) (he : e ∈ S) :
    action D S old r (edge D S old e) =
      ((old r).transport D).edgePerm D (↑r.val : Set E) (old r).edge e := by
  rw [edge_of_mem D S old e he]
  rfl

theorem left_inverse (r : Proper S) :
    Function.LeftInverse (ret D S old r) (inc D S old C r) := by
  have h : (ret D S old r).comp (inc D S old C r) = MonoidHom.id _ := by
    apply hom_ext_of_words (fun e : r.val => (old r).edge e.val) (old r).generated
    intro e
    change ret D S old r (inc D S old C r ((old r).edge e.val)) = (old r).edge e.val
    rw [inc_edge D S old C r e.val e.property,
      ret_edge D S old r e.val ((Finset.ssubset_iff_subset_ne.mp r.property).1 e.property)]
    simp only [ite_eq_left e.property]
  intro g
  exact DFunLike.congr_fun h g

theorem action_inc (r : Proper S) (g : (old r).Carrier) :
    action D S old r (inc D S old C r g) = ((old r).transport D).action g := by
  have h : (action D S old r).comp (inc D S old C r) =
      ((old r).transport D).action := by
    apply hom_ext_of_words (fun e : r.val => (old r).edge e.val) (old r).generated
    intro e
    change action D S old r (inc D S old C r ((old r).edge e.val)) =
      ((old r).transport D).action ((old r).edge e.val)
    rw [inc_edge D S old C r e.val e.property,
      action_edge D S old r e.val ((Finset.ssubset_iff_subset_ne.mp r.property).1 e.property)]
    simp only [Transport.edgePerm, ite_eq_left e.property]
  exact DFunLike.congr_fun h g

theorem replacement (r : Proper S) (u v : V) (g : (old r).Carrier)
    (p : D.WalkValue (↑S : Set E) (edge D S old) u v (inc D S old C r g)) :
    D.WalkValue (↑r.val : Set E) (old r).edge u v g := by
  apply ((old r).transport D).replacement_of_coordinate D (↑S : Set E)
    (edge D S old) (fun e _ => edge_involutive D S old e)
    (inc D S old C r) (action D S old r) (action_inc D S old C r) ?_ p rfl
  intro e he u v hj
  rw [action_edge D S old r e he]
  apply ((old r).transport D).edgePerm_endpoint D (↑r.val : Set E) (old r).edge
    (fun e _ => (old r).involutive e) ?_ hj
  intro e he u v hj
  exact EdgeGraph.WalkValue.single he hj

/-- All inductive properties of the actual current group follow from the
compatible old coordinates. The separate regular coordinates prove injectivity. -/
noncomputable def correct : Correct D S (data D S old) old where
  inc := inc D S old C
  inc_edge := inc_edge D S old C
  ret := ret D S old
  ret_edge := ret_edge D S old
  left_inverse := left_inverse D S old C
  replacement := replacement D S old C
  action := action D S old
  action_edge := action_edge D S old

end Step
end FiniteFamily
end GluingEPPA.Steiner
