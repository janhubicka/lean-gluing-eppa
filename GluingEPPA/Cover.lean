import GluingEPPA.Parity
import GluingEPPA.Replay

namespace GluingEPPA
universe u v w z t
namespace EdgeGraph
variable {V : Type u} {E : Type v} {A : Type w} {U : Type z}
variable (G : EdgeGraph V E) [DecidableEq E] (D : System V A)

/-- Lift the point-transport relation to the Boolean cover. -/
def cover : System (V × Valuation (E := E)) A where
  step p q := G.LiftEdge p.1 q.1 ∧ D.step (p.1.1, p.2) (q.1.1, q.2)
  reverse h := ⟨G.liftEdge_symm h.1, D.reverse h.2⟩

theorem project_point_path {p q} (h : (G.cover D).Connected p q) :
    D.Connected (p.1.1, p.2) (q.1.1, q.2) := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail e.2

theorem project_lift_path {p q} (h : (G.cover D).Connected p q) :
    Relation.ReflTransGen G.LiftEdge p.1 q.1 := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail e.1

def coverFrame (F : D.Frame U) : (G.cover D).Frame U where
  value p x := F.value p.1 x
  injective p := F.injective p.1
  commute h := F.commute h.2

/-- A base edge is available to a transported point in the specified direction. -/
def PointAvailable (start : V × A) (b c : V) : Prop :=
  ∃ y z, D.Connected start (b, y) ∧ D.step (b, y) (c, z)

/-- A changed valuation coordinate witnesses a traversal of that edge.
The point can use that edge in either direction, by reversing the traversal. -/
theorem changed_available {p q} (h : (G.cover D).Connected p q) (e : E)
    (hne : p.1.2 e ≠ q.1.2 e) :
    PointAvailable D (p.1.1, p.2) (G.left e) (G.right e) ∧
    PointAvailable D (p.1.1, p.2) (G.right e) (G.left e) := by
  revert hne
  induction h with
  | refl => intro hne; exact False.elim (hne rfl)
  | @tail q r h step ih =>
    intro hne
    by_cases before : p.1.2 e ≠ q.1.2 e
    · exact ih before
    · have same : p.1.2 e = q.1.2 e := not_not.mp before
      obtain ⟨d, inc, value⟩ := step.1
      have de : d = e := by
        by_contra hd
        apply hne
        calc
          p.1.2 e = q.1.2 e := same
          _ = r.1.2 e := by rw [value]; simp [flip, Ne.symm hd]
      subst d
      have prefix := G.project_point_path D h
      have transport := step.2
      have both :
          PointAvailable D (p.1.1, p.2) q.1.1 r.1.1 ∧
          PointAvailable D (p.1.1, p.2) r.1.1 q.1.1 :=
        ⟨⟨q.2, r.2, prefix, transport⟩,
         ⟨r.2, q.2, prefix.tail transport, D.reverse transport⟩⟩
      rcases inc with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · simpa only [hl, hr] using both
      · simpa only [hl, hr] using And.intro both.2 both.1

variable [Fintype E] {L : Nat → Type t}

/-- The Boolean cover of a faithful point-transport frame has an induced
free relational realization. No realization or EPPA conclusion is assumed. -/
theorem cover_compatible (S : RelStructure L A) (F : D.Frame U)
    (respect : D.RespectsRelations S) : (G.cover D).Compatible S := by
  refine ⟨(G.coverFrame D F).copy_injective, ?_⟩
  intro n r p q x y ends
  cases n with
  | zero =>
    have heq : x = y := funext (fun i => Fin.elim0 i)
    rw [heq]
  | succ n =>
    have common := G.support_reachable
      (G.project_lift_path D (ends ⟨0, Nat.zero_lt_succ n⟩))
    have walk : Relation.ReflTransGen (D.Available p.1 x) p.1 q.1 := by
      induction common with
      | refl => exact .refl
      | @tail b c common edge ih =>
        refine ih.tail ?_
        intro i
        obtain ⟨e, changed, inc⟩ := edge
        have available := G.changed_available D (ends i) e changed
        rcases inc with ⟨hl, hr⟩ | ⟨hr, hl⟩
        · simpa only [hl, hr] using available.1
        · simpa only [hl, hr] using available.2
    exact D.replay S F r p.1 q.1 x y respect walk
      (fun i => G.project_point_path D (ends i))

/-- The canonical copies in the finite construction are induced embeddings. -/
def coverEmbedding (S : RelStructure L A) (F : D.Frame U)
    (respect : D.RespectsRelations S) (p : V × Valuation (E := E)) :
    Embedding S ((G.cover D).quotientStructure S) :=
  (G.cover D).embedding S (G.cover_compatible D S F respect) p

instance finite_realization [Finite V] [Finite A] : Finite (G.cover D).Realization :=
  inferInstance
end EdgeGraph
end GluingEPPA
