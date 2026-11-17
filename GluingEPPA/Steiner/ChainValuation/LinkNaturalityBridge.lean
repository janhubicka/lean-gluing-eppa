import GluingEPPA.Steiner.RecursiveLinks
import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Relabelling squares for actual inclusion and deletion Links

The two homomorphisms in any Link are determined by their values on named
generators. Under relabellings of their source and target groups, the
inclusion and deletion squares commute automatically. No separate
compatibility assumption about the chosen Link witnesses is needed.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

universe u
variable {V E V' E' : Type u}
variable (D : EdgeGraph V E) (D' : EdgeGraph V' E')
variable {M S : Finset E} {M' S' : Finset E'}
variable (A : Data E M) (B : Data E S)
variable (A' : Data E' M') (B' : Data E' S')
variable (L : Link D A B) (L' : Link D' A' B')
variable (p : E ≃ E')
variable (FM : A.Carrier ≃* A'.Carrier)
variable (FS : B.Carrier ≃* B'.Carrier)

/-- Every inclusion square commutes by generator extensionality. -/
theorem Link.relabel_inclusion
    (hM : ∀ e ∈ M, p e ∈ M')
    (hA : ∀ e ∈ M, FM (A.edge e) = A'.edge (p e))
    (hB : ∀ e ∈ M, FS (B.edge e) = B'.edge (p e)) :
    FS.toMonoidHom.comp L.incl = L'.incl.comp FM.toMonoidHom := by
  apply A.hom_ext
  intro e he
  change FS (L.incl (A.edge e)) = L'.incl (FM (A.edge e))
  calc
    FS (L.incl (A.edge e)) = FS (B.edge e) :=
      congrArg FS (L.incl_edge e he)
    _ = B'.edge (p e) := hB e he
    _ = L'.incl (A'.edge (p e)) :=
      (L'.incl_edge (p e) (hM e he)).symm
    _ = L'.incl (FM (A.edge e)) :=
      congrArg L'.incl (hA e he).symm

/-- Deletion squares also commute, including letters removed by the
smaller mask. -/
theorem Link.relabel_deletion
    (hM : ∀ e, p e ∈ M' ↔ e ∈ M)
    (hS : ∀ e ∈ S, p e ∈ S')
    (hA : ∀ e ∈ M, FM (A.edge e) = A'.edge (p e))
    (hB : ∀ e ∈ S, FS (B.edge e) = B'.edge (p e)) :
    FM.toMonoidHom.comp L.delete = L'.delete.comp FS.toMonoidHom := by
  apply B.hom_ext
  intro e he
  change FM (L.delete (B.edge e)) = L'.delete (FS (B.edge e))
  rw [L.delete_edge e he, hB e he,
    L'.delete_edge (p e) (hS e he)]
  by_cases hm : e ∈ M
  · rw [if_pos hm, if_pos ((hM e).2 hm), hA e hm]
  · have hm' : p e ∉ M' := fun h => hm ((hM e).1 h)
    rw [if_neg hm, if_neg hm', map_one]

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
