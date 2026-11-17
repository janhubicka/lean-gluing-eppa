import GluingEPPA.Steiner.ChainValuation.StateRelabelExtension
import GluingEPPA.Steiner.ChainValuation.WordAction

/-!
# Equivariance of full word actions on relabelled literal chain states

The checked state-relabelling interface reflects every genuine labelled
edge, so its canonical fixed-point completions commute with every renamed
generator. Induction on the length of a word gives conjugacy of the
whole opposite-order word action on actual chain spaces.
-/

namespace GluingEPPA.Steiner.ChainValuation.StateRelabel

universe u v
variable {E E' : Type u}

/-- An edge-reflecting state equivalence conjugates the complete action
of every word, with letters and their order unchanged except for renaming. -/
theorem wordPerm
    (p : E ≃ E')
    {A : GroupBlock.{u,v} E} {A' : GroupBlock.{u,v} E'}
    (F : A.Carrier ≃* A'.Carrier)
    {C : ChainState E A} {C' : ChainState E' A'}
    (R : StateRelabel p F C C')
    (w : List E) (x : C.Space) :
    R.space
        (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
          (fun e => (C.matching e).perm) w x) =
      EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (C'.matching e).perm) (w.map p) (R.space x) := by
  induction w generalizing x with
  | nil => rfl
  | cons e tail ih =>
      change
        R.space
          (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
            (fun e => (C.matching e).perm) tail
              ((C.matching e).perm x)) =
        EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
          (fun e => (C'.matching e).perm) (tail.map p)
            ((C'.matching (p e)).perm (R.space x))
      calc
        R.space
          (EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
            (fun e => (C.matching e).perm) tail
              ((C.matching e).perm x)) =
          EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
            (fun e => (C'.matching e).perm) (tail.map p)
              (R.space ((C.matching e).perm x)) := ih _
        _ = EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
              (fun e => (C'.matching e).perm) (tail.map p)
                ((C'.matching (p e)).perm (R.space x)) := by
          rw [completed_perm p F R e x]

end GluingEPPA.Steiner.ChainValuation.StateRelabel
