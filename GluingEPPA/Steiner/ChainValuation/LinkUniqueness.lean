import GluingEPPA.Steiner.RecursiveLinks

/-!
# Earlier links are determined by their named generators

Both homomorphisms of a Link are fixed by their generator equations.
The remaining fields are propositions.  Thus selecting a link family
at one recursive stage cannot change the links used at a smaller stage.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord

universe u
variable {V E : Type u} (D : EdgeGraph V E)

theorem Link.eq_of_generator_rules {M S : Finset E}
    (A : Data E M) (B : Data E S) (P Q : Link D A B) : P = Q := by
  have hi : P.incl = Q.incl := A.hom_ext _ _
    (fun e he => (P.incl_edge e he).trans (Q.incl_edge e he).symm)
  have hd : P.delete = Q.delete := B.hom_ext _ _
    (fun e he => (P.delete_edge e he).trans (Q.delete_edge e he).symm)
  cases P
  cases Q
  cases hi
  cases hd
  rfl

instance linkSubsingleton {M S : Finset E} (A : Data E M) (B : Data E S) :
    Subsingleton (Link D A B) :=
  ⟨Link.eq_of_generator_rules D A B⟩

/-- All links between the proper predecessors of one stage. -/
abbrev EarlierLinks (S : Finset E) (old : ∀ i : Proper S, Data E i.val) :=
  ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t)

end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
