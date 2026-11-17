import GluingEPPA.Steiner.ChainValuation.ChainIndex
import Mathlib.Logic.Equiv.Basic

/-!
# Relabelling the finite indices of bounded separated-chain tests

The raw chain index is a positive length and a tuple of block atoms. An
equivalence on proper alphabets, together with an equivalence on each old
group carrier, induces a length-preserving equivalence of all raw chains.
Restricting that equivalence to the separated subtype requires only a
proof that the two separation predicates agree.

The geometric work of augmented naturality is to construct the induced
proper-stage maps from a diagram isomorphism and prove that they preserve
separation and conjugate the actual quotient matchings. This module proves
the independent finite-index part without assuming those geometric facts.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation

universe u
variable {E E' : Type u}
variable [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']
variable {S : Finset E} {T : Finset E'}
variable {old : ∀ i : Proper S, Data E i.val}
variable {old' : ∀ j : Proper T, Data E' j.val}

/-- Transport one block's proper alphabet and its old-group coordinate. -/
noncomputable def atomRelabel
    (P : Proper S ≃ Proper T)
    (F : ∀ i : Proper S, (old i).Carrier ≃ (old' (P i)).Carrier) :
    ChainAtom S old ≃ ChainAtom T old' :=
  Equiv.sigmaCongr P F

/-- Transport all block coordinates, retaining the same positive length and
bound N. This also transports the unused final shift in the raw index. -/
noncomputable def rawChainRelabel
    (N : Nat) (P : Proper S ≃ Proper T)
    (F : ∀ i : Proper S, (old i).Carrier ≃ (old' (P i)).Carrier) :
    RawChain N S old ≃ RawChain N T old' :=
  Equiv.sigmaCongrRight
    (fun r : ChainLength N =>
      Equiv.piCongrRight
        (fun _ : Fin r.val => atomRelabel P F))

/-- Every bounded chain is mapped to a bounded chain of exactly the same
number of blocks. -/
theorem rawChainRelabel_length
    (N : Nat) (P : Proper S ≃ Proper T)
    (F : ∀ i : Proper S, (old i).Carrier ≃ (old' (P i)).Carrier)
    (c : RawChain N S old) :
    ((rawChainRelabel N P F) c).1 = c.1 := rfl

/-- A relabelling respecting separation induces a bijection of the *literal*
finite test-index types, not just a map of isomorphism classes of chains. -/
noncomputable def filteredChainRelabel
    (N : Nat) (P : Proper S ≃ Proper T)
    (F : ∀ i : Proper S, (old i).Carrier ≃ (old' (P i)).Carrier)
    (Psrc : RawChain N S old → Prop)
    (Ptgt : RawChain N T old' → Prop)
    (hP : ∀ c, Psrc c ↔ Ptgt ((rawChainRelabel N P F) c)) :
    FilteredChains N S old Psrc ≃ FilteredChains N T old' Ptgt :=
  (rawChainRelabel N P F).subtypeEquiv hP

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation
