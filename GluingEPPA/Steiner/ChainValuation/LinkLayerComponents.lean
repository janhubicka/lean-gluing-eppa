import GluingEPPA.Steiner.ChainValuation.LinkRestrictedMatching
import GluingEPPA.Steiner.ChainValuation.LayerMatching

/-!
# The partial-matching path of restricted pieces for actual earlier Links

For a sequence of earlier blocks A_0,A_1,..., this applies the literal
two-group restricted attachment matching at each boundary. The resulting
combinatorial components have one piece per block and are classified by their
leftmost roots.

The remaining geometric restriction lemma must identify these components
with the actual M-components of the glued Cayley chain and provide its
equivariant test charts. No such identification is assumed here.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))
variable (M : Proper S)
variable (A : Nat → Proper S)
variable (h : ∀ n, (old (A n)).Carrier)

/-- Possible restricted-coset pieces at block n, represented as sets of
vertices of the actual earlier group K_(A_n). -/
abbrev restrictedPieceLayer (n : Nat) : Type u :=
  Set ((old (A n)).Carrier)

/-- The literal matching between restricted pieces of adjacent blocks. -/
noncomputable def restrictedBoundaryMatching (n : Nat) :
    ChainValuation.Matching
      (Sum (restrictedPieceLayer S old A n)
        (restrictedPieceLayer S old A (n + 1))) :=
  restrictedLinkMatching D S old L M (A n) (A (n + 1)) (h n)

/-- The path of such matchings, with no hypothetical ambient group K_S. -/
noncomputable def restrictedLayerSystem :
    ChainValuation.LayerMatch (restrictedPieceLayer S old A) :=
  ChainValuation.layerMatchOfMatchings
    (fun n => restrictedBoundaryMatching D S old L M A h n)

/-- Every combinatorial restricted component meets a given original block
in at most one piece, irrespective of the number of chain attachments. -/
theorem restrictedLayers_no_merge
    (n : Nat) (x y : restrictedPieceLayer S old A n)
    (hc : (restrictedLayerSystem D S old L M A h).Connected
      ⟨n, x⟩ ⟨n, y⟩) : x = y :=
  (restrictedLayerSystem D S old L M A h).connected_same_layer n x y hc

/-- Two restricted pieces are joined across a sequence of attachments
exactly when their canonical earliest roots agree. -/
theorem restrictedLayers_connected_iff_roots
    (x y : Sigma (restrictedPieceLayer S old A)) :
    (restrictedLayerSystem D S old L M A h).Connected x y ↔
    (restrictedLayerSystem D S old L M A h).root x.1 x.2 =
      (restrictedLayerSystem D S old L M A h).root y.1 y.2 :=
  (restrictedLayerSystem D S old L M A h).connected_iff_same_root x y

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
