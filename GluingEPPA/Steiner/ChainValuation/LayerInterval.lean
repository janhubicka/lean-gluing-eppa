import GluingEPPA.Steiner.ChainValuation.LayerMatch

/-!
# The support of a component of a line of partial matchings is an interval

Restricted coset pieces in a separated chain form partial matchings
between consecutive blocks. An abstract component already has at most
one piece in each layer (LayerMatch.connected_same_layer).
Here we prove that it occupies every *intermediate* layer between
any two of its members. This identifies the exact interval-support
property without making assumptions about the Cayley block groups.

Identifying these abstract pieces with genuine M-word components of
the final chain, and normalizing their gluing charts, remain separate.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u
variable {V : Nat → Type u}
variable (P : LayerMatch V)

/-- Starting at a vertex, every level from its earliest root up to
its own level contains a unique predecessor connected to it. -/
theorem LayerMatch.exists_intermediate_root
    (n : Nat) (x : V n) (k : Nat)
    (hroot : (P.root n x).1 ≤ k) (hkn : k ≤ n) :
    ∃ z : V k, P.Connected ⟨k, z⟩ ⟨n, x⟩ := by
  induction n generalizing x k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact ⟨x, LayerMatch.Connected.refl _⟩
  | succ n ih =>
      by_cases hk : k = n + 1
      · subst k
        exact ⟨x, LayerMatch.Connected.refl _⟩
      have hkle : k ≤ n := by omega
      cases hb : P.backward n x with
      | none =>
          have hroot' : (P.root (n + 1) x).1 = n + 1 := by
            simp [LayerMatch.root, hb]
          omega
      | some y =>
          have hroot' : P.root (n + 1) x = P.root n y := by
            simp [LayerMatch.root, hb]
          have hlow : (P.root n y).1 ≤ k := by
            rw [← hroot']
            exact hroot
          obtain ⟨z, hz⟩ := ih y k hlow hkle
          refine ⟨z, ?_⟩
          exact LayerMatch.Connected.trans hz
            (LayerMatch.Connected.forward n y x
              ((P.inverse_iff n y x).2 hb))

/-- A connected component of a path of partial matchings contains an
actual vertex at every intermediate layer; these vertices are
connected to both endpoints. Thus its set of support layers is an
interval, not an arbitrary subset of the line. -/
theorem LayerMatch.connected_intermediate
    {n m : Nat} (x : V n) (y : V m)
    (hxy : P.Connected ⟨n, x⟩ ⟨m, y⟩)
    (k : Nat) (hnk : n ≤ k) (hkm : k ≤ m) :
    ∃ z : V k,
      P.Connected ⟨n, x⟩ ⟨k, z⟩ ∧
      P.Connected ⟨k, z⟩ ⟨m, y⟩ := by
  have hroot : P.root n x = P.root m y :=
    P.root_of_connected hxy
  have hlower : (P.root m y).1 ≤ k := by
    rw [← hroot]
    exact (P.root_le n x).trans hnk
  obtain ⟨z, hz⟩ := P.exists_intermediate_root m y k hlower hkm
  have hroot_z : P.root n x = P.root k z := by
    have hzr : P.root k z = P.root m y :=
      P.root_of_connected hz
    exact hroot.trans hzr.symm
  refine ⟨z, ?_, hz⟩
  exact (P.connected_iff_same_root ⟨n, x⟩ ⟨k, z⟩).2 hroot_z

end GluingEPPA.Steiner.ChainValuation
