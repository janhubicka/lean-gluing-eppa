import GluingEPPA.Steiner.CayleyIsomorphism

/-! Elementary homomorphisms from allowed word representations.
Preservation of word equalities is an explicit premise, supplied for the
literal records by the next module. No group-existence theorem is used. -/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.Data
universe u
variable {E E' H : Type u} {S : Finset E} {T : Finset E'}
variable (A : Data E S) [Group H] (t : E → H)

noncomputable def wordMap (g : A.Carrier) : H :=
  ((Classical.choose (A.generated g)).map t).prod

variable (hker : ∀ p q : List E,
  (∀ e ∈ p, e ∈ S) → (∀ e ∈ q, e ∈ S) →
  (p.map A.edge).prod = (q.map A.edge).prod →
  (p.map t).prod = (q.map t).prod)

include hker in
/-- Evaluation is independent of the chosen representative. -/
theorem wordMap_word (w : List E) (hw : ∀ e ∈ w, e ∈ S) :
    wordMap A t ((w.map A.edge).prod) = (w.map t).prod := by
  exact hker _ w (Classical.choose_spec (A.generated ((w.map A.edge).prod))).1
    hw (Classical.choose_spec (A.generated ((w.map A.edge).prod))).2

noncomputable def wordHom : A.Carrier →* H where
  toFun := wordMap A t
  map_one' := by simpa using wordMap_word A t hker [] (by simp)
  map_mul' g h := by
    obtain ⟨p, hp, rfl⟩ := A.generated g
    obtain ⟨q, hq, rfl⟩ := A.generated h
    have hpq : ∀ e ∈ p ++ q, e ∈ S := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hp e he
      · exact hq e he
    calc
      wordMap A t ((p.map A.edge).prod * (q.map A.edge).prod) =
          wordMap A t (((p ++ q).map A.edge).prod) := by simp
      _ = ((p ++ q).map t).prod := wordMap_word A t hker (p ++ q) hpq
      _ = wordMap A t ((p.map A.edge).prod) * wordMap A t ((q.map A.edge).prod) := by
        rw [wordMap_word A t hker p hp, wordMap_word A t hker q hq]
        simp

theorem wordHom_word (w : List E) (hw : ∀ e ∈ w, e ∈ S) :
    wordHom A t hker ((w.map A.edge).prod) = (w.map t).prod :=
  wordMap_word A t hker w hw

theorem wordHom_edge (e : E) (he : e ∈ S) :
    wordHom A t hker (A.edge e) = t e := by
  simpa using wordHom_word A t hker [e] (by
    intro f hf
    have hfe : f = e := by simpa using hf
    simpa only [hfe] using he)

/-- Inverse changes of edge names yield inverse homomorphisms. -/
theorem exists_equiv_of_word_equalities (B : Data E' T) (p : E ≃ E')
    (hST : ∀ e, p e ∈ T ↔ e ∈ S)
    (hforward : ∀ w q : List E,
      (∀ e ∈ w, e ∈ S) → (∀ e ∈ q, e ∈ S) →
      (w.map A.edge).prod = (q.map A.edge).prod →
      (w.map (fun e => B.edge (p e))).prod =
        (q.map (fun e => B.edge (p e))).prod)
    (hback : ∀ w q : List E',
      (∀ e ∈ w, e ∈ T) → (∀ e ∈ q, e ∈ T) →
      (w.map B.edge).prod = (q.map B.edge).prod →
      (w.map (fun e => A.edge (p.symm e))).prod =
        (q.map (fun e => A.edge (p.symm e))).prod) :
    ∃ F : A.Carrier ≃* B.Carrier, ∀ e ∈ S, F (A.edge e) = B.edge (p e) := by
  let F := wordHom A (fun e => B.edge (p e)) hforward
  let G := wordHom B (fun e => A.edge (p.symm e)) hback
  have hF : ∀ e ∈ S, F (A.edge e) = B.edge (p e) :=
    wordHom_edge A (fun e => B.edge (p e)) hforward
  have hG : ∀ e ∈ T, G (B.edge e) = A.edge (p.symm e) :=
    wordHom_edge B (fun e => A.edge (p.symm e)) hback
  have hGF : G.comp F = MonoidHom.id _ := by
    apply A.hom_ext
    intro e he
    change G (F (A.edge e)) = A.edge e
    rw [hF e he, hG (p e) ((hST e).2 he), p.symm_apply_apply]
  have hFG : F.comp G = MonoidHom.id _ := by
    apply B.hom_ext
    intro e he
    change F (G (B.edge e)) = B.edge e
    have hs : p.symm e ∈ S := (hST (p.symm e)).1 (by simpa using he)
    rw [hG e he, hF (p.symm e) hs, p.apply_symm_apply]
  let Q : A.Carrier ≃* B.Carrier :=
    { toFun := F
      invFun := G
      left_inv := fun x => DFunLike.congr_fun hGF x
      right_inv := fun x => DFunLike.congr_fun hFG x
      map_mul' := F.map_mul }
  exact ⟨Q, hF⟩

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.Data
