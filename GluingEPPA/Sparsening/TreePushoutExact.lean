import GluingEPPA.Sparsening.TreePushoutRelations

/-!
# Exact source embeddings into a relational/unary strong amalgam

A compact port of the key step in AllThoseEPPA/TreeLikeAmalgamEmbeddings:
the overlap lemma forces any tuple represented from both sides into the
common interface. Consequently neither relation reflection nor complete
unary fibres acquire extraneous values after free amalgamation.

This does not assume that the resulting structure is an EPPA witness,
nor invoke the pre-existing AllThoseEPPA restricted EPPA theorem.
-/
namespace GluingEPPA.Sparsening.Tree
universe u v w x t
variable {L : Nat → Type u} {F : Type t}
variable {I : Type v} {X : Type w} {Y : Type x}

/-- The two representations of a tuple agree only when every coordinate
comes from one and the same interface. This also covers empty tuples. -/
theorem tuple_overlap
    (f : I → X) (g : I → Y) (hg : Function.Injective g)
    {n : Nat} {xs : Fin n → X} {ys : Fin n → Y}
    (eq : (fun j => inclLeft f g (xs j)) =
          (fun j => inclRight f g (ys j))) :
    ∃ cs : Fin n → I,
      (∀ j, xs j = f (cs j)) ∧ (∀ j, ys j = g (cs j)) := by
  have pointwise : ∀ j : Fin n, ∃ c : I,
      xs j = f c ∧ ys j = g c := by
    intro j
    exact (left_eq_right_iff f g hg (xs j) (ys j)).mp (congrFun eq j)
  choose cs hxs hys using pointwise
  exact ⟨cs, hxs, hys⟩

theorem left_rel_iff
    (RI : RelStructure L I) (outI : F → I → Set I)
    (RX : RelStructure L X) (outX : F → X → Set X)
    (RY : RelStructure L Y) (outY : F → Y → Set Y)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    {n : Nat} (r : L n) (xs : Fin n → X) :
    (pushoutRelations ef.toFun eg.toFun RX RY).rel r
      (fun j => inclLeft ef.toFun eg.toFun (xs j)) ↔ RX.rel r xs := by
  constructor
  · intro h
    change (∃ zs : Fin n → X,
      (fun j => inclLeft ef.toFun eg.toFun (zs j)) =
        (fun j => inclLeft ef.toFun eg.toFun (xs j)) ∧ RX.rel r zs) ∨
      (∃ ys : Fin n → Y,
      (fun j => inclRight ef.toFun eg.toFun (ys j)) =
        (fun j => inclLeft ef.toFun eg.toFun (xs j)) ∧ RY.rel r ys) at h
    rcases h with ⟨zs, hz, hr⟩ | ⟨ys, hy, hr⟩
    · have hz_eq : zs = xs := by
        funext j
        exact inclLeft_injective ef.toFun eg.toFun (congrFun hz j)
      simpa only [hz_eq] using hr
    · obtain ⟨cs, hxs, hys⟩ :=
        tuple_overlap ef.toFun eg.toFun eg.injective hy.symm
      have hy_eq : (fun j => eg.toFun (cs j)) = ys :=
        funext (fun j => (hys j).symm)
      have hRI : RI.rel r cs :=
        (eg.rel_iff r cs).mp (by simpa only [hy_eq] using hr)
      have hRX : RX.rel r (fun j => ef.toFun (cs j)) :=
        (ef.rel_iff r cs).mpr hRI
      have hx_eq : (fun j => ef.toFun (cs j)) = xs :=
        funext (fun j => (hxs j).symm)
      simpa only [hx_eq] using hRX
  · exact left_map_rel ef.toFun eg.toFun RX RY r xs

theorem right_rel_iff
    (RI : RelStructure L I) (outI : F → I → Set I)
    (RX : RelStructure L X) (outX : F → X → Set X)
    (RY : RelStructure L Y) (outY : F → Y → Set Y)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    {n : Nat} (r : L n) (ys : Fin n → Y) :
    (pushoutRelations ef.toFun eg.toFun RX RY).rel r
      (fun j => inclRight ef.toFun eg.toFun (ys j)) ↔ RY.rel r ys := by
  constructor
  · intro h
    change (∃ xs : Fin n → X,
      (fun j => inclLeft ef.toFun eg.toFun (xs j)) =
        (fun j => inclRight ef.toFun eg.toFun (ys j)) ∧ RX.rel r xs) ∨
      (∃ zs : Fin n → Y,
      (fun j => inclRight ef.toFun eg.toFun (zs j)) =
        (fun j => inclRight ef.toFun eg.toFun (ys j)) ∧ RY.rel r zs) at h
    rcases h with ⟨xs, hx, hr⟩ | ⟨zs, hz, hr⟩
    · obtain ⟨cs, hxs, hys⟩ :=
        tuple_overlap ef.toFun eg.toFun eg.injective hx
      have hx_eq : (fun j => ef.toFun (cs j)) = xs :=
        funext (fun j => (hxs j).symm)
      have hRI : RI.rel r cs :=
        (ef.rel_iff r cs).mp (by simpa only [hx_eq] using hr)
      have hRY : RY.rel r (fun j => eg.toFun (cs j)) :=
        (eg.rel_iff r cs).mpr hRI
      have hy_eq : (fun j => eg.toFun (cs j)) = ys :=
        funext (fun j => (hys j).symm)
      simpa only [hy_eq] using hRY
    · have hz_eq : zs = ys := by
        funext j
        exact inclRight_injective ef.toFun eg.toFun
          ef.injective eg.injective (congrFun hz j)
      simpa only [hz_eq] using hr
  · exact right_map_rel ef.toFun eg.toFun RX RY r ys

/-- Source interface fibres remain exactly equal after amalgamation;
the opposite side cannot introduce any new unary outputs over the interface. -/
theorem left_unary_image_eq
    (RI : RelStructure L I) (outI : F → I → Set I)
    (RX : RelStructure L X) (outX : F → X → Set X)
    (RY : RelStructure L Y) (outY : F → Y → Set Y)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (h : F) (x : X) :
    (inclLeft ef.toFun eg.toFun) '' outX h x =
      pushoutOutput ef.toFun eg.toFun outX outY h
        (inclLeft ef.toFun eg.toFun x) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact left_map_unary ef.toFun eg.toFun outX outY h x z hz
  · intro hw
    change (∃ a : X, inclLeft ef.toFun eg.toFun a =
      inclLeft ef.toFun eg.toFun x ∧
        w ∈ inclLeft ef.toFun eg.toFun '' outX h a) ∨
      (∃ b : Y, inclRight ef.toFun eg.toFun b =
      inclLeft ef.toFun eg.toFun x ∧
        w ∈ inclRight ef.toFun eg.toFun '' outY h b) at hw
    rcases hw with ⟨a, ha, hw⟩ | ⟨b, hb, hw⟩
    · have he : a = x :=
        inclLeft_injective ef.toFun eg.toFun ha
      simpa only [he] using hw
    · obtain ⟨i, hxi, hbi⟩ :=
        (left_eq_right_iff ef.toFun eg.toFun eg.injective x b).mp hb.symm
      obtain ⟨z, hz, hzw⟩ := hw
      have hzOld : z ∈ eg.toFun '' outI h i := by
        rw [eg.out_eq h i]
        simpa only [hbi] using hz
      obtain ⟨c, hc, hgc⟩ := hzOld
      have hfmem : ef.toFun c ∈ outX h x := by
        rw [hxi, ← ef.out_eq h i]
        exact ⟨c, hc, rfl⟩
      refine ⟨ef.toFun c, hfmem, ?_⟩
      calc
        inclLeft ef.toFun eg.toFun (ef.toFun c) =
          inclRight ef.toFun eg.toFun (eg.toFun c) :=
          (inclRight_glued ef.toFun eg.toFun eg.injective c).symm
        _ = inclRight ef.toFun eg.toFun z := congrArg _ hgc
        _ = w := hzw

theorem right_unary_image_eq
    (RI : RelStructure L I) (outI : F → I → Set I)
    (RX : RelStructure L X) (outX : F → X → Set X)
    (RY : RelStructure L Y) (outY : F → Y → Set Y)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (h : F) (y : Y) :
    (inclRight ef.toFun eg.toFun) '' outY h y =
      pushoutOutput ef.toFun eg.toFun outX outY h
        (inclRight ef.toFun eg.toFun y) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact right_map_unary ef.toFun eg.toFun outX outY h y z hz
  · intro hw
    change (∃ a : X, inclLeft ef.toFun eg.toFun a =
      inclRight ef.toFun eg.toFun y ∧
        w ∈ inclLeft ef.toFun eg.toFun '' outX h a) ∨
      (∃ b : Y, inclRight ef.toFun eg.toFun b =
      inclRight ef.toFun eg.toFun y ∧
        w ∈ inclRight ef.toFun eg.toFun '' outY h b) at hw
    rcases hw with ⟨a, ha, hw⟩ | ⟨b, hb, hw⟩
    · obtain ⟨i, hai, hyi⟩ :=
        (left_eq_right_iff ef.toFun eg.toFun eg.injective a y).mp ha
      obtain ⟨z, hz, hzw⟩ := hw
      have hzOld : z ∈ ef.toFun '' outI h i := by
        rw [ef.out_eq h i]
        simpa only [hai] using hz
      obtain ⟨c, hc, hfc⟩ := hzOld
      have hgmem : eg.toFun c ∈ outY h y := by
        rw [hyi, ← eg.out_eq h i]
        exact ⟨c, hc, rfl⟩
      refine ⟨eg.toFun c, hgmem, ?_⟩
      calc
        inclRight ef.toFun eg.toFun (eg.toFun c) =
          inclLeft ef.toFun eg.toFun (ef.toFun c) :=
          inclRight_glued ef.toFun eg.toFun eg.injective c
        _ = inclLeft ef.toFun eg.toFun z := congrArg _ hfc
        _ = w := hzw
    · have he : b = y :=
        inclRight_injective ef.toFun eg.toFun
          ef.injective eg.injective hb
      simpa only [he] using hw

end GluingEPPA.Sparsening.Tree
