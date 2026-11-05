import GluingEPPA.Steiner.ChainValuation.GroupAttachment

/-!
# Noncommutative boundary square for a normalized restricted chain

To normalize a restricted piece of a Cayley chain, choose an old coset
representative g and a parameter k of the actual original attachment.
The translated old coset contains the attaching point h·i(k) exactly
when there is a smaller-group element u with g·p(u)=h·i(k).

The whole interface is indexed by a still smaller common group C.
When the earlier inclusion diagrams commute, the old/new translated
charts identify *all* interface points, not just the chosen k.
The formulas are valid in arbitrary groups; no commutativity,
conjugacy or subgroup normality is assumed.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w a b c
variable {H : Type u} {G : Type v} {K : Type w}
variable {P : Type a} {Q : Type b} {C : Type c}
variable [Group H] [Group G] [Group K]
variable [Group P] [Group Q] [Group C]

/-- In the old block, the correct normalized interface shift is
the element u satisfying g·p(u)=h·i(k). The equality holds
for every common-interface parameter t, in this word order. -/
theorem normalized_old_boundary
    (i : H →* G) (p : P →* G)
    (r : C →* H) (a : C →* P)
    (hcomm : p.comp a = i.comp r)
    (g h : G) (k : H) (shift : P)
    (hbase : g * p shift = h * i k) (t : C) :
    g * p (shift * a t) = h * i (k * r t) := by
  have hs : p (a t) = i (r t) := by
    exact DFunLike.congr_fun hcomm t
  calc
    g * p (shift * a t) = (g * p shift) * p (a t) := by
      simp only [map_mul, mul_assoc]
    _ = (h * i k) * i (r t) := by rw [hbase, hs]
    _ = h * i (k * r t) := by simp only [map_mul, mul_assoc]

/-- In the new block, the selected coset is represented by j(k)
and its normalized entry interface has shift one. -/
theorem normalized_new_boundary
    (j : H →* K) (q : Q →* K)
    (r : C →* H) (b : C →* Q)
    (hcomm : q.comp b = j.comp r)
    (k : H) (t : C) :
    (j k) * q (b t) = j (k * r t) := by
  have hs : q (b t) = j (r t) := DFunLike.congr_fun hcomm t
  rw [hs, map_mul]

/-- The two translated smaller-block charts yield exactly the same
point of the literal original injective pushout for every parameter
in the entire restricted common interface. -/
theorem normalized_boundary_pushout
    (i : H →* G) (j : H →* K)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (p : P →* G) (q : Q →* K)
    (r : C →* H) (a : C →* P) (b : C →* Q)
    (hOld : p.comp a = i.comp r)
    (hNew : q.comp b = j.comp r)
    (g h : G) (k : H) (shift : P)
    (hbase : g * p shift = h * i k) (t : C) :
    pushoutInl (attachLeft h i) j
        (attachLeft_injective h i hi) hj
        (g * p (shift * a t)) =
      pushoutInr (attachLeft h i) j
        (attachLeft_injective h i hi) hj
        ((j k) * q (b t)) := by
  calc
    pushoutInl (attachLeft h i) j
        (attachLeft_injective h i hi) hj
        (g * p (shift * a t)) =
      pushoutInl (attachLeft h i) j
        (attachLeft_injective h i hi) hj
        (h * i (k * r t)) := by
          rw [normalized_old_boundary i p r a hOld g h k shift hbase t]
    _ =
      pushoutInr (attachLeft h i) j
        (attachLeft_injective h i hi) hj
        (j (k * r t)) := by
          exact pushout_attachment (attachLeft h i) j
            (attachLeft_injective h i hi) hj (k * r t)
    _ =
      pushoutInr (attachLeft h i) j
        (attachLeft_injective h i hi) hj
        ((j k) * q (b t)) := by
          rw [normalized_new_boundary j q r b hNew k t]

end GluingEPPA.Steiner.ChainValuation
