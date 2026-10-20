import GluingEPPA.Steiner.QuotientSymmetry

/-!
# Coherent two-spoke corrections

The extension assigned to a partial automorphism has the form
`L_(range) * F_(permutation) * L_(domain)⁻¹`. This file proves the
multiplicative identity behind coherence in an arbitrary group.
It does not assume or claim that those elements have yet been realized
as automorphisms of the final Steiner witness.
-/

namespace GluingEPPA.Steiner

universe u v w
variable {P : Type u} {H : Type v} [Group P] [Group H]

/-- The algebraic correction with given domain and range spokes. -/
def twoSpoke (F : P →* H) (sigma : P) (dom ran : H) : H :=
  ran * F sigma * dom⁻¹

theorem twoSpoke_id (F : P →* H) (a : H) :
    twoSpoke F 1 a a = 1 := by
  simp [twoSpoke]

/-- The middle spoke cancels for composable partial maps. -/
theorem twoSpoke_comp (F : P →* H) (sigma tau : P) (a b c : H) :
    twoSpoke F (tau * sigma) a c =
      twoSpoke F tau b c * twoSpoke F sigma a b := by
  simp only [twoSpoke, map_mul]
  group

/-- The data from which the coherent extension family is constructed. -/
structure CoherentSpokes (I : Type w) (P : Type u) (H : Type v)
    [Group P] [Group H] where
  sigma : I → P
  domain : I → H
  range : I → H

namespace CoherentSpokes

variable {I : Type w} (D : CoherentSpokes I P H)

def extension (F : P →* H) (f : I) : H :=
  twoSpoke F (D.sigma f) (D.domain f) (D.range f)

theorem extension_id (F : P →* H) (f : I)
    (hsigma : D.sigma f = 1)
    (hspoke : D.domain f = D.range f) :
    D.extension F f = 1 := by
  rw [extension, hsigma, hspoke]
  exact twoSpoke_id F (D.range f)

theorem extension_comp (F : P →* H) (f g h : I)
    (hmiddle : D.range f = D.domain g)
    (hsigma : D.sigma h = D.sigma g * D.sigma f)
    (hdomain : D.domain h = D.domain f)
    (hrange : D.range h = D.range g) :
    D.extension F h = D.extension F g * D.extension F f := by
  calc
    D.extension F h =
        twoSpoke F (D.sigma g * D.sigma f) (D.domain f) (D.range g) := by
          simp [extension, hsigma, hdomain, hrange]
    _ = twoSpoke F (D.sigma g) (D.range f) (D.range g) *
        twoSpoke F (D.sigma f) (D.domain f) (D.range f) :=
          twoSpoke_comp F (D.sigma f) (D.sigma g)
            (D.domain f) (D.range f) (D.range g)
    _ = D.extension F g * D.extension F f := by
          simp only [extension, hmiddle]

end CoherentSpokes
end GluingEPPA.Steiner
