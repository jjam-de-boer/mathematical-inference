import Thesis.Probability.SignedRatioOrder

namespace Thesis.Probability.FourSquareNorm

/-!
# The arithmetic identity behind the four-square bound witnesses

Integer quadruples are convenient during descent because residue
representatives and the product formula may be negative. Squaring removes
that dependence. Euler's identity gives an explicit representation of a
product whenever the two factors are represented. In the descent the
second quadruple is congruent to the first modulo the current multiplier;
then the dot product and the three alternating coordinates are divisible
by that multiplier.
-/

structure Quad where
  first : Int
  second : Int
  third : Int
  fourth : Int

namespace Quad

def norm (a : Quad) : Int :=
  a.first * a.first + a.second * a.second + a.third * a.third + a.fourth * a.fourth

/-- Euler's four-square product, with a dot product and three alternating
coordinates. This orientation exposes the congruent-input descent. -/
def product (a b : Quad) : Quad :=
  ⟨a.first * b.first + a.second * b.second + a.third * b.third + a.fourth * b.fourth,
    a.first * b.second - a.second * b.first + a.third * b.fourth - a.fourth * b.third,
    a.first * b.third - a.second * b.fourth - a.third * b.first + a.fourth * b.second,
    a.first * b.fourth + a.second * b.third - a.third * b.second - a.fourth * b.first⟩

/-- Euler's identity by polynomial normalization over the integers. -/
theorem norm_product (a b : Quad) : (a.product b).norm = a.norm * b.norm := by
  simp only [norm, product]
  grind

def scale (a : Quad) (factor : Int) : Quad :=
  ⟨factor * a.first, factor * a.second, factor * a.third, factor * a.fourth⟩

theorem norm_scale (a : Quad) (factor : Int) : (a.scale factor).norm = factor * factor * a.norm := by
  simp only [norm, scale]
  grind

/-- Coordinatewise congruence modulo a supplied integer. -/
def Congruent (a b : Quad) (modulus : Int) : Prop :=
  modulus ∣ a.first - b.first ∧ modulus ∣ a.second - b.second ∧
    modulus ∣ a.third - b.third ∧ modulus ∣ a.fourth - b.fourth

/-- A product of congruent quadruples has every coordinate divisible by
`modulus` when the second quadruple's norm is divisible by `modulus`. -/
theorem product_dvd_of_congruent (a b : Quad) (modulus : Int)
    (congruent : a.Congruent b modulus) (normDvd : modulus ∣ b.norm) :
    ∃ divided : Quad, divided.scale modulus = a.product b := by
  rcases congruent with ⟨⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩, ⟨u, hu⟩⟩
  rcases normDvd with ⟨scaleNorm, hNorm⟩
  have first : a.first = b.first + modulus * r := by omega
  have second : a.second = b.second + modulus * s := by omega
  have third : a.third = b.third + modulus * t := by omega
  have fourth : a.fourth = b.fourth + modulus * u := by omega
  refine ⟨⟨scaleNorm + r * b.first + s * b.second + t * b.third + u * b.fourth,
    r * b.second - s * b.first + t * b.fourth - u * b.third,
    r * b.third - s * b.fourth - t * b.first + u * b.second,
    r * b.fourth + s * b.third - t * b.second - u * b.first⟩, ?_⟩
  have normalized : modulus * scaleNorm =
      b.first * b.first + b.second * b.second + b.third * b.third + b.fourth * b.fourth := hNorm.symm
  simp only [scale, product, first, second, third, fourth, Quad.mk.injEq]
  constructor
  · rw [Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add, normalized]
    grind
  · exact ⟨by grind, by grind, by grind⟩

end Quad
end Thesis.Probability.FourSquareNorm
