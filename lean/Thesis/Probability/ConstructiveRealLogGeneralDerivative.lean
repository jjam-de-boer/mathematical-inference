import Thesis.Probability.ConstructiveRealLogDerivative
import Thesis.Probability.ConstructiveRealLogReciprocal

namespace Thesis.Probability.ConstructiveReal

/-- A logarithm derivative modulus on an explicitly positive half-line.
The inverse is at most the natural denominator of the supplied lower bound. -/
def logModulus (lower precision : PositiveRatio) : PositiveRatio :=
  (logOneModulus (precision.divideNat lower.den lower.den_pos)).divideNat lower.den lower.den_pos

private theorem normalized_increment (x y inverse : ConstructiveReal) (unit : Equiv (mul x inverse) one) :
    Equiv (sub (mul y inverse) one) (mul (sub y x) inverse) :=
  equiv_trans (add_congr (equiv_refl (mul y inverse)) (neg_congr (equiv_symm unit)))
    (equiv_symm (sub_mul y x inverse))

private theorem add_sub_cancel_left (a b : ConstructiveReal) : Equiv (add a (sub b a)) b :=
  equiv_trans (add_comm a (sub b a)) (equiv_trans (add_assoc b (neg a) a)
    (equiv_trans (add_congr (equiv_refl b) (equiv_trans (add_comm (neg a) a) (add_neg a))) (add_zero b)))

/-- First variation at every positive real point. Normalizing by the
constructed inverse reduces to the proved variation at one. All quotient
lower bounds and reciprocal estimates are constructed from the input data. -/
theorem positiveLog2_first_variation (x y : ConstructiveReal) (lower : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y)
    (precision radius : PositiveRatio) (small : PositiveRatio.LE radius (logModulus lower precision))
    (close : Within radius.toQProb x y) :
    Within (QProb.mul precision.toQProb radius.toQProb) (y.positiveLog2 lower boundedY)
      (add (x.positiveLog2 lower boundedX)
        (mul (sub y x) (mul RationalLogSecant.limit (x.positiveInverse lower boundedX)))) := by
  let inverse := x.positiveInverse lower boundedX
  let quotient := mul y inverse
  let quotientLower := lower.mul x.positiveInverseLower
  have quotientBound : LE (ofSignedRatio quotientLower.toSignedRatio) quotient :=
    mul_positive_lower y inverse lower x.positiveInverseLower boundedY (x.positiveInverse_lower lower boundedX)
  let outerPrecision := precision.divideNat lower.den lower.den_pos
  let outerRadius := radius.mul (PositiveRatio.ofNat lower.den lower.den_pos)
  have scaledClose : Within (QProb.mul radius.toQProb (QProb.ofNat lower.den)) (mul x inverse) (mul y inverse) :=
    within_mul_right_bounded (bound := QProb.ofNat lower.den) close
      (x.positiveInverse_nonnegative lower boundedX) (x.positiveInverse_upper lower boundedX)
  have normalizedClose : Within (QProb.mul radius.toQProb (QProb.ofNat lower.den)) one quotient :=
    (within_congr (error := QProb.mul radius.toQProb (QProb.ofNat lower.den))
      (x.mul_positiveInverse lower boundedX) (equiv_refl quotient)).mp scaledClose
  have quotientClose : Within outerRadius.toQProb one quotient := normalizedClose
  have outerSmall : PositiveRatio.LE outerRadius (logOneModulus outerPrecision) :=
    QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul (logOneModulus outerPrecision) lower.den lower.den_pos)
      (QProb.mul_le_mul small (QProb.le_refl (QProb.ofNat lower.den)))
  have estimate := positiveLog2_first_variation_one quotient quotientLower quotientBound outerPrecision outerRadius outerSmall quotientClose
  have errorSame : QProb.Equiv (QProb.mul outerPrecision.toQProb outerRadius.toQProb)
      (QProb.mul precision.toQProb radius.toQProb) := by
    simp only [QProb.Equiv, QProb.mul, PositiveRatio.toQProb, PositiveRatio.divideNat,
      PositiveRatio.mul, PositiveRatio.ofNat, outerPrecision, outerRadius, Nat.mul_one]
    ac_rfl
  have logarithm : Equiv (quotient.positiveLog2 quotientLower quotientBound)
      (sub (y.positiveLog2 lower boundedY) (x.positiveLog2 lower boundedX)) :=
    positiveLog2_quotient y x lower lower boundedY boundedX
  have increment : Equiv (sub quotient one) (mul (sub y x) inverse) :=
    normalized_increment x y inverse (x.mul_positiveInverse lower boundedX)
  have linear : Equiv (mul (sub quotient one) RationalLogSecant.limit)
      (mul (sub y x) (mul RationalLogSecant.limit inverse)) :=
    equiv_trans (mul_congr increment (equiv_refl RationalLogSecant.limit))
      (equiv_trans (mul_assoc (sub y x) inverse RationalLogSecant.limit)
        (mul_congr (equiv_refl (sub y x)) (mul_comm inverse RationalLogSecant.limit)))
  have reduced := (within_congr logarithm linear).mp
    (within_mono estimate (QProb.le_congr (QProb.equiv_refl _) errorSame (QProb.le_refl _)))
  have translated := (within_add_left_iff _ (x.positiveLog2 lower boundedX) _ _).mpr reduced
  have canceled := add_sub_cancel_left (x.positiveLog2 lower boundedX) (y.positiveLog2 lower boundedY)
  exact (within_congr canceled (equiv_refl _)).mp translated

/-- Effective logarithm differentiation on the entire supplied positive
half-line, including zero increments. The base-two coefficient `c` is the
constructed secant limit; its conversion to natural-log units is a further
analytic identity, not a premise of this derivative proof. -/
def positiveLog2_hasDerivativeWithinAt (point : ConstructiveReal) (lower : PositiveRatio)
    (inside : LE (ofSignedRatio lower.toSignedRatio) point) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) y)
      (fun y admitted => y.positiveLog2 lower admitted) point inside
      (mul RationalLogSecant.limit (point.positiveInverse lower inside)) where
  modulus := logModulus lower
  remainder precision radius small y admitted close :=
    positiveLog2_first_variation point y lower inside admitted precision radius small close

end Thesis.Probability.ConstructiveReal
