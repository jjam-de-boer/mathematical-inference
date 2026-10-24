import Thesis.Probability.ConstructiveRealLogGeneralDerivative

namespace Thesis.Examples.ConstructiveLogDerivative
open Probability ConstructiveReal

/-- The derivative theorem applies to every admitted positive real point. -/
example (point : ConstructiveReal) (lower : PositiveRatio)
    (inside : LE (ofSignedRatio lower.toSignedRatio) point) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) y)
      (fun y admitted => y.positiveLog2 lower admitted) point inside
      (mul RationalLogSecant.limit (point.positiveInverse lower inside)) :=
  positiveLog2_hasDerivativeWithinAt point lower inside

/-- Zero increments do not require an equality or sign decision on reals. -/
example (point : ConstructiveReal) (lower : PositiveRatio)
    (inside : LE (ofSignedRatio lower.toSignedRatio) point) (epsilon radius : PositiveRatio)
    (small : PositiveRatio.LE radius (logModulus lower epsilon)) :
    Within (QProb.mul epsilon.toQProb radius.toQProb) (point.positiveLog2 lower inside)
      (add (point.positiveLog2 lower inside)
        (mul (sub point point) (mul RationalLogSecant.limit (point.positiveInverse lower inside)))) :=
  (positiveLog2_hasDerivativeWithinAt point lower inside).remainder epsilon radius small point inside (within_refl _ point)

private def unit : PositiveRatio := PositiveRatio.one
private def radius : PositiveRatio := ⟨1, 64, by decide, by decide⟩
private def below : PositiveRatio := ⟨63, 64, by decide, by decide⟩
private def above : PositiveRatio := ⟨65, 64, by decide, by decide⟩

/-- The same rational modulus handles actual increments on both sides. -/
example : Within radius.toQProb (rationalLog2 below)
    (mul (sub (ofSignedRatio below.toSignedRatio) one) RationalLogSecant.limit) :=
  RationalLogSecant.rational_variation unit radius below (by decide +kernel) (by decide +kernel)

example : Within radius.toQProb (rationalLog2 above)
    (mul (sub (ofSignedRatio above.toSignedRatio) one) RationalLogSecant.limit) :=
  RationalLogSecant.rational_variation unit radius above (by decide +kernel) (by decide +kernel)

private def unreducedOne : PositiveRatio := ⟨9, 9, by decide, by decide⟩
example : Within radius.toQProb (rationalLog2 unreducedOne)
    (mul (sub (ofSignedRatio unreducedOne.toSignedRatio) one) RationalLogSecant.limit) :=
  RationalLogSecant.rational_variation unit radius unreducedOne (by decide +kernel) (by decide +kernel)

/-- The reflection bound includes the endpoint h=1/2, where the quadratic
bound is an equality. -/
private def half : PositiveRatio := ⟨1, 2, by decide, by decide⟩
example : Within half.toQProb (ofSignedRatio (RationalLogSecant.reflectedStep half (by decide +kernel)).toSignedRatio)
    (ofSignedRatio half.toSignedRatio) :=
  within_mono (RationalLogSecant.reflectedStep_within half (by decide +kernel)) (by decide +kernel)

private theorem oneAdmitted : LE (ofSignedRatio half.toSignedRatio) one :=
  (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
private def realRadius : PositiveRatio := ⟨1, 256, by decide, by decide⟩
private def nearby : ConstructiveReal := ofSignedRatio ⟨511, 512, by decide⟩
private theorem nearbyAdmitted : LE (ofSignedRatio half.toSignedRatio) nearby :=
  (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)

/-- A concrete negative real increment satisfies the computed one-point
modulus and its certified analytic error bound. -/
example : Within realRadius.toQProb (nearby.positiveLog2 half nearbyAdmitted)
    (mul (sub nearby one) RationalLogSecant.limit) :=
  positiveLog2_first_variation_one nearby half nearbyAdmitted unit realRadius (by decide +kernel)
    ((within_ofSignedRatio_iff _ _ _).mpr (by decide +kernel))

private def two : PositiveRatio := PositiveRatio.ofNat 2 (by decide)
private theorem twoAdmitted : LE (ofSignedRatio unit.toSignedRatio) (ofSignedRatio two.toSignedRatio) :=
  (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)

/-- At two, the general slope is c/2. This exercises normalization at a
point other than one and the proved rational reciprocal interpretation. -/
example : HasDerivativeWithinAt (fun y => LE (ofSignedRatio unit.toSignedRatio) y)
    (fun y admitted => y.positiveLog2 unit admitted) (ofSignedRatio two.toSignedRatio) twoAdmitted
    (mul RationalLogSecant.limit (ofSignedRatio two.inv.toSignedRatio)) :=
  (positiveLog2_hasDerivativeWithinAt _ unit twoAdmitted).slope_congr
    (mul_congr (equiv_refl RationalLogSecant.limit) (ofPositiveRatio_inverse two unit twoAdmitted))

/-- Zero remains outside the stated positive logarithm domain. -/
example (admitted : LE (ofSignedRatio half.toSignedRatio) zero) : False :=
  (by decide +kernel : ¬ SignedRatio.LE half.toSignedRatio SignedRatio.zero) ((ofSignedRatio_le_iff _ _).mp admitted)

end Thesis.Examples.ConstructiveLogDerivative
