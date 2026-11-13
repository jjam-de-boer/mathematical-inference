import Thesis.Probability.RationalLogVariation

namespace Thesis.Examples.RationalLogVariation
open Probability ConstructiveReal

/-- Weighted AM–GM accepts a nonunit arithmetic mean. -/
example : PositiveRatio.LE
    (RationalAMGM.weightedProduct [(PositiveRatio.ofNat 2 (by decide), 1), (PositiveRatio.ofNat 8 (by decide), 1)])
    ((PositiveRatio.ofNat 5 (by decide)).pow 2) :=
  RationalAMGM.weightedProduct_le_mean _ _ (by decide +kernel)

/-- Zero multiplicities remain valid even when all recorded values exceed
one. They contribute neither arithmetic mass nor a product factor. -/
example : PositiveRatio.LE
    (RationalAMGM.weightedProduct [(PositiveRatio.ofNat 9 (by decide), 0), (PositiveRatio.ofNat 7 (by decide), 0)])
    PositiveRatio.one := RationalAMGM.weightedProduct_le_mean _ PositiveRatio.one (by decide +kernel)

example : ExactLog.LE
    (ExactLog.divideNat (ExactLog.add (ExactLog.log (PositiveRatio.ofNat 2 (by decide)))
      (ExactLog.log (PositiveRatio.ofNat 8 (by decide)))) 2 (by decide))
    (ExactLog.log (PositiveRatio.ofNat 5 (by decide))) :=
  by
    simpa only [ExactLog.scaleNat_one] using
      rational_log_pair_concavity (PositiveRatio.ofNat 2 (by decide)) (PositiveRatio.ofNat 8 (by decide))
        (PositiveRatio.ofNat 5 (by decide)) 1 1 (by decide) (by decide +kernel)

/-- Coincident secants exercise the zero complementary weight in the
concavity proof, while nonreciprocal steps use the general interface. -/
example : ExactLog.LE (RationalLogSecant.offsetSlope ⟨2, 3, by decide, by decide⟩)
    (RationalLogSecant.offsetSlope ⟨1, 7, by decide, by decide⟩) :=
  RationalLogSecant.offsetSlope_antitone _ _ (by decide +kernel)

example (step : PositiveRatio) : ExactLog.LE (RationalLogSecant.offsetSlope step) (RationalLogSecant.offsetSlope step) :=
  RationalLogSecant.offsetSlope_antitone step step (PositiveRatio.le_refl _)

/-- Unreduced rational steps give the same exact logarithmic secant. -/
example : ExactLog.Equiv (RationalLogSecant.offsetSlope ⟨2, 8, by decide, by decide⟩)
    (RationalLogSecant.offsetSlope ⟨1, 4, by decide, by decide⟩) := by decide +kernel

example : Within (⟨1, 8, by decide⟩ : QProb) (RationalLogSecant.realValue 4) RationalLogSecant.limit :=
  within_mono (RationalLogSecant.remainder 4) (by decide +kernel)

example : LE one RationalLogSecant.limit := RationalLogSecant.one_le_limit
example : LE RationalLogSecant.limit (ofSignedRatio ⟨3, 1, by decide⟩) := RationalLogSecant.limit_le_three

private def precision : PositiveRatio := ⟨1, 8, by decide, by decide⟩
private def step : PositiveRatio := ⟨3, 256, by decide, by decide⟩

/-- A non-dyadic positive increment satisfies the actual computed modulus.
The resulting certified analytic error is 3/2048. -/
example : Within (⟨3, 2048, by decide⟩ : QProb)
    (rationalLog2 (RationalLogSecant.offsetPoint step))
    (mul (ofSignedRatio step.toSignedRatio) RationalLogSecant.limit) := by
  have small : PositiveRatio.LE step (RationalLogSecant.rightModulus precision) := by decide +kernel
  exact within_mono (RationalLogSecant.right_variation precision step small) (by decide +kernel)

/-- The generic geometric-increment construction includes a zero error
coefficient; its completed constant sequence has the original real value. -/
example (x : ConstructiveReal) :
    Equiv (RealCauchySequence.ofDyadicSteps (fun _ => x) 0 (fun _ => within_refl _ x)).limit x :=
  equiv_trans (RealCauchySequence.limit_congr _ (RealCauchySequence.constant x) (fun _ => equiv_refl _))
    (RealCauchySequence.constant_limit x)

end Thesis.Examples.RationalLogVariation
