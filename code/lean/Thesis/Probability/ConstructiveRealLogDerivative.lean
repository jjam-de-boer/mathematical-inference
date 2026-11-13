import Thesis.Probability.RationalLogSignedVariation
import Thesis.Probability.ConstructiveRealLogLimits
import Thesis.Probability.ConstructiveRealProductLimits
import Thesis.Probability.ConstructiveDerivativeWithin

namespace Thesis.Probability.ConstructiveReal

/-- Spare half of the rational variation radius absorbs input-enclosure
errors before passage to a real limit. -/
def logOneModulus (precision : PositiveRatio) : PositiveRatio :=
  (RationalLogSecant.variationModulus precision.half).half

/-- Two-sided first variation of the constructed logarithm at one, for
arbitrary real nearby values with a supplied positive lower bound. The input
increment may be zero and its sign need not be decidable. -/
theorem positiveLog2_first_variation_one (y : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) y) (precision radius : PositiveRatio)
    (small : PositiveRatio.LE radius (logOneModulus precision)) (close : Within radius.toQProb one y) :
    Within (QProb.mul precision.toQProb radius.toQProb) (y.positiveLog2 lower bounded)
      (mul (sub y one) RationalLogSecant.limit) := by
  let inputs := y.positiveSequence lower bounded
  let linear := (inputs.sub (RealCauchySequence.constant one)).mul (RealCauchySequence.constant RationalLogSecant.limit)
  let enlarged := radius.mul (PositiveRatio.ofNat 2 (by decide))
  have enlargedSmall : PositiveRatio.LE enlarged (RationalLogSecant.variationModulus precision.half) := by
    simpa only [PositiveRatio.LE, PositiveRatio.toQProb, QProb.LE, enlarged, logOneModulus,
      PositiveRatio.half, PositiveRatio.mul, PositiveRatio.ofNat, Nat.mul_one, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using small
  have errorSame : QProb.Equiv (QProb.mul precision.half.toQProb enlarged.toQProb)
      (QProb.mul precision.toQProb radius.toQProb) := by
    simp only [QProb.Equiv, QProb.mul, PositiveRatio.toQProb, PositiveRatio.half, enlarged,
      PositiveRatio.mul, PositiveRatio.ofNat, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have compared := RealCauchySequence.limit_within_of_tail (y.logSequence lower bounded) linear
    (QProb.mul precision.toQProb radius.toQProb) radius.den (by
      intro n later
      let unit := PositiveRatio.unitPrecision n
      let value := y.positiveCenter lower unit
      have inputClose := within_symm (within_triangle close (y.positiveCenter_within lower bounded unit))
      have errorBound : QProb.LE (QProb.add radius.toQProb unit.toQProb) enlarged.toQProb := by
        have doubled : QProb.Equiv (QProb.add radius.toQProb radius.toQProb) enlarged.toQProb := by
          simp only [QProb.Equiv, QProb.add, PositiveRatio.toQProb, PositiveRatio.mul,
            PositiveRatio.ofNat, enlarged, Nat.mul_one, Nat.mul_two, Nat.add_mul]
          ac_rfl
        exact QProb.le_congr (QProb.equiv_refl _) doubled
          (QProb.add_le_add (QProb.le_refl _) (PositiveRatio.unitPrecision_le radius n later))
      have rationalClose := (within_ofSignedRatio_iff value.toSignedRatio SignedRatio.one enlarged.toQProb).mp
        (within_mono inputClose errorBound)
      have estimate := RationalLogSecant.rational_variation precision.half enlarged value enlargedSmall rationalClose
      exact within_mono estimate (QProb.le_congr (QProb.equiv_refl _) errorSame (QProb.le_refl _)))
  have inputLimit : Equiv inputs.limit y := y.positiveSequence_limit lower bounded
  have differenceLimit : Equiv (inputs.sub (RealCauchySequence.constant one)).limit (sub y one) :=
    equiv_trans (RealCauchySequence.sub_limit _ _)
      (add_congr inputLimit (neg_congr (RealCauchySequence.constant_limit one)))
  have linearLimit : Equiv linear.limit (mul (sub y one) RationalLogSecant.limit) :=
    equiv_trans (RealCauchySequence.mul_limit _ _)
      (mul_congr differenceLimit (RealCauchySequence.constant_limit RationalLogSecant.limit))
  exact (within_congr (equiv_refl _) linearLimit).mp compared

/-- The logarithm has a computed domain-relative derivative at one on
any supplied positive half-line containing one. Its coefficient was derived
from finite logarithm comparisons and effective limits. -/
def positiveLog2_hasDerivativeWithinAt_one (lower : PositiveRatio)
    (inside : LE (ofSignedRatio lower.toSignedRatio) one) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) y)
      (fun y admitted => y.positiveLog2 lower admitted) one inside RationalLogSecant.limit where
  modulus := logOneModulus
  remainder precision radius small y admitted close :=
    (within_congr (equiv_refl _) (equiv_symm (equiv_trans
      (add_congr (positiveLog2_one lower inside) (equiv_refl _)) (zero_add _)))).mp
      (positiveLog2_first_variation_one y lower admitted precision radius small close)

end Thesis.Probability.ConstructiveReal
