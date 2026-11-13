import Thesis.Probability.ConstructiveDerivativeChain
import Thesis.Probability.ConstructiveDerivative
import Thesis.Probability.ConstructiveRealExpDistanceVariation

namespace Thesis.Probability.ConstructiveReal

/-- A computed input radius for the exponential's first-order approximation. -/
def expDerivativePrecision (x : ConstructiveReal) (epsilon : PositiveRatio) : PositiveRatio :=
  (epsilon.divideNat (RationalTaylorExponential.uniformSumBound x.expLocalBound)
    (RationalTaylorExponential.uniformSumBound_pos _)).capOne

private theorem radius_error_le (x : ConstructiveReal) (epsilon radius : PositiveRatio)
    (small : PositiveRatio.LE radius (x.expDerivativePrecision epsilon)) :
    QProb.LE (expRadiusError x.expLocalBound radius) (QProb.mul epsilon.toQProb radius.toQProb) := by
  let k := RationalTaylorExponential.uniformSumBound x.expLocalBound
  have scaled : QProb.LE (QProb.mul radius.toQProb (QProb.ofNat k)) epsilon.toQProb :=
    QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul epsilon k (RationalTaylorExponential.uniformSumBound_pos _))
      (QProb.mul_le_mul (PositiveRatio.le_trans small (PositiveRatio.capOne_le _)) (QProb.le_refl _))
  have half : QProb.LE (⟨k, 2, by decide⟩ : QProb) (QProb.ofNat k) := by
    change k * 1 ≤ k * 2
    simpa only [Nat.mul_one] using Nat.le_mul_of_pos_right k (by decide : 0 < 2)
  have estimate := QProb.le_trans (QProb.mul_le_mul (QProb.le_refl (QProb.mul radius.toQProb radius.toQProb)) half)
    (QProb.le_congr (QProb.equiv_symm (QProb.mul_assoc _ _ _)) (QProb.mul_comm _ _)
      (QProb.mul_le_mul (QProb.le_refl radius.toQProb) scaled))
  exact estimate

/-- The constructed exponential is differentiable at every constructive real,
with derivative equal to its value. The proof derives an effective modulus
from the proved Taylor remainder; no derivative or addition law is assumed. -/
def exp_hasDerivativeAt (x : ConstructiveReal) : HasDerivativeAt exp x x.exp where
  modulus := x.expDerivativePrecision
  remainder epsilon radius small y close := by
    have unit : PositiveRatio.LE radius PositiveRatio.one :=
      PositiveRatio.le_trans small (PositiveRatio.capOne_le_one _)
    exact within_mono (exp_first_variation_local x y radius unit close) (radius_error_le x epsilon radius small)

/-- Exponentials of affine real functions have their expected derivative.
This supplies the individual weight derivatives needed by finite partition
functions; normalization and logarithmic partition identities are separate. -/
def exp_affine_hasDerivativeAt (point factor offset : ConstructiveReal) :
    HasDerivativeAt (fun y => exp (add (mul y factor) offset)) point
      (mul factor (exp (add (mul point factor) offset))) :=
  (HasDerivativeAt.affine point factor offset).chain (exp_hasDerivativeAt _)

end Thesis.Probability.ConstructiveReal
