import Thesis.Probability.RationalLogVariation
import Thesis.Probability.ConstructiveRealDistanceBounded
import Thesis.Probability.ConstructiveRealDistanceScaling
import Thesis.Probability.ConstructiveRealDifferenceLimits

namespace Thesis.Probability.RationalLogSecant
open ConstructiveReal

private theorem retreat_positive (step : PositiveRatio)
    (small : PositiveRatio.LE step (⟨1, 2, by decide, by decide⟩ : PositiveRatio)) : 0 < step.den - step.num := by
  have bounded : step.num * 2 ≤ step.den := by simpa only [PositiveRatio.LE, PositiveRatio.toQProb, QProb.LE, Nat.one_mul] using small
  have positive := step.num_pos
  omega

/-- A positive rational point `1-h` with an explicit small-step certificate. -/
def retreat (step : PositiveRatio)
    (small : PositiveRatio.LE step (⟨1, 2, by decide, by decide⟩ : PositiveRatio)) : PositiveRatio :=
  ⟨step.den - step.num, step.den, retreat_positive step small, step.den_pos⟩

/-- Inversion sends the retreat `1-h` to the advance `1+h/(1-h)`. -/
def reflectedStep (step : PositiveRatio)
    (small : PositiveRatio.LE step (⟨1, 2, by decide, by decide⟩ : PositiveRatio)) : PositiveRatio :=
  ⟨step.num, step.den - step.num, step.num_pos, retreat_positive step small⟩

theorem retreat_log (step : PositiveRatio)
    (small : PositiveRatio.LE step (⟨1, 2, by decide, by decide⟩ : PositiveRatio)) :
    Equiv (rationalLog2 (retreat step small)) (neg (rationalLog2 (offsetPoint (reflectedStep step small)))) := by
  have recovered : step.den - step.num + step.num = step.den := Nat.sub_add_cancel (by
    have := retreat_positive step small; omega)
  have equal : (offsetPoint (reflectedStep step small)).inv = retreat step small := by
    apply PositiveRatio.ext <;> simp only [offsetPoint, reflectedStep, retreat, PositiveRatio.inv, recovered]
  rw [← equal]
  exact rationalLog2_inv _

theorem reflectedStep_le_twice (step : PositiveRatio)
    (small : PositiveRatio.LE step (⟨1, 2, by decide, by decide⟩ : PositiveRatio)) :
    QProb.LE (reflectedStep step small).toQProb (QProb.scale 2 step.toQProb) := by
  change step.num * step.den ≤ (2 * step.num) * (step.den - step.num)
  have bounded : step.num * 2 ≤ step.den := by simpa only [PositiveRatio.LE, PositiveRatio.toQProb, QProb.LE, Nat.one_mul] using small
  have denominator : step.den ≤ 2 * (step.den - step.num) := by omega
  simpa only [Nat.mul_assoc, Nat.mul_left_comm 2 step.num] using Nat.mul_le_mul_left step.num denominator

/-- The reflected increment differs from the original by at most `2h²`.
The proof is finite rational algebra and includes unreduced step data. -/
theorem reflectedStep_within (step : PositiveRatio)
    (small : PositiveRatio.LE step (⟨1, 2, by decide, by decide⟩ : PositiveRatio)) :
    Within (QProb.scale 2 (QProb.mul step.toQProb step.toQProb))
      (ofSignedRatio (reflectedStep step small).toSignedRatio) (ofSignedRatio step.toSignedRatio) := by
  have recovered : step.den - step.num + step.num = step.den := Nat.sub_add_cancel (by
    have := retreat_positive step small; omega)
  let difference : QProb := ⟨step.num * step.num, (step.den - step.num) * step.den,
    Nat.mul_pos (retreat_positive step small) step.den_pos⟩
  have identity : SignedRatio.Equiv
      (SignedRatio.sub (reflectedStep step small).toSignedRatio step.toSignedRatio) difference.toSignedRatio := by
    simp only [SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add, SignedRatio.neg,
      PositiveRatio.toSignedRatio, PositiveRatio.toQProb, QProb.toSignedRatio, reflectedStep, difference,
      Int.natCast_mul, Int.neg_mul]
    have recovery := congrArg (fun n : Nat => (n : Int)) recovered
    simp only [Int.natCast_add] at recovery
    have rewriteDen : (step.den : Int) = ((step.den - step.num : Nat) : Int) + (step.num : Int) := recovery.symm
    have numerator : (step.num : Int) * (step.den : Int) + -((step.num : Int) * ((step.den - step.num : Nat) : Int)) =
        (step.num : Int) * (step.num : Int) := by
      rw [rewriteDen, Int.mul_add]
      omega
    rw [numerator]
  have bound : QProb.LE difference (QProb.scale 2 (QProb.mul step.toQProb step.toQProb)) := by
    have doubled := reflectedStep_le_twice step small
    have scale := QProb.mul_le_mul doubled (QProb.le_refl step.toQProb)
    simpa only [QProb.LE, QProb.mul, QProb.scale, PositiveRatio.toQProb,
      reflectedStep, difference, Nat.mul_assoc] using scale
  apply (within_ofSignedRatio_iff _ _ _).mpr
  exact QProb.le_congr (QProb.equiv_symm (SignedRatio.magnitude_congr identity)) (QProb.equiv_refl _)
    (QProb.le_congr (by
      simp only [SignedRatio.magnitude, QProb.toSignedRatio, Int.natAbs_natCast]
      exact QProb.equiv_refl _) (QProb.equiv_refl _) bound)


/-- A common computable left radius enforces the reflected right radius,
the positive-domain bound, and the quadratic-error bound simultaneously. -/
def leftModulus (precision : PositiveRatio) : PositiveRatio :=
  ⟨1, 2 * (rightModulus (precision.divideNat 4 (by decide))).den + 12 * precision.den,
    by decide, by have := precision.den_pos; omega⟩

theorem leftModulus_le_half (precision : PositiveRatio) :
    PositiveRatio.LE (leftModulus precision) (⟨1, 2, by decide, by decide⟩ : PositiveRatio) := by
  have positive := precision.den_pos
  change 1 * 2 ≤ 1 * (2 * (rightModulus (precision.divideNat 4 (by decide))).den + 12 * precision.den)
  omega

theorem leftModulus_le_linear (precision : PositiveRatio) :
    PositiveRatio.LE (leftModulus precision) (precision.divideNat 12 (by decide)) := by
  change 1 * (precision.den * 12) ≤ precision.num * (leftModulus precision).den
  rw [Nat.one_mul]
  exact Nat.le_trans (by simp only [leftModulus]; omega) (Nat.le_mul_of_pos_left _ precision.num_pos)

private theorem reflected_small (precision step : PositiveRatio)
    (small : PositiveRatio.LE step (leftModulus precision))
    (half : PositiveRatio.LE step (⟨1, 2, by decide, by decide⟩ : PositiveRatio)) :
    PositiveRatio.LE (reflectedStep step half) (rightModulus (precision.divideNat 4 (by decide))) := by
  have doubled : QProb.LE (QProb.scale 2 step.toQProb) (QProb.scale 2 (leftModulus precision).toQProb) :=
    QProb.scale_le_scale 2 small
  have upper : QProb.LE (QProb.scale 2 (leftModulus precision).toQProb)
      (rightModulus (precision.divideNat 4 (by decide))).toQProb := by
    simp only [QProb.LE, QProb.scale, PositiveRatio.toQProb, leftModulus, rightModulus, Nat.mul_one, Nat.one_mul]
    omega
  exact QProb.le_trans (reflectedStep_le_twice step half) (QProb.le_trans doubled upper)

private theorem left_quadratic_small (precision step : PositiveRatio)
    (small : PositiveRatio.LE step (leftModulus precision)) :
    QProb.LE (QProb.mul (QProb.scale 2 (QProb.mul step.toQProb step.toQProb)) (QProb.ofNat 3))
      (QProb.mul precision.half.toQProb step.toQProb) := by
  have bounded := PositiveRatio.le_trans small (leftModulus_le_linear precision)
  have scaled := Nat.mul_le_mul_right (step.num * step.den) bounded
  simpa only [PositiveRatio.LE, PositiveRatio.toQProb, QProb.LE, QProb.mul, QProb.scale,
    QProb.ofNat, PositiveRatio.half, PositiveRatio.divideNat, Nat.mul_one, Nat.one_mul,
    show (12 : Nat) = 2 * (2 * 3) from rfl, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using scaled

/-- The left logarithm has the same first-variation coefficient as the
right logarithm. Its reflected-step and quadratic errors are both certified,
with all hypotheses checked using positive rational comparisons. -/
theorem left_variation (precision step : PositiveRatio) (small : PositiveRatio.LE step (leftModulus precision)) :
    Within (QProb.mul precision.toQProb step.toQProb)
      (rationalLog2 (retreat step (PositiveRatio.le_trans small (leftModulus_le_half precision))))
      (neg (mul (ofSignedRatio step.toSignedRatio) limit)) := by
  let half := PositiveRatio.le_trans small (leftModulus_le_half precision)
  let reflected := reflectedStep step half
  have first := within_neg (right_variation (precision.divideNat 4 (by decide)) reflected (reflected_small precision step small half))
  have firstBound : QProb.LE (QProb.mul (precision.divideNat 4 (by decide)).toQProb reflected.toQProb)
      (QProb.mul precision.half.toQProb step.toQProb) := by
    have compared := QProb.mul_le_mul (QProb.le_refl (precision.divideNat 4 (by decide)).toQProb) (reflectedStep_le_twice step half)
    have collect : QProb.Equiv
        (QProb.mul (precision.divideNat 4 (by decide)).toQProb (QProb.scale 2 step.toQProb))
        (QProb.mul precision.half.toQProb step.toQProb) := by
      simp only [QProb.Equiv, QProb.mul, QProb.scale, PositiveRatio.toQProb, PositiveRatio.divideNat, PositiveRatio.half,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    exact QProb.le_congr (QProb.equiv_refl _) collect compared
  have second := within_neg (within_mul_right_bounded (bound := QProb.ofNat 3) (reflectedStep_within step half)
    (le_trans ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel : SignedRatio.LE SignedRatio.zero SignedRatio.one)) one_le_limit) limit_le_three)
  have combined := within_triangle (within_mono first firstBound) (within_mono second (left_quadratic_small precision step small))
  have collect : QProb.Equiv
      (QProb.add (QProb.mul precision.half.toQProb step.toQProb) (QProb.mul precision.half.toQProb step.toQProb))
      (QProb.mul precision.toQProb step.toQProb) :=
    QProb.equiv_trans (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))
      (QProb.mul_congr precision.half_sum (QProb.equiv_refl _))
  exact (within_congr (equiv_symm (retreat_log step half)) (equiv_refl _)).mp
    (within_mono combined (QProb.le_congr (QProb.equiv_refl _) collect (QProb.le_refl _)))

end Thesis.Probability.RationalLogSecant
