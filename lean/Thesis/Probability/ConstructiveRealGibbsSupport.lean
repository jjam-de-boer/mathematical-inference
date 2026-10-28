import Thesis.Probability.ConstructiveRealEntropyGibbsForm

namespace Thesis.Probability.Distros.RationalEntropyProblem.LagrangeCoefficients
open ConstructiveReal

/-- A normalized finite Gibbs weight has a computed positive floor, for
any finite coefficient values, independently of a multiplier optimality proof. -/
def gibbsLower {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (index : Fin variables) : PositiveRatio :=
  (neg (certificate.score index)).expLower.mul certificate.partition.positiveInverseLower

theorem gibbs_positive {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (index : Fin variables) :
    LE (ofSignedRatio (certificate.gibbsLower index).toSignedRatio)
      (mul (neg (certificate.score index)).exp certificate.partitionInverse) :=
  mul_positive_lower _ _ (neg (certificate.score index)).expLower certificate.partition.positiveInverseLower
    (exp_lower _) (certificate.partition.positiveInverse_lower certificate.partitionLower certificate.partition_positive)

/-- Consequently a forced-zero coordinate cannot have a finite normalized
Gibbs representation on the original full grid. Passing to its feasible
face is mathematically necessary for finite parameters in this case. -/
theorem gibbs_not_zero {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (index : Fin variables) :
    ¬ Equiv (mul (neg (certificate.score index)).exp certificate.partitionInverse) zero := by
  intro vanished
  have impossible := (ofSignedRatio_le_iff _ _).mp (le_trans (certificate.gibbs_positive index) vanished.1)
  rw [SignedRatio.le_iff_cross] at impossible
  simp only [PositiveRatio.toSignedRatio, PositiveRatio.toQProb, QProb.toSignedRatio,
    SignedRatio.zero, Int.natCast_one, Int.mul_one, Int.zero_mul] at impossible
  have positive := (certificate.gibbsLower index).num_pos
  omega

end Thesis.Probability.Distros.RationalEntropyProblem.LagrangeCoefficients
