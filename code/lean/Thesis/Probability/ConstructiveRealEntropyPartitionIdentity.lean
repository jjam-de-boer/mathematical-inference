import Thesis.Probability.ConstructiveRealGibbsFamilyDerivative
import Thesis.Probability.ConstructiveRealFaceKKT

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal
open RationalLinear

/-- The exponential family of the original rational constraint responses,
with unit reference weights on distinct probability coordinates. -/
def gibbsFamily (problem : RationalEntropyProblem variables) : FiniteGibbsFamily variables problem.rows.length :=
  ⟨problem.nonempty, (fun _ => PositiveRatio.one), (fun r i => (problem.rows[r.val]).coefficients i)⟩

theorem gibbsFamily_logWeight {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (i : Fin variables) :
    Equiv ((problem.gibbsFamily.asTilt certificate.coefficient).logWeight one i) (neg (certificate.score i)) :=
  equiv_trans (add_congr (one_mul _) (positiveLn_one PositiveRatio.one (le_refl one))) (add_zero _)

theorem gibbsFamily_partition {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) :
    Equiv (problem.gibbsFamily.partition certificate.coefficient) certificate.partition :=
  listSum_map_congr (List.finRange variables) _ _ (fun i _ => exp_congr (gibbsFamily_logWeight certificate i))

theorem gibbsFamily_inverse {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) :
    Equiv ((problem.gibbsFamily.asTilt certificate.coefficient).partitionInverse one) certificate.partitionInverse :=
  positiveInverse_congr (gibbsFamily_partition certificate) _ _
    ((problem.gibbsFamily.asTilt certificate.coefficient).partition_positive one) certificate.partition_positive

/-- A natural-unit stationary law equals the independent family at its actual
coefficient vector. This connects the family calculus to the multiplier
proofs, rather than defining the family through a supplied optimum. -/
theorem RealLaw.gibbsFamily_mass {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i)))
    (i : Fin variables) : Equiv (law.mass i).value (problem.gibbsFamily.mass certificate.coefficient i) :=
  equiv_trans (gibbsForm_of_coefficients law lower positive certificate i)
    (equiv_symm (mul_congr (exp_congr (gibbsFamily_logWeight certificate i)) (gibbsFamily_inverse certificate)))

theorem RealLaw.gibbsFamily_entropy {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i))) :
    Equiv law.entropy (problem.gibbsFamily.entropy certificate.coefficient) := by
  unfold RealLaw.entropy FiniteGibbsFamily.entropy FiniteGibbsTilt.entropy realEntropySum
  simp only [List.map_map, Function.comp_def]
  exact listSum_map_congr (List.finRange variables) _ _ (fun i _ => realEntropyTerm_congr
    (law.gibbsFamily_mass lower positive certificate i) (law.mass i).nonnegative
    (problem.gibbsFamily.probability certificate.coefficient i).nonnegative (law.mass i).bounded
    (problem.gibbsFamily.probability certificate.coefficient i).bounded)

theorem RealLaw.gibbsFamily_expectation {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i)))
    (r : Fin problem.rows.length) :
    Equiv (problem.gibbsFamily.expectation certificate.coefficient (problem.gibbsFamily.feature r))
      (realRationalDot variables (problem.rows[r.val]).coefficients (fun i => (law.mass i).value)) :=
  equiv_trans (FiniteLinear.pair_congr variables _ _ _ _ (fun _ => equiv_refl _)
    (fun i => equiv_symm (law.gibbsFamily_mass lower positive certificate i)))
    (equiv_symm (realRationalDot_pair variables (problem.rows[r.val]).coefficients _))

/-- Entropy in terms of log partition, actual feature expectations
and natural multipliers. At a fitted maximum these are computed from feasibility. For interval problems, complementary
slackness permits replacing the weighted expectations by their bounds.
The bit entropy is explicitly multiplied by `ln(2)`. -/
theorem RealLaw.entropy_partition_identity {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i))) :
    Equiv (mul law.entropy lnTwo)
      (add (certificate.partition.positiveLn certificate.partitionLower certificate.partition_positive)
        (FiniteLinear.pair problem.rows.length certificate.coefficient (fun r =>
          realRationalDot variables (problem.rows[r.val]).coefficients (fun i => (law.mass i).value)))) := by
  have offsetZero : Equiv (problem.gibbsFamily.expectation certificate.coefficient problem.gibbsFamily.logReference) zero :=
    equiv_trans ((problem.gibbsFamily.asTilt certificate.coefficient).expectation_congr one _ _
      (fun i => positiveLn_one PositiveRatio.one (le_refl one)))
      ((problem.gibbsFamily.asTilt certificate.coefficient).expectation_constant one zero)
  have partitionLog := positiveLn_congr (gibbsFamily_partition certificate) _ _
    ((problem.gibbsFamily.asTilt certificate.coefficient).partition_positive one) certificate.partition_positive
  exact equiv_trans (mul_congr (law.gibbsFamily_entropy lower positive certificate) (equiv_refl _))
    (equiv_trans (problem.gibbsFamily.entropy_partition certificate.coefficient)
      (equiv_trans (add_congr (add_congr partitionLog
        (FiniteLinear.pair_congr problem.rows.length certificate.coefficient certificate.coefficient _ _ (fun _ => equiv_refl _)
          (law.gibbsFamily_expectation lower positive certificate))) (neg_congr offsetZero))
        (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _))))

end Thesis.Probability.Distros.RationalEntropyProblem
