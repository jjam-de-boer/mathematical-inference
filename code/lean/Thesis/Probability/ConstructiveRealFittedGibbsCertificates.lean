import Thesis.Probability.ConstructiveRealEntropyPartitionIdentity

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal
open RationalLinear

/-- Complementarity replaces weighted feature expectations by weighted row
bounds, including intervals with nonzero slack and zero multiplier. -/
theorem LagrangeCoefficients.KKTAt.weighted_expectations {problem : RationalEntropyProblem variables}
    {gradient : Fin variables → ConstructiveReal} {certificate : problem.LagrangeCoefficients gradient}
    {law : problem.RealLaw} (kkt : certificate.KKTAt law) :
    Equiv (FiniteLinear.pair problem.rows.length certificate.coefficient (fun r =>
      realRationalDot variables (problem.rows[r.val]).coefficients (fun i => (law.mass i).value)))
      (realRationalDot problem.rows.length (fun r => (problem.rows[r.val]).bound) certificate.coefficient) := by
  have weighted := listSum_map_congr (List.finRange problem.rows.length) _ _ (fun r _ => by
    have canceled := (sub_equiv_zero_iff _ _).mp (equiv_trans (equiv_symm (mul_sub _ _ _)) (kkt.complementary r))
    exact equiv_symm canceled)
  exact equiv_trans weighted (equiv_trans (FiniteLinear.pair_comm problem.rows.length _ _)
    (equiv_symm (realRationalDot_pair problem.rows.length _ certificate.coefficient)))

theorem RealLaw.entropy_partition_bounds {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i)))
    (kkt : certificate.KKTAt law) :
    Equiv (mul law.entropy lnTwo)
      (add (certificate.partition.positiveLn certificate.partitionLower certificate.partition_positive)
        (realRationalDot problem.rows.length (fun r => (problem.rows[r.val]).bound) certificate.coefficient)) :=
  equiv_trans (law.entropy_partition_identity lower positive certificate)
    (add_congr (equiv_refl _) kkt.weighted_expectations)

/-- The computed natural-unit KKT parameter vector of the actual ideal
maximum. Each coordinate has the standard certified rational enclosure
interface, although the vector and the resulting ideal probabilities need
not be exactly rational. -/
def RealLaw.fittedParameters {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) :
    Fin problem.rows.length → ConstructiveReal := (feasible.fittedNaturalKKT lower positive).val.coefficient

def RealLaw.fittedParameterEnclosure {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value)
    (r : Fin problem.rows.length) (precision : PositiveRatio) : RationalEnclosure precision :=
  (feasible.fittedParameters lower positive r).enclose precision

/-- Every returned interval has its stored rational width guarantee and
bounds the actual fitted coefficient, which is also proved nonnegative.
No equality decision or rational-representability claim is made. -/
theorem RealLaw.fittedParameter_bounds {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value)
    (r : Fin problem.rows.length) (precision : PositiveRatio) :
    LE (ofSignedRatio (feasible.fittedParameterEnclosure lower positive r precision).lower) (feasible.fittedParameters lower positive r) ∧
    LE (feasible.fittedParameters lower positive r) (ofSignedRatio (feasible.fittedParameterEnclosure lower positive r precision).upper) ∧
    LE zero (feasible.fittedParameters lower positive r) :=
  ⟨(feasible.fittedParameters lower positive r).lower_bound precision,
    (feasible.fittedParameters lower positive r).upper_bound precision, (feasible.fittedNaturalKKT lower positive).property.nonnegative r⟩

/-- An exactly feasible rational approximation to the fitted Gibbs law.
This uses the existing constraint-preserving density algorithm; it does
not independently round exponential probabilities or multiplier coordinates. -/
def RealLaw.fittedRationalGibbs {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (precision : PositiveRatio) :
    {rational : Distro (Fin variables) //
      (∀ row ∈ problem.rows, row.Holds (fun i => (rational.pmf i).toSignedRatio)) ∧
      (∀ i, ∃ weight, (i, weight) ∈ rational.record.atoms) ∧
      ∀ i, Within precision.toQProb (problem.gibbsFamily.mass (feasible.fittedParameters lower positive) i)
        (ofSignedRatio (rational.pmf i).toSignedRatio)} := by
  let approximation := feasible.maximize.approximate precision
  refine ⟨approximation.val, approximation.property.1, approximation.property.2.1, ?_⟩
  intro i
  exact (within_congr (feasible.maximize.gibbsFamily_mass (fun i => interiorLower variables (lower i))
    (feasible.maximize_positive lower positive) (feasible.fittedNaturalKKT lower positive).val i) (equiv_refl _)).mp (approximation.property.2.2 i)

/-- Universal rational entropy certificates bound the actual fitted ideal
family. The certificate's own rational candidate continues to satisfy every
original row exactly, by `RealLaw.certifyEntropy_valid`. -/
theorem RealLaw.fittedFamily_certificate_bound {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value)
    (tolerance : QProb) (tolerancePositive : 0 < tolerance.num) :
    LE (problem.gibbsFamily.entropy (feasible.fittedParameters lower positive))
      (ofSignedRatio (feasible.certifyEntropy tolerance tolerancePositive).upper.toSignedRatio) :=
  (le_congr (feasible.maximize.gibbsFamily_entropy (fun i => interiorLower variables (lower i))
    (feasible.maximize_positive lower positive) (feasible.fittedNaturalKKT lower positive).val) (equiv_refl _)).mp
    (certificate_global_bound (feasible.certifyEntropy tolerance tolerancePositive) feasible.maximize)

end Thesis.Probability.Distros.RationalEntropyProblem
