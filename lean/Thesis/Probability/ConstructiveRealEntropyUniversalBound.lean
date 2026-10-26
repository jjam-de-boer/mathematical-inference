import Thesis.Probability.ConstructiveRealEntropyCertificates

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

/-- Any universal rational entropy upper bound extends to every feasible
analytic law by exact-feasible entropy density. The bound may itself be an
analytic value; no rational enclosure or strict positivity is required. -/
theorem RealCompatibleLaw.entropy_le_of_rational_bound [DecidableEq A] {problem : PartialMomentProblem A}
    (law : problem.RealCompatibleLaw) (upper : ConstructiveReal)
    (bounded : ∀ rational : problem.CompatibleLaw,
      LE (rational.distro.entropy problem.entropyGrid rational.support).interpret upper) :
    LE law.entropy upper := by
  apply le_of_forall_rational_error
  intro precision
  let approximation := law.approximateEntropy precision
  exact le_trans approximation.property.1 (add_le_add (bounded approximation.val) (le_refl _))

/-- The executable rational solver's symbolic gap also bounds all ideal
feasible laws, including boundary laws with irrational coordinates. -/
theorem EntropyApproximation.real_upper [DecidableEq A] {problem : PartialMomentProblem A} {tolerance : QProb}
    (approximation : problem.EntropyApproximation tolerance) (law : problem.RealCompatibleLaw) :
    LE law.entropy (add approximation.law.toReal.entropy (ofSignedRatio tolerance.toSignedRatio)) := by
  apply law.entropy_le_of_rational_bound
  intro rational
  have compared := ExactLog.interpret_mono (approximation.upper rational.distro ⟨rational.support, rational.moments⟩)
  have collected := equiv_trans (ExactLog.interpret_add _ (ExactLog.ofSignedRatio tolerance.toSignedRatio))
    (add_congr (equiv_symm approximation.law.toReal_entropy) (ExactLog.interpret_ofSignedRatio tolerance.toSignedRatio))
  exact (le_congr (equiv_refl _) collected).mp compared

end Thesis.Probability.Distros.PartialMomentProblem
