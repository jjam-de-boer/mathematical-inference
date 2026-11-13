import Thesis.Probability.ConstructiveRealEntropyOptimizer
import Thesis.Probability.Distros.LogLinearEntropy

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

/-- The established exact rational log-linear certificate also bounds all
feasible analytic laws. Exact-feasible entropy density extends its global
bound, including irrational and boundary competitors, without changing the
rational `Distro` interface or assuming a real optimum. -/
theorem LogLinearReference.real_optimal [DecidableEq A] {problem : PartialMomentProblem A}
    (certificate : problem.LogLinearReference) (feasible : problem.Admissible certificate.reference)
    (law : problem.RealCompatibleLaw) :
    LE law.entropy (certificate.reference.entropy problem.entropyGrid feasible.1).interpret := by
  apply law.entropy_le_of_rational_bound
  intro rational
  exact ExactLog.interpret_mono (certificate.optimal feasible rational.distro ⟨rational.support, rational.moments⟩).1

/-- When the existing positive reference is presented as a retained-grid
compatible law, its analytic embedding is an attained global maximum. -/
theorem LogLinearReference.real_maximal [DecidableEq A] {problem : PartialMomentProblem A}
    (certificate : problem.LogLinearReference) (feasible : problem.Admissible certificate.reference)
    (reference : problem.CompatibleLaw) (same : reference.distro = certificate.reference) : reference.toReal.Maximal := by
  intro law
  have represented : Equiv reference.toReal.entropy (certificate.reference.entropy problem.entropyGrid feasible.1).interpret := by
    simpa only [same] using reference.toReal_entropy
  exact (le_congr (equiv_refl _) (equiv_symm represented)).mp (certificate.real_optimal feasible law)

theorem LogLinearReference.real_maximal_unique [DecidableEq A] {problem : PartialMomentProblem A}
    (certificate : problem.LogLinearReference) (feasible : problem.Admissible certificate.reference)
    (reference : problem.CompatibleLaw) (same : reference.distro = certificate.reference)
    (law : problem.RealCompatibleLaw) (maximal : law.Maximal) (index : Fin problem.cells.length) :
    Equiv (law.mass index).value (reference.toReal.mass index).value :=
  law.maximal_unique reference.toReal maximal (certificate.real_maximal feasible reference same) index

end Thesis.Probability.Distros.PartialMomentProblem
