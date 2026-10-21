import Thesis.Probability.Distros.LogExpectation
import Thesis.Probability.Distros.ShiftedMoments

namespace Thesis.Probability.Distros

/-- Affine log scores use shifted integer responses on the unchanged grid.
This covers signed integer moments without signed probability weights. -/
def logLinearScore (grid : EntropyGrid A) (constraints : List (MomentInterval A))
    (coefficient : MomentInterval A → ExactLog) (offset : ExactLog) (value : A) : ExactLog :=
  ExactLog.add offset (ExactLog.listSum (constraints.map (fun constraint =>
    ExactLog.scaleNat (grid.shiftedResponse constraint.response value) (coefficient constraint))))

namespace PartialMomentProblem

/-- A positive rational log-linear reference for selected exact expectation
rows. Other interval constraints may remain in the problem. The reference
need not itself be feasible; an arbitrary feasible anchor determines its
common cross entropy and hence a global entropy upper bound. -/
structure LogLinearReference [DecidableEq A] (problem : PartialMomentProblem A) where
  reference : Distro A
  support : reference.AlmostSurely (fun value => value ∈ problem.cells)
  positive : reference.GridPositive problem.entropyGrid
  constraints : List (MomentInterval A)
  listed : ∀ constraint ∈ constraints, constraint ∈ problem.intervals
  exact : ∀ constraint ∈ constraints, SignedRatio.Equiv constraint.lower constraint.upper
  coefficient : MomentInterval A → ExactLog
  offset : ExactLog
  score : ∀ value (member : value ∈ problem.cells), ExactLog.Equiv
    (ExactLog.log ⟨(reference.pmf value).den, (reference.pmf value).num,
      (reference.pmf value).den_pos, positive value member⟩)
    (logLinearScore problem.entropyGrid constraints coefficient offset value)

/-- Exact affine cross-entropy value, useful for explicit finite certificates. -/
theorem LogLinearReference.crossEntropy_affine [DecidableEq A] {problem : PartialMomentProblem A}
    (certificate : problem.LogLinearReference) (μ : Distro A)
    (support : μ.AlmostSurely (fun value => value ∈ problem.cells)) :
    ExactLog.Equiv (μ.crossEntropy certificate.reference problem.entropyGrid support certificate.support certificate.positive)
      (ExactLog.add certificate.offset (ExactLog.listSum (certificate.constraints.map (fun constraint =>
        ExactLog.scaleRatio (μ.expectNat (problem.entropyGrid.shiftedResponse constraint.response)) (certificate.coefficient constraint))))) :=
  ExactLog.equiv_trans (μ.crossEntropy_eq_logExpectation certificate.reference problem.entropyGrid support certificate.support certificate.positive
    (logLinearScore problem.entropyGrid certificate.constraints certificate.coefficient certificate.offset) certificate.score)
    (μ.logExpectation_affine problem.entropyGrid support certificate.constraints
      (fun constraint => problem.entropyGrid.shiftedResponse constraint.response) certificate.coefficient certificate.offset)

/-- Fixed exact moments force equal cross entropy for the represented affine
log score. The proof is global finite integration, with no stationarity claim. -/
theorem LogLinearReference.crossEntropy_fixed [DecidableEq A] {problem : PartialMomentProblem A}
    (certificate : problem.LogLinearReference) (μ ν : Distro A)
    (first : problem.Admissible μ) (second : problem.Admissible ν) :
    ExactLog.Equiv (μ.crossEntropy certificate.reference problem.entropyGrid first.1 certificate.support certificate.positive)
      (ν.crossEntropy certificate.reference problem.entropyGrid second.1 certificate.support certificate.positive) := by
  have firstScore := μ.crossEntropy_eq_logExpectation certificate.reference problem.entropyGrid first.1 certificate.support certificate.positive
    (logLinearScore problem.entropyGrid certificate.constraints certificate.coefficient certificate.offset) certificate.score
  have secondScore := ν.crossEntropy_eq_logExpectation certificate.reference problem.entropyGrid second.1 certificate.support certificate.positive
    (logLinearScore problem.entropyGrid certificate.constraints certificate.coefficient certificate.offset) certificate.score
  have firstIntegral := μ.logExpectation_affine problem.entropyGrid first.1 certificate.constraints
    (fun constraint => problem.entropyGrid.shiftedResponse constraint.response) certificate.coefficient certificate.offset
  have secondIntegral := ν.logExpectation_affine problem.entropyGrid second.1 certificate.constraints
    (fun constraint => problem.entropyGrid.shiftedResponse constraint.response) certificate.coefficient certificate.offset
  have same := ExactLog.add_congr (ExactLog.equiv_refl certificate.offset)
    (ExactLog.listSum_map_congr certificate.constraints _ _ (fun constraint member =>
      ExactLog.scaleRatio_weight_congr
        (constraint.shiftedMean_congr μ ν problem.entropyGrid first.1 second.1
          (constraint.mean_eq_of_exact μ ν (certificate.exact constraint member)
            (first.2 constraint (certificate.listed constraint member))
            (second.2 constraint (certificate.listed constraint member)))) (certificate.coefficient constraint)))
  exact ExactLog.equiv_trans firstScore (ExactLog.equiv_trans firstIntegral
    (ExactLog.equiv_trans same (ExactLog.equiv_trans (ExactLog.equiv_symm secondIntegral) (ExactLog.equiv_symm secondScore))))

/-- A log-linear reference gives a universal entropy upper bound even when
its own expectation is different from the constrained target expectation. -/
theorem LogLinearReference.entropy_upper [DecidableEq A] {problem : PartialMomentProblem A}
    (certificate : problem.LogLinearReference) (anchor : problem.CompatibleLaw) (μ : Distro A)
    (valid : problem.Admissible μ) :
    ExactLog.LE (μ.entropy problem.entropyGrid valid.1)
      (anchor.distro.crossEntropy certificate.reference problem.entropyGrid anchor.support certificate.support certificate.positive) := by
  have upper := μ.entropy_le_crossEntropy certificate.reference problem.entropyGrid valid.1 certificate.support certificate.positive
  exact (ExactLog.le_congr (ExactLog.equiv_refl _)
    (certificate.crossEntropy_fixed μ anchor.distro valid ⟨anchor.support, anchor.moments⟩)).mp upper

/-- A representable positive log-linear reference that is itself feasible
is a global maximum. No exact rational existence assertion is imposed. -/
theorem LogLinearReference.optimal [DecidableEq A] {problem : PartialMomentProblem A}
    (certificate : problem.LogLinearReference)
    (feasible : problem.Admissible certificate.reference) (μ : Distro A) (valid : problem.Admissible μ) :
    ExactLog.LE (μ.entropy problem.entropyGrid valid.1) (certificate.reference.entropy problem.entropyGrid feasible.1) ∧
    (ExactLog.Equiv (μ.entropy problem.entropyGrid valid.1) (certificate.reference.entropy problem.entropyGrid feasible.1) ↔
      μ.SameLaw certificate.reference) := by
  have fixed := certificate.crossEntropy_fixed μ certificate.reference valid feasible
  exact ⟨μ.entropy_le_of_crossEntropy_eq certificate.reference problem.entropyGrid valid.1 certificate.support certificate.positive fixed,
    μ.entropy_eq_of_crossEntropy_eq_iff certificate.reference problem.entropyGrid valid.1 certificate.support certificate.positive fixed⟩

end PartialMomentProblem
end Thesis.Probability.Distros
