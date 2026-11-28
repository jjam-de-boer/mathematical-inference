import Thesis.CausalTransport.CatalogueIIDSymmetry
import Thesis.Examples.InferenceWorkflowSymmetry

/-! # IID relabelling on the two-model inference catalogue -/

namespace Thesis.Causality.Examples.CatalogueIIDSymmetry

open Probability Probability.Distros BinaryBow
open Causality.CatalogueInference
open Examples.CatalogueInference Examples.CatalogueSampling Examples.InferenceWorkflowSymmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The library action computes the same complete cohort as the hand-built
fixture, including the intervention tag and all four histogram cells. -/
theorem generic_flip_successExperiment :
    (CountExperiment.actionOf modelFamily.outcomes modelFamily.experiments).act true
      successExperiment = failureExperiment := by
  have counts : (sixSuccesses.rename modelFamily.outcomes true).bins = sixFailures.bins := by
    decide +kernel
  change CountExperiment.mk (.intervene (transformIntervention true doX))
      (sixSuccesses.rename modelFamily.outcomes true) = CountExperiment.mk (.intervene doXFalse) sixFailures
  rw [flip_doX, CountSample.eq_of_bins_eq counts]

theorem generic_cohort_likelihoods_unchanged (hypothesis : Fin 2) :
    QProb.Equiv (iidModelCountLikelihood (twoModels hypothesis) failureExperiment)
      (iidModelCountLikelihood (twoModels hypothesis) successExperiment) := by
  have transported := iidCountLikelihood_equivariant modelFamily true hypothesis successExperiment
  rw [generic_flip_successExperiment] at transported
  exact transported

/-- One observation with X=false under do(X=true) exhausts the catalogue.
A coherent flip still produces a cohort that contradicts its setting. -/
private def contradictsSetting : CountExperiment signature :=
  ⟨.intervene doX, CountSample.ofCounts (fun sample =>
    if !(sample x) && !(sample y) then 1 else 0)⟩

/-- Both versions of the contradictory cohort exhaust the actual posterior. -/
theorem unsupported_cohorts :
    (iidModelPosterior? twoCatalogue [contradictsSetting]).isNone = true ∧
    (iidModelPosterior? twoCatalogue
      [(CountExperiment.actionOf modelFamily.outcomes modelFamily.experiments).act true
        contradictsSetting]).isNone = true := by
  constructor <;> decide +kernel

end Thesis.Causality.Examples.CatalogueIIDSymmetry
