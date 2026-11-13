import Thesis.Causality.EndpointSemantics
import Thesis.Causality.ModalRealization
import Thesis.Causality.ModalCounterfactual

namespace Thesis
namespace Causality

open Probability

/-!
Agreement of current-state endpoint semantics with the concrete do, AAP and
counterfactual executions used elsewhere in the development.

These theorems do not assert completeness for arbitrary histories.  They show
that the histories already constructed by the thesis are read through the
same endpoint-record semantics.
-/

namespace KernelOperationRealization

variable {S : ObservedSignature} {model : ExactModel S}
  {kernel : Kernel S} {reference : S.Assignment}

/--
The value carried by a supported do-calculus kernel is also the value obtained
by evaluating that kernel at its initial epistemic mode.
-/
noncomputable def endpointDenotation
    (realization : KernelOperationRealization model kernel reference) :
    ProbabilityResult.Equivalent
      (kernel.endpointDenote (CausalEpistemicRecord.initial model) reference)
      (some realization.value) :=
  ProbabilityResult.trans
    (kernel.endpointDenote_initial model reference)
    realization.denotation

end KernelOperationRealization

namespace AbductionActionPrediction

/-- The generic endpoint query read after abduction and atomic action. -/
noncomputable def endpointQuery
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    EndpointQuery
      (atomicAction M evidence hEvidence intervention).signature :=
  EndpointQuery.unconditional
    (AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointEvent
      (atomicAction M evidence hEvidence intervention) outcome)

/-- Evaluate AAP through the generic endpoint-record semantics. -/
noncomputable def endpointDenote
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    ProbabilityResult.Result :=
  (endpointQuery M evidence hEvidence intervention outcome).denote
    (actedRecord M evidence hEvidence intervention)

noncomputable def endpointDenote_eq_prediction
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    ProbabilityResult.Equivalent
      (endpointDenote M evidence hEvidence intervention outcome)
      (some (prediction M evidence hEvidence intervention outcome)) := by
  simpa [endpointDenote, endpointQuery, prediction] using
    (EndpointQuery.unconditional_denote
      (actedRecord M evidence hEvidence intervention)
      (AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointEvent
        (atomicAction M evidence hEvidence intervention) outcome))

/--
The single-action counterfactual query and modal AAP are two presentations of
the same generic endpoint denotation.
-/
noncomputable def endpointDenote_eq_singleAction
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    ProbabilityResult.Equivalent
      (endpointDenote M evidence hEvidence intervention outcome)
      ((CounterfactualQuery.singleAction
        evidence intervention outcome).denote M) :=
  ProbabilityResult.trans
    (endpointDenote_eq_prediction M evidence hEvidence intervention outcome)
    (ProbabilityResult.symm
      (singleAction_query_eq_prediction M evidence hEvidence
        intervention outcome))

end AbductionActionPrediction

namespace ModalCombinedCounterfactualConstruction

/-- Numerator and denominator events on the actual from-factual endpoint. -/
noncomputable def endpointQuery
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    EndpointQuery construction.fromFactual.signature where
  numerator :=
    construction.fromFactual.endpointEvent
      (query.combinedNumeratorPredicate construction.fromFactual.World)
  denominator :=
    construction.fromFactual.endpointEvent
      (query.combinedConditionPredicate construction.fromFactual.World)

/-- Generic endpoint semantics along the construction's proof-carrying path. -/
noncomputable def pathEndpointDenote
  (construction : ModalCombinedCounterfactualConstruction mode query) :
    ProbabilityResult.Result :=
  construction.fromFactual.probabilityPath.endpointDenote
    construction.endpointQuery

theorem pathEndpointDenote_eq
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    construction.pathEndpointDenote = construction.endpointDenote := by
  rfl

/--
The arbitrary finite counterfactual construction is therefore interpreted by
the same endpoint semantics before it is compared with the independent query
language.
-/
noncomputable def pathEndpoint_semanticAgreement
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    ProbabilityResult.Equivalent construction.pathEndpointDenote
      (query.denote mode.record.model) := by
  rw [construction.pathEndpointDenote_eq]
  exact construction.semanticAgreement

end ModalCombinedCounterfactualConstruction

end Causality
end Thesis
