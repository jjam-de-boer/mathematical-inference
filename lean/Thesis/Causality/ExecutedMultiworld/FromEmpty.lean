import Thesis.Causality.ExecutedMultiworld.EmptyConstruction

namespace Thesis
namespace Causality

open Probability

/-! Complete probability-bearing multiworld execution from an empty mode. -/

/--
The complete empty-origin execution.  Its endpoint is obtained solely by the
record transformations in its path; the occurrence model is retained only as
an independent semantic reference.
-/
structure FromEmptyExecutedOccurrenceConstruction
    (mode : CausalMode S) (event : CounterfactualEvent S) where
  linked : EmptyOccurrenceConstruction.Linked mode.record.model event
  linked_eq :
    linked =
      EmptyOccurrenceConstruction.Linked.build mode.record.model event
  atomic :
    AtomicIntervention.Execution linked.reindexBeliefTransition.target
  atomic_eq :
    atomic = AtomicIntervention.compile linked.reindexBeliefTransition.target
      linked.combinedAction

namespace FromEmptyExecutedOccurrenceConstruction

noncomputable def canonical (mode : CausalMode S)
    (event : CounterfactualEvent S) :
    FromEmptyExecutedOccurrenceConstruction mode event :=
  let linked :=
    EmptyOccurrenceConstruction.Linked.build mode.record.model event
  { linked := linked
    linked_eq := rfl
    atomic := AtomicIntervention.compile linked.reindexBeliefTransition.target
      linked.combinedAction
    atomic_eq := rfl }

/-- Root/node creation and causal linkage preserve the empty mode's override. -/
theorem linked_noActiveIntervention
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.NoActiveIntervention construction.linked.target := by
  rw [construction.linked_eq]
  exact EmptyOccurrenceConstruction.Linked.build_noActiveIntervention
    mode.record.model event

/-- Equation configuration preserves the from-empty route's empty override. -/
theorem configured_noActiveIntervention
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.NoActiveIntervention
      construction.linked.configureTransition.target :=
  AtomicIntervention.mechanismReplacement_noActiveIntervention
    construction.linked.target construction.linked.configureOperation
    "configure-empty-occurrence-equations"
    construction.linked_noActiveIntervention

/-- Prior reindexing preserves the empty override before atomic compilation. -/
theorem atomicSource_noActiveIntervention
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.NoActiveIntervention
      construction.linked.reindexBeliefTransition.target :=
  AtomicIntervention.beliefReindexing_noActiveIntervention
    construction.linked.configureTransition.target
    construction.linked.reindexBeliefOperation
    "reindex-empty-occurrence-belief"
    construction.configured_noActiveIntervention

abbrev World
    {S : ObservedSignature} {mode : CausalMode S}
    {event : CounterfactualEvent S}
    (_construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    OccurrenceMultiworld S event :=
  mode.record.model.occurrenceMultiworld event

abbrev signature
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    ObservedSignature :=
  construction.atomic.signature

abbrev target
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    CausalMode construction.signature :=
  construction.atomic.target

def path
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    CausalEditPath EmptyCausalMode.mode construction.target :=
  construction.linked.path.append
    ((CausalEditPath.single construction.linked.configureTransition).append
      ((CausalEditPath.single
        construction.linked.reindexBeliefTransition).append
        construction.atomic.path))

def coordinates
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.SameCoordinates
      (OccurrenceMultiworld.Encoding.signature construction.World)
      construction.signature :=
  construction.linked.coordinates.trans construction.atomic.coordinates

noncomputable def realizes
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation
      construction.atomic
      (fun assignment =>
        construction.linked.configuredModel.evalUnder
          construction.linked.combinedAction assignment) := by
  rw [construction.atomic_eq]
  exact AtomicIntervention.compileDeterministicRealizes
    construction.linked.reindexBeliefTransition.target
    construction.linked.combinedAction

theorem atomicTarget_noActiveIntervention
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.NoActiveIntervention construction.atomic.target := by
  rw [construction.atomic_eq]
  exact AtomicIntervention.compile_noActiveIntervention
    construction.linked.reindexBeliefTransition.target
    construction.linked.combinedAction
    construction.atomicSource_noActiveIntervention

/-- Certified absorption evidence for from-empty endpoint clearing. -/
noncomputable def endpointInterventionAbsorbed
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation.EndpointInterventionAbsorbed
      construction.realizes :=
  AtomicIntervention.Execution.DeterministicRealizesEvaluation.EndpointInterventionAbsorbed.ofEmpty
    construction.realizes construction.atomicTarget_noActiveIntervention

/-- Close the from-empty atomic program at its probability-bearing target. -/
noncomputable def probabilityExecution
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.Execution
      construction.linked.reindexBeliefTransition.target :=
  construction.realizes.canonicalExecution
    construction.endpointInterventionAbsorbed

noncomputable def probabilityRealizes
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation
      construction.probabilityExecution
      (fun assignment =>
        construction.linked.configuredModel.evalUnder
          construction.linked.combinedAction assignment) :=
  construction.realizes.canonicalRealizes
    construction.endpointInterventionAbsorbed

noncomputable def probabilityTarget
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    CausalMode construction.signature :=
  construction.probabilityExecution.target

noncomputable def probabilityPath
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    CausalEditPath EmptyCausalMode.mode construction.probabilityTarget :=
  construction.path.append
    (CausalEditPath.single
      (construction.realizes.endpointTransition
        construction.endpointInterventionAbsorbed))

/--
The complete from-empty endpoint belief is the source prior pushed through the
explicitly created root coordinates and then through atomic compilation.
-/
@[simp] theorem probabilityTarget_belief_provenance
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    construction.probabilityTarget.record.belief =
      (mode.record.model.prior.map construction.linked.rootAssignment).map
        construction.realizes.assignment :=
  rfl

noncomputable def endpointAssignment
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (assignment : mode.record.model.latent.Assignment) :
    construction.target.record.model.latent.Assignment :=
  construction.realizes.assignment
    (construction.linked.rootAssignment assignment)

theorem endpoint_eval
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (assignment : mode.record.model.latent.Assignment) :
    construction.target.record.model.eval
        (construction.endpointAssignment assignment) =
      construction.coordinates.transportObserved
        (OccurrenceMultiworld.Encoding.encodeAssignment construction.World
          (construction.World.eval assignment)) := by
  have acted := construction.realizes.evaluate
    (construction.linked.rootAssignment assignment)
  rw [construction.linked.configured_evalUnder_eq_reference assignment] at acted
  exact acted.trans
    (AtomicIntervention.SameCoordinates.transportObserved_trans
      construction.linked.coordinates construction.atomic.coordinates
      (OccurrenceMultiworld.Encoding.encodeAssignment construction.World
        (construction.World.eval assignment)))

theorem endpoint_decodedAssignment
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (assignment : mode.record.model.latent.Assignment) :
    OccurrenceMultiworld.Encoding.decodeAssignment construction.World
        (construction.coordinates.untransportObserved
          (construction.target.record.model.eval
            (construction.endpointAssignment assignment))) =
      construction.World.eval assignment := by
  rw [construction.endpoint_eval]
  rw [AtomicIntervention.SameCoordinates.untransportObserved_transportObserved]
  exact OccurrenceMultiworld.Encoding.decodeAssignment_encodeAssignment
    construction.World (construction.World.eval assignment)

theorem endpoint_counterfactualOccurrence
    {S : ObservedSignature} {mode : CausalMode S}
    {event : CounterfactualEvent S}
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (assignment : mode.record.model.latent.Assignment)
    (occurrence : Fin event.atoms.length) (node : Fin S.count) :
    OccurrenceMultiworld.Encoding.decodeAssignment construction.World
        (construction.coordinates.untransportObserved
          (construction.target.record.model.eval
            (construction.endpointAssignment assignment)))
        ⟨.counterfactual occurrence, node⟩ =
      mode.record.model.evalUnder
        (event.atoms.get occurrence).action assignment node := by
  rw [construction.endpoint_decodedAssignment]
  rfl

noncomputable def endpointRecord
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    CausalEpistemicRecord construction.signature :=
  construction.probabilityTarget.record

@[simp] theorem endpointRecord_is_probabilityTarget
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    construction.endpointRecord = construction.probabilityTarget.record :=
  rfl

theorem endpointRecord_probabilityTarget
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (eventAtTarget : construction.signature.Assignment -> Bool) :
    QProb.Equiv
      (construction.endpointRecord.observedValue eventAtTarget)
      (construction.probabilityTarget.record.observedValue eventAtTarget) :=
  QProb.equiv_refl _

def configuredEvent
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (predicate : construction.World.Assignment -> Bool) :
    construction.linked.signature.Assignment -> Bool :=
  fun assignment =>
    predicate
      (OccurrenceMultiworld.Encoding.decodeAssignment construction.World
        (construction.linked.coordinates.untransportObserved assignment))

def endpointEvent
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (predicate : construction.World.Assignment -> Bool) :
    construction.signature.Assignment -> Bool :=
  AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointEvent
    construction.atomic (construction.configuredEvent predicate)

theorem configuredEvent_eval
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (predicate : construction.World.Assignment -> Bool)
    (assignment : mode.record.model.latent.Assignment) :
    construction.configuredEvent predicate
        (construction.linked.configuredModel.evalUnder
          construction.linked.combinedAction
          (construction.linked.rootAssignment assignment)) =
      predicate (construction.World.eval assignment) := by
  unfold configuredEvent
  rw [construction.linked.configured_evalUnder_eq_reference assignment]
  rw [AtomicIntervention.SameCoordinates.untransportObserved_transportObserved]
  change
    predicate
        (OccurrenceMultiworld.Encoding.decodeAssignment construction.World
          (OccurrenceMultiworld.Encoding.encodeAssignment construction.World
            (construction.World.eval assignment))) =
      predicate (construction.World.eval assignment)
  exact congrArg predicate
    (OccurrenceMultiworld.Encoding.decodeAssignment_encodeAssignment
      construction.World (construction.World.eval assignment))

theorem endpointRecord_observedValue
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (predicate : construction.World.Assignment -> Bool) :
    QProb.Equiv
      (construction.endpointRecord.observedValue
        (construction.endpointEvent predicate))
      (construction.World.jointDist.probVal predicate) := by
  exact QProb.equiv_trans
    (AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointRecord_observedValue
      construction.realizes
      (construction.configuredEvent predicate))
    (QProb.equiv_trans
      (FiniteProbRecord.map_probVal mode.record.model.prior
        construction.linked.rootAssignment
        (fun assignment =>
          construction.configuredEvent predicate
            (construction.linked.configuredModel.evalUnder
              construction.linked.combinedAction assignment)))
      (QProb.equiv_trans
        (FiniteProbRecord.probVal_congr mode.record.model.prior _ _
          (fun assignment =>
            construction.configuredEvent_eval predicate assignment))
        (QProb.equiv_symm
          (FiniteProbRecord.map_probVal mode.record.model.prior
            construction.World.eval predicate))))

variable {S : ObservedSignature} {mode : CausalMode S}
  {query : CounterfactualQuery S}

noncomputable def denominator
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb :=
  construction.endpointRecord.observedValue
    (construction.endpointEvent
      (query.combinedConditionPredicate construction.World))

noncomputable def numerator
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb :=
  construction.endpointRecord.observedValue
    (construction.endpointEvent
      (query.combinedNumeratorPredicate construction.World))

noncomputable def denote
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    ProbabilityResult.Result :=
  ProbabilityResult.divide (some construction.numerator)
    (some construction.denominator)

theorem denominator_equiv
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv construction.denominator
      (query.denominator mode.record.model) := by
  exact QProb.equiv_trans
    (construction.endpointRecord_observedValue
      (query.combinedConditionPredicate construction.World))
    (QProb.equiv_trans
      (FiniteProbRecord.map_probVal mode.record.model.prior
        construction.World.eval
        (query.combinedConditionPredicate construction.World))
      (FiniteProbRecord.probVal_congr mode.record.model.prior _ _
        (fun assignment =>
          query.combinedConditionPredicate_eval
            construction.World assignment)))

theorem numerator_equiv
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv construction.numerator
      (query.numerator mode.record.model) := by
  exact QProb.equiv_trans
    (construction.endpointRecord_observedValue
      (query.combinedNumeratorPredicate construction.World))
    (QProb.equiv_trans
      (FiniteProbRecord.map_probVal mode.record.model.prior
        construction.World.eval
        (query.combinedNumeratorPredicate construction.World))
      (FiniteProbRecord.probVal_congr mode.record.model.prior _ _
        (fun assignment =>
          query.combinedNumeratorPredicate_eval
            construction.World assignment)))

noncomputable def semanticAgreement
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    ProbabilityResult.Equivalent construction.denote
      (query.denote mode.record.model) :=
  ProbabilityResult.divide_congr
    (.value construction.numerator_equiv)
    (.value construction.denominator_equiv)

end FromEmptyExecutedOccurrenceConstruction

end Causality
end Thesis
