import Thesis.Causality.ExecutedMultiworld.EmptyConstruction
import Thesis.Causality.ExecutedMultiworld.Endpoint

namespace Thesis
namespace Causality

open Probability

/-!
Complete probability-bearing multiworld execution from an empty mode.

`EmptyOccurrenceConstruction.Linked` builds the required finite model from
`EmptyCausalMode.mode`; this module closes that construction with the same
atomic action compiler used by the from-factual route. The endpoint is an
actual causal record with its own dependent signature, so comparisons with the
reference use explicit coordinate transport. Besides evaluator and probability
agreement, the construction proves that both its atomic target and its final
probability-bearing target have exactly the reference directed and latent
classifiers, with no additional edges or incidences.
-/

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

/-- The source-root equivalence through recreation and atomic compilation. -/
def rootEquiv
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.FinIndexEquiv mode.record.model.latent.count
      construction.target.record.model.latent.count :=
  construction.linked.sourceRootEquiv.trans construction.atomic.roots.rootEquiv

/-- Transport a recreated source root through the final atomic program. -/
def sourceRoot
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (root : Fin mode.record.model.latent.count) :
    Fin construction.target.record.model.latent.count :=
  construction.rootEquiv.toFun root

theorem sourceRoot_surjective
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (targetRoot : Fin construction.target.record.model.latent.count) :
    Exists fun root : Fin mode.record.model.latent.count =>
      construction.sourceRoot root = targetRoot :=
  ⟨construction.rootEquiv.invFun targetRoot,
    construction.rootEquiv.right_inv targetRoot⟩

/-- The actual from-empty atomic target has exactly the reference directed graph. -/
theorem target_directed_eq_reference
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (parent child : Fin
      (OccurrenceMultiworld.Encoding.signature construction.World).count) :
    construction.signature.directed
        (construction.coordinates.nodeEquiv.toFun parent)
        (construction.coordinates.nodeEquiv.toFun child) =
      construction.World.directed
        (OccurrenceMultiworld.Encoding.decode parent)
        (OccurrenceMultiworld.Encoding.decode child) := by
  have compiled := AtomicIntervention.compile_directed_eq
    construction.linked.reindexBeliefTransition.target
    construction.linked.combinedAction
    (construction.linked.coordinates.nodeEquiv.toFun parent)
    (construction.linked.coordinates.nodeEquiv.toFun child)
  rw [← construction.atomic_eq] at compiled
  have actionEq := construction.linked.combinedAction_encodedNode_isSome child
  have sourceEq := construction.linked.directed_eq_untreated parent child
  have referenceEq := EmptyOccurrenceConstruction.Linked.world_directed_encoded_eq
    mode.record.model event parent child
  change construction.atomic.signature.directed
      (construction.atomic.coordinates.nodeEquiv.toFun
        (construction.linked.encodedNode parent))
      (construction.atomic.coordinates.nodeEquiv.toFun
        (construction.linked.encodedNode child)) =
    if (construction.linked.combinedAction
        (construction.linked.encodedNode child)).isSome then false
    else construction.linked.signature.directed
      (construction.linked.encodedNode parent)
      (construction.linked.encodedNode child) at compiled
  rw [actionEq, sourceEq] at compiled
  change construction.atomic.signature.directed
      (construction.atomic.coordinates.nodeEquiv.toFun
        (construction.linked.encodedNode parent))
      (construction.atomic.coordinates.nodeEquiv.toFun
        (construction.linked.encodedNode child)) = _
  exact compiled.trans referenceEq.symm

/-- The actual from-empty atomic target has exactly the reference latent graph. -/
theorem target_incident_eq_reference
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (root : Fin mode.record.model.latent.count)
    (child : Fin
      (OccurrenceMultiworld.Encoding.signature construction.World).count) :
    construction.target.record.model.latent.incident
        (construction.sourceRoot root)
        (construction.coordinates.nodeEquiv.toFun child) =
      construction.World.incident root
        (OccurrenceMultiworld.Encoding.decode child) := by
  have compiled := AtomicIntervention.compile_latent_incident_eq
    construction.linked.reindexBeliefTransition.target
    construction.linked.combinedAction
    (construction.linked.sourceRoot root)
    (construction.linked.coordinates.nodeEquiv.toFun child)
  rw [← construction.atomic_eq] at compiled
  have actionEq := construction.linked.combinedAction_encodedNode_isSome child
  have sourceEq := construction.linked.incident_eq_source root child
  have referenceEq := EmptyOccurrenceConstruction.Linked.world_incident_encoded_eq
    mode.record.model event root child
  change construction.atomic.target.record.model.latent.incident
      (construction.atomic.roots.rootEquiv.toFun
        (construction.linked.sourceRoot root))
      (construction.atomic.coordinates.nodeEquiv.toFun
        (construction.linked.encodedNode child)) =
    if (construction.linked.combinedAction
        (construction.linked.encodedNode child)).isSome then false
    else construction.linked.target.record.model.latent.incident
      (construction.linked.sourceRoot root)
      (construction.linked.encodedNode child) at compiled
  rw [actionEq, sourceEq] at compiled
  change construction.atomic.target.record.model.latent.incident
      (construction.atomic.roots.rootEquiv.toFun
        (construction.linked.sourceRoot root))
      (construction.atomic.coordinates.nodeEquiv.toFun
        (construction.linked.encodedNode child)) = _
  exact compiled.trans referenceEq.symm

theorem target_directed_eq_true_iff
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (parent child : Fin
      (OccurrenceMultiworld.Encoding.signature construction.World).count) :
    construction.signature.directed
          (construction.coordinates.nodeEquiv.toFun parent)
          (construction.coordinates.nodeEquiv.toFun child) = true ↔
      construction.World.directed
          (OccurrenceMultiworld.Encoding.decode parent)
          (OccurrenceMultiworld.Encoding.decode child) = true := by
  rw [construction.target_directed_eq_reference]

theorem target_incident_eq_true_iff
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (root : Fin mode.record.model.latent.count)
    (child : Fin
      (OccurrenceMultiworld.Encoding.signature construction.World).count) :
    construction.target.record.model.latent.incident
          (construction.sourceRoot root)
          (construction.coordinates.nodeEquiv.toFun child) = true ↔
      construction.World.incident root
          (OccurrenceMultiworld.Encoding.decode child) = true := by
  rw [construction.target_incident_eq_reference]

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

noncomputable def probabilityTarget
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    CausalMode construction.signature :=
  construction.probabilityExecution.target

/-- Probability closure changes only belief and the compact-intervention field. -/
@[simp] theorem probabilityTarget_model_eq_target
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    construction.probabilityTarget.record.model =
      construction.target.record.model :=
  rfl

/-- The probability-bearing endpoint retains the exact reference directed graph. -/
theorem probabilityTarget_directed_eq_reference
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (parent child : Fin
      (OccurrenceMultiworld.Encoding.signature construction.World).count) :
    construction.signature.directed
        (construction.coordinates.nodeEquiv.toFun parent)
        (construction.coordinates.nodeEquiv.toFun child) =
      construction.World.directed
        (OccurrenceMultiworld.Encoding.decode parent)
        (OccurrenceMultiworld.Encoding.decode child) :=
  construction.target_directed_eq_reference parent child

/-- The probability-bearing endpoint retains the exact reference latent graph. -/
theorem probabilityTarget_incident_eq_reference
    (construction : FromEmptyExecutedOccurrenceConstruction mode event)
    (root : Fin mode.record.model.latent.count)
    (child : Fin
      (OccurrenceMultiworld.Encoding.signature construction.World).count) :
    construction.probabilityTarget.record.model.latent.incident
        (construction.sourceRoot root)
        (construction.coordinates.nodeEquiv.toFun child) =
      construction.World.incident root
        (OccurrenceMultiworld.Encoding.decode child) :=
  construction.target_incident_eq_reference root child

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

/-- The route-specific endpoint exposed through the shared multiworld interface. -/
noncomputable def sharedEndpoint
    (construction : FromEmptyExecutedOccurrenceConstruction mode event) :
    MultiworldEndpoint mode.record.model event where
  signature := construction.signature
  record := construction.endpointRecord
  coordinates := construction.coordinates
  eventAt := construction.endpointEvent
  eventAt_coordinates := by
    intro predicate assignment
    unfold endpointEvent configuredEvent
    change predicate
        (OccurrenceMultiworld.Encoding.decodeAssignment construction.World
          (construction.linked.coordinates.untransportObserved
            (construction.atomic.coordinates.untransportObserved assignment))) =
      predicate
        (OccurrenceMultiworld.Encoding.decodeAssignment construction.World
          (construction.coordinates.untransportObserved assignment))
    rw [show construction.coordinates =
        construction.linked.coordinates.trans construction.atomic.coordinates
      from rfl]
    exact congrArg
      (fun encoded => predicate
        (OccurrenceMultiworld.Encoding.decodeAssignment construction.World
          encoded))
      (AtomicIntervention.SameCoordinates.untransportObserved_trans
        construction.linked.coordinates construction.atomic.coordinates
        assignment).symm
  observedValue := construction.endpointRecord_observedValue

variable {S : ObservedSignature} {mode : CausalMode S}
  {query : CounterfactualQuery S}

noncomputable def denominator
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb :=
  MultiworldEndpoint.denominator query construction.sharedEndpoint

noncomputable def numerator
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb :=
  MultiworldEndpoint.numerator query construction.sharedEndpoint

noncomputable def denote
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    ProbabilityResult.Result :=
  MultiworldEndpoint.denote query construction.sharedEndpoint

theorem denominator_equiv
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv construction.denominator
      (query.denominator mode.record.model) :=
  MultiworldEndpoint.denominator_equiv query construction.sharedEndpoint

theorem numerator_equiv
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv construction.numerator
      (query.numerator mode.record.model) :=
  MultiworldEndpoint.numerator_equiv query construction.sharedEndpoint

noncomputable def semanticAgreement
    (construction :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    ProbabilityResult.Equivalent construction.denote
      (query.denote mode.record.model) :=
  MultiworldEndpoint.semanticAgreement query construction.sharedEndpoint

end FromEmptyExecutedOccurrenceConstruction

end Causality
end Thesis
