import Thesis.Causality.ExecutedMultiworld.Linking
import Thesis.Causality.ExecutedMultiworld.Endpoint

namespace Thesis
namespace Causality

open Probability

/-!
Equation installation and complete execution from a fresh factual record.

The route retains the source structural model but starts from its initial
product prior with no active intervention. The first section configures copied
occurrence worlds and reindexes that prior. The second section runs the atomic
intervention compiler and reads probabilities from its actual endpoint record.
Keeping those steps separate matters: the occurrence multiworld remains an
independent semantic reference, not a pre-installed target model.
-/

/-! ## Executable equation installation -/

/--
An occurrence node together with evidence that it represents one concrete
endpoint coordinate.  Packaging the equality makes dependent elimination over
the general mechanism constructive and stable.
-/
structure ExecutedOccurrenceFiber
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (child : Fin linked.signature.count) where
  occurrence : OccurrenceNode template event
  represented :
    linked.worldNode occurrence.world occurrence.node = child

def LinkedOccurrenceCopies.decodedFiber
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (child : Fin linked.signature.count) :
    ExecutedOccurrenceFiber linked child where
  occurrence :=
    OccurrenceMultiworld.Encoding.decode
      (linked.coordinates.nodeEquiv.invFun child)
  represented := linked.coordinates.nodeEquiv.right_inv child

def LinkedOccurrenceCopies.worldFiber
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (node : Fin template.count) :
    ExecutedOccurrenceFiber linked (linked.worldNode world node) where
  occurrence := ⟨world, node⟩
  represented := rfl

theorem LinkedOccurrenceCopies.decodedFiber_eq_worldFiber
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (node : Fin template.count) :
    linked.decodedFiber (linked.worldNode world node) =
      linked.worldFiber world node := by
  have occurrenceEq :
      (linked.decodedFiber
        (linked.worldNode world node)).occurrence =
      (linked.worldFiber world node).occurrence :=
    (congrArg OccurrenceMultiworld.Encoding.decode
      (linked.coordinates_invFun_worldNode world node)).trans
        (OccurrenceMultiworld.Encoding.decode_encode _)
  cases decoded : linked.decodedFiber (linked.worldNode world node) with
  | mk decodedOccurrence decodedRepresented =>
      cases expected : linked.worldFiber world node with
      | mk expectedOccurrence expectedRepresented =>
          simp only [decoded, expected] at occurrenceEq
          subst expectedOccurrence
          have representedEq :
              decodedRepresented = expectedRepresented :=
            Subsingleton.elim _ _
          cases representedEq
          rfl

def LinkedOccurrenceCopies.representedMechanism
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    {child : Fin linked.signature.count}
    (fiber : ExecutedOccurrenceFiber linked child)
    (parents : linked.signature.ParentValues child)
    (latents : linked.target.record.model.latent.Inputs child) :
    template.Value fiber.occurrence.node :=
  source.record.model.mechanism fiber.occurrence.node
    (fun parent edge =>
      cast (linked.worldNode_value_eq fiber.occurrence.world parent)
        (parents (linked.worldNode fiber.occurrence.world parent)
          (by
            have representedEdge :=
              linked.worldNode_directed fiber.occurrence.world parent
                fiber.occurrence.node edge
            rw [fiber.represented] at representedEdge
            exact representedEdge)))
    (fun sourceRoot incident =>
      cast (linked.rootValue_eq sourceRoot)
        (latents (linked.root sourceRoot)
          (by
            have representedIncident :=
              linked.worldNode_incident fiber.occurrence.world sourceRoot
                fiber.occurrence.node incident
            rw [fiber.represented] at representedIncident
            exact representedIncident)))

def LinkedOccurrenceCopies.fiberMechanism
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (child : Fin linked.signature.count)
    (parents : linked.signature.ParentValues child)
    (latents : linked.target.record.model.latent.Inputs child)
    (fiber : ExecutedOccurrenceFiber linked child) :
    linked.signature.Value child :=
  cast
    (Eq.trans
      (linked.worldNode_value_eq fiber.occurrence.world
        fiber.occurrence.node).symm
      (congrArg linked.signature.Value fiber.represented))
    (linked.representedMechanism fiber parents latents)

def LinkedOccurrenceCopies.sourceMechanism
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (child : Fin linked.signature.count)
    (parents : linked.signature.ParentValues child)
    (latents : linked.target.record.model.latent.Inputs child) :
    linked.signature.Value child :=
  linked.fiberMechanism child parents latents (linked.decodedFiber child)

def LinkedOccurrenceCopies.configureOperation
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    StructuralMechanismReplacement.Operation linked.target.record where
  replacement := linked.sourceMechanism

def LinkedOccurrenceCopies.configuredModel
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    ExactModel linked.signature :=
  linked.configureOperation.apply.model

def LinkedOccurrenceCopies.configureRecord
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    CausalEpistemicRecord linked.signature :=
  linked.configureOperation.apply

def LinkedOccurrenceCopies.configureTransition
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    CausalEditTransition linked.signature linked.signature where
  source := linked.target
  target := ⟨"configure-occurrence-equations", linked.configureRecord⟩
  operation := .replacingMechanisms linked.configureOperation
  realized := rfl

/-- Reindex the source prior onto the roots of the newly executed worlds. -/
def LinkedOccurrenceCopies.reindexBeliefOperation
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    BeliefReindexing.CertifiedOperation
      linked.configureTransition.target.record where
  OriginSignature := template
  origin := .prior source.record.model
  assignment := linked.rootAssignment
  reference := fun assignment =>
    linked.configureTransition.target.record.model.evalUnder
      linked.configureTransition.target.record.intervention.value
      (linked.rootAssignment assignment)
  interventionPolicy := .preserve (fun _ => rfl)

def LinkedOccurrenceCopies.reindexBeliefRecord
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    CausalEpistemicRecord linked.signature :=
  linked.reindexBeliefOperation.apply

/--
The from-factual route obtains its world-root belief from the source SCM prior
through the explicit root-coordinate map.
-/
@[simp] theorem LinkedOccurrenceCopies.reindexBelief_prior_provenance
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    linked.reindexBeliefRecord.belief =
      source.record.model.prior.map linked.rootAssignment :=
  rfl

def LinkedOccurrenceCopies.reindexBeliefTransition
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    CausalEditTransition linked.signature linked.signature where
  source := linked.configureTransition.target
  target := ⟨"reindex-occurrence-belief", linked.reindexBeliefRecord⟩
  operation := .reindexingBelief linked.reindexBeliefOperation
  realized := rfl

theorem LinkedOccurrenceCopies.configured_mechanism_worldNode
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (child : Fin template.count)
    (parents : linked.signature.ParentValues (linked.worldNode world child))
    (latents : linked.target.record.model.latent.Inputs
      (linked.worldNode world child)) :
    cast (linked.worldNode_value_eq world child)
        (linked.configuredModel.mechanism
          (linked.worldNode world child) parents latents) =
      source.record.model.mechanism child
        (fun parent edge =>
          cast (linked.worldNode_value_eq world parent)
            (parents (linked.worldNode world parent)
              (linked.worldNode_directed world parent child edge)))
        (fun sourceRoot incident =>
          cast (linked.rootValue_eq sourceRoot)
            (latents (linked.root sourceRoot)
              (linked.worldNode_incident world sourceRoot child incident))) := by
  change cast (linked.worldNode_value_eq world child)
      (linked.fiberMechanism (linked.worldNode world child)
        parents latents
        (linked.decodedFiber (linked.worldNode world child))) = _
  have fiberEq := linked.decodedFiber_eq_worldFiber world child
  rw [congrArg
    (linked.fiberMechanism (linked.worldNode world child) parents latents)
    fiberEq]
  simp [fiberMechanism, worldFiber, representedMechanism]

def LinkedOccurrenceCopies.fiberAction
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (child : Fin linked.signature.count)
    (fiber : ExecutedOccurrenceFiber linked child) :
    Option (linked.signature.Value child) :=
  match fiber.occurrence.world.action fiber.occurrence.node with
  | none => none
  | some value =>
      some (cast
        (Eq.trans
          (linked.worldNode_value_eq fiber.occurrence.world
            fiber.occurrence.node).symm
          (congrArg linked.signature.Value fiber.represented))
        value)

/-- The simultaneous action selecting every syntactic counterfactual occurrence. -/
def LinkedOccurrenceCopies.combinedAction
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    AtomicIntervention.Action linked.signature :=
  fun child => linked.fiberAction child (linked.decodedFiber child)

theorem LinkedOccurrenceCopies.combinedAction_worldNode_none
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (node : Fin template.count)
    (selected : world.action node = none) :
    linked.combinedAction (linked.worldNode world node) = none := by
  unfold combinedAction
  have fiberEq := linked.decodedFiber_eq_worldFiber world node
  rw [congrArg
    (linked.fiberAction (linked.worldNode world node)) fiberEq]
  simp [fiberAction, worldFiber, selected]

theorem LinkedOccurrenceCopies.combinedAction_worldNode_some
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (node : Fin template.count)
    (value : template.Value node) (selected : world.action node = some value) :
    linked.combinedAction (linked.worldNode world node) =
      some (cast (linked.worldNode_value_eq world node).symm value) := by
  unfold combinedAction
  have fiberEq := linked.decodedFiber_eq_worldFiber world node
  rw [congrArg
    (linked.fiberAction (linked.worldNode world node)) fiberEq]
  simp [fiberAction, worldFiber, selected]

/--
Before the atomic cuts are compiled, evaluating the configured endpoint under
the simultaneous occurrence action agrees with source-world intervention.
-/
theorem LinkedOccurrenceCopies.configured_evalUnder_worldNode
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (assignment : source.record.model.latent.Assignment)
    (world : OccurrenceWorld template event) (child : Fin template.count) :
    cast (linked.worldNode_value_eq world child)
        (linked.configuredModel.evalUnder linked.combinedAction
          (linked.rootAssignment assignment)
          (linked.worldNode world child)) =
      source.record.model.evalUnder world.action assignment child := by
  change cast (linked.worldNode_value_eq world child)
      (linked.configuredModel.evalNodeUnder linked.combinedAction
        (linked.rootAssignment assignment)
        (linked.worldNode world child)) =
    source.record.model.evalNodeUnder world.action assignment child
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases selected : world.action child with
  | some value =>
      rw [linked.combinedAction_worldNode_some world child value selected]
      simp
  | none =>
      rw [linked.combinedAction_worldNode_none world child selected]
      rw [linked.configured_mechanism_worldNode world child]
      congr 1
      · funext parent edge
        exact linked.configured_evalUnder_worldNode assignment world parent
      · funext sourceRoot incident
        exact linked.rootAssignment_at assignment sourceRoot
termination_by child.val
decreasing_by
  exact template.directed_earlier edge

theorem LinkedOccurrenceCopies.configured_evalUnder_eq_reference
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (assignment : source.record.model.latent.Assignment) :
    linked.configuredModel.evalUnder linked.combinedAction
        (linked.rootAssignment assignment) =
      linked.coordinates.transportObserved
        (OccurrenceMultiworld.Encoding.encodeAssignment
          (source.record.model.occurrenceMultiworld event)
          ((source.record.model.occurrenceMultiworld event).eval assignment)) := by
  let actual :=
    linked.configuredModel.evalUnder linked.combinedAction
      (linked.rootAssignment assignment)
  let reference :=
    OccurrenceMultiworld.Encoding.encodeAssignment
      (source.record.model.occurrenceMultiworld event)
      ((source.record.model.occurrenceMultiworld event).eval assignment)
  have back :
      linked.coordinates.untransportObserved actual = reference := by
    funext index
    let occurrenceNode := OccurrenceMultiworld.Encoding.decode index
    have evaluated :=
      linked.configured_evalUnder_worldNode assignment
        occurrenceNode.world occurrenceNode.node
    change cast (linked.coordinates.value_eq index).symm
        (actual (linked.coordinates.nodeEquiv.toFun index)) =
      reference index
    change cast (linked.coordinates.value_eq index).symm
        (actual
          (linked.worldNode occurrenceNode.world occurrenceNode.node)) =
      (source.record.model.occurrenceMultiworld event).eval assignment
        occurrenceNode
    have valueProofEq :
        (linked.coordinates.value_eq index).symm =
          linked.worldNode_value_eq occurrenceNode.world occurrenceNode.node :=
      Subsingleton.elim _ _
    rw [valueProofEq]
    exact evaluated
  calc
    actual =
        linked.coordinates.transportObserved
          (linked.coordinates.untransportObserved actual) :=
      (AtomicIntervention.SameCoordinates.transportObserved_untransportObserved
        linked.coordinates actual).symm
    _ = linked.coordinates.transportObserved reference :=
      congrArg linked.coordinates.transportObserved back

/-!
## Complete from-factual execution

This route starts from a fresh factual copy of the source model, creates the
additional occurrence worlds, installs their equations, transports the belief,
and only then compiles the combined action. Endpoint equalities below are
therefore semantic statements about a recorded edit path.
-/

/--
The executable occurrence construction.  The direct occurrence model is not a
field: it is reconstructed independently from `mode.record.model` when stating
the semantic comparison.
-/
structure ExecutedOccurrenceConstruction
    (mode : CausalMode S) (event : CounterfactualEvent S) where
  linked : LinkedOccurrenceCopies S (counterfactualBaseMode mode) event.atoms
  linked_eq :
    linked = LinkedOccurrenceCopies.build S
      (counterfactualBaseMode mode) event.atoms
  atomic : AtomicIntervention.Execution linked.reindexBeliefTransition.target
  atomic_eq :
    atomic = AtomicIntervention.compile linked.reindexBeliefTransition.target
      linked.combinedAction

namespace ExecutedOccurrenceConstruction

noncomputable def canonical (mode : CausalMode S)
    (event : CounterfactualEvent S) :
    ExecutedOccurrenceConstruction mode event :=
  let linked := LinkedOccurrenceCopies.build S
    (counterfactualBaseMode mode) event.atoms
  { linked := linked
    linked_eq := rfl
    atomic := AtomicIntervention.compile linked.reindexBeliefTransition.target
      linked.combinedAction
    atomic_eq := rfl }

/-- Copy creation and causal linkage preserve the fresh source's empty override. -/
theorem linked_noActiveIntervention
    (construction : ExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.NoActiveIntervention construction.linked.target := by
  rw [construction.linked_eq]
  exact LinkedOccurrenceCopies.build_noActiveIntervention _
    (counterfactualBaseMode mode) event.atoms
    (counterfactualBaseMode_noActiveIntervention mode)

/-- Mechanism configuration changes equations but leaves the override empty. -/
theorem configured_noActiveIntervention
    (construction : ExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.NoActiveIntervention
      construction.linked.configureTransition.target :=
  AtomicIntervention.mechanismReplacement_noActiveIntervention
    construction.linked.target construction.linked.configureOperation
    "configure-occurrence-equations" construction.linked_noActiveIntervention

/-- Prior reindexing preserves the empty override used by atomic compilation. -/
theorem atomicSource_noActiveIntervention
    (construction : ExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.NoActiveIntervention
      construction.linked.reindexBeliefTransition.target :=
  AtomicIntervention.beliefReindexing_noActiveIntervention
    construction.linked.configureTransition.target
    construction.linked.reindexBeliefOperation
    "reindex-occurrence-belief" construction.configured_noActiveIntervention

abbrev World {S : ObservedSignature} {mode : CausalMode S}
    {event : CounterfactualEvent S}
    (_construction : ExecutedOccurrenceConstruction mode event) :
    OccurrenceMultiworld S event :=
  mode.record.model.occurrenceMultiworld event

abbrev signature
    (construction : ExecutedOccurrenceConstruction mode event) :
    ObservedSignature :=
  construction.atomic.signature

abbrev target
    (construction : ExecutedOccurrenceConstruction mode event) :
    CausalMode construction.signature :=
  construction.atomic.target

def path (construction : ExecutedOccurrenceConstruction mode event) :
    CausalEditPath (counterfactualBaseMode mode) construction.target :=
  construction.linked.path.append
    ((CausalEditPath.single construction.linked.configureTransition).append
      ((CausalEditPath.single
        construction.linked.reindexBeliefTransition).append
        construction.atomic.path))

def coordinates (construction : ExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.SameCoordinates
      (OccurrenceMultiworld.Encoding.signature construction.World)
      construction.signature :=
  construction.linked.coordinates.trans construction.atomic.coordinates

noncomputable def realizes
    (construction : ExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation
      construction.atomic
      (fun assignment =>
        construction.linked.configuredModel.evalUnder
          construction.linked.combinedAction assignment) := by
  rw [construction.atomic_eq]
  exact AtomicIntervention.compileDeterministicRealizes
    construction.linked.reindexBeliefTransition.target
    construction.linked.combinedAction

/-- The compiled atomic target still has no compact intervention. -/
theorem atomicTarget_noActiveIntervention
    (construction : ExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.NoActiveIntervention construction.atomic.target := by
  rw [construction.atomic_eq]
  exact AtomicIntervention.compile_noActiveIntervention
    construction.linked.reindexBeliefTransition.target
    construction.linked.combinedAction
    construction.atomicSource_noActiveIntervention

/--
The canonical from-factual atomic endpoint may clear its override because the
entire preceding construction and atomic compiler preserve intervention
emptiness.
-/
noncomputable def endpointInterventionAbsorbed
    (construction : ExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation.EndpointInterventionAbsorbed
      construction.realizes :=
  AtomicIntervention.Execution.DeterministicRealizesEvaluation.EndpointInterventionAbsorbed.ofEmpty
    construction.realizes construction.atomicTarget_noActiveIntervention

/-- Close the atomic program with its canonical probability-bearing target. -/
noncomputable def probabilityExecution
    (construction : ExecutedOccurrenceConstruction mode event) :
    AtomicIntervention.Execution
      construction.linked.reindexBeliefTransition.target :=
  construction.realizes.canonicalExecution
    construction.endpointInterventionAbsorbed

noncomputable def probabilityTarget
    (construction : ExecutedOccurrenceConstruction mode event) :
    CausalMode construction.signature :=
  construction.probabilityExecution.target

/-- The complete modal path ends at the record used for probabilities. -/
noncomputable def probabilityPath
    (construction : ExecutedOccurrenceConstruction mode event) :
    CausalEditPath (counterfactualBaseMode mode)
      construction.probabilityTarget :=
  construction.path.append
    (CausalEditPath.single
      (construction.realizes.endpointTransition
        construction.endpointInterventionAbsorbed))

/--
The complete from-factual endpoint belief is the source prior pushed first
through shared-world root coordinates and then through the executed atomic
assignment.
-/
@[simp] theorem probabilityTarget_belief_provenance
    (construction : ExecutedOccurrenceConstruction mode event) :
    construction.probabilityTarget.record.belief =
      (mode.record.model.prior.map construction.linked.rootAssignment).map
        construction.realizes.assignment :=
  rfl

noncomputable def endpointAssignment
    (construction : ExecutedOccurrenceConstruction mode event)
    (assignment : mode.record.model.latent.Assignment) :
    construction.target.record.model.latent.Assignment :=
  construction.realizes.assignment
    (construction.linked.rootAssignment assignment)

/-- The actual SCM endpoint computes the independent occurrence evaluator. -/
theorem endpoint_eval
    (construction : ExecutedOccurrenceConstruction mode event)
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

/-- Decoding the executed endpoint recovers every factual and occurrence world. -/
theorem endpoint_decodedAssignment
    (construction : ExecutedOccurrenceConstruction mode event)
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

/-- One retained syntactic occurrence is executed with its own action. -/
theorem endpoint_counterfactualOccurrence
    {S : ObservedSignature} {mode : CausalMode S}
    {event : CounterfactualEvent S}
    (construction : ExecutedOccurrenceConstruction mode event)
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

/-- The endpoint epistemic record uses the actual atomic target SCM. -/
noncomputable def endpointRecord
    (construction : ExecutedOccurrenceConstruction mode event) :
    CausalEpistemicRecord construction.signature :=
  construction.probabilityTarget.record

@[simp] theorem endpointRecord_is_probabilityTarget
    (construction : ExecutedOccurrenceConstruction mode event) :
    construction.endpointRecord = construction.probabilityTarget.record :=
  rfl

theorem endpointRecord_probabilityTarget
    (construction : ExecutedOccurrenceConstruction mode event)
    (eventAtTarget : construction.signature.Assignment -> Bool) :
    QProb.Equiv
      (construction.endpointRecord.observedValue eventAtTarget)
      (construction.probabilityTarget.record.observedValue eventAtTarget) :=
  QProb.equiv_refl _

def configuredEvent
    (construction : ExecutedOccurrenceConstruction mode event)
    (predicate : construction.World.Assignment -> Bool) :
    construction.linked.signature.Assignment -> Bool :=
  fun assignment =>
    predicate
      (OccurrenceMultiworld.Encoding.decodeAssignment construction.World
        (construction.linked.coordinates.untransportObserved assignment))

def endpointEvent
    (construction : ExecutedOccurrenceConstruction mode event)
    (predicate : construction.World.Assignment -> Bool) :
    construction.signature.Assignment -> Bool :=
  AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointEvent
    construction.atomic (construction.configuredEvent predicate)

theorem configuredEvent_eval
    (construction : ExecutedOccurrenceConstruction mode event)
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

/-- Every endpoint event has exactly the independent occurrence-world probability. -/
theorem endpointRecord_observedValue
    (construction : ExecutedOccurrenceConstruction mode event)
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
    (construction : ExecutedOccurrenceConstruction mode event) :
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

/-! ## Query probabilities read from the executed endpoint -/

variable {S : ObservedSignature} {mode : CausalMode S}
  {query : CounterfactualQuery S}

noncomputable def denominator
    (construction :
      ExecutedOccurrenceConstruction mode query.combinedEvent) : QProb :=
  MultiworldEndpoint.denominator query construction.sharedEndpoint

noncomputable def numerator
    (construction :
      ExecutedOccurrenceConstruction mode query.combinedEvent) : QProb :=
  MultiworldEndpoint.numerator query construction.sharedEndpoint

noncomputable def denote
    (construction :
      ExecutedOccurrenceConstruction mode query.combinedEvent) :
    ProbabilityResult.Result :=
  MultiworldEndpoint.denote query construction.sharedEndpoint

theorem denominator_equiv
    (construction :
      ExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv construction.denominator
      (query.denominator mode.record.model) :=
  MultiworldEndpoint.denominator_equiv query construction.sharedEndpoint

theorem numerator_equiv
    (construction :
      ExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv construction.numerator
      (query.numerator mode.record.model) :=
  MultiworldEndpoint.numerator_equiv query construction.sharedEndpoint

noncomputable def semanticAgreement
    (construction :
      ExecutedOccurrenceConstruction mode query.combinedEvent) :
    ProbabilityResult.Equivalent construction.denote
      (query.denote mode.record.model) :=
  MultiworldEndpoint.semanticAgreement query construction.sharedEndpoint

end ExecutedOccurrenceConstruction

end Causality
end Thesis
