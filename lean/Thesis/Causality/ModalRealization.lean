import Thesis.Causality.Structural

namespace Thesis
namespace Causality

open Probability

/-!
Executable realizations of the kernel leaves occurring in modal do-calculus
traces.  A do-calculus derivation is an equality proof, not a chronological
execution trace.  The structures below therefore connect each locked kernel
to the ordinary record operations that realize its action and observation
components, while semantic soundness remains attached to the derivation.
-/

namespace Kernel

/-- The canonical record obtained by executing a kernel's action lock. -/
def actionRecord (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) : CausalEpistemicRecord S :=
  (CausalEpistemicRecord.initial model).interveneNodes kernel.action reference

/-- The latent evidence used to execute a kernel's observation lock. -/
def observationEvidence (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) : model.latent.Assignment -> Bool :=
  (kernel.actionRecord model reference).nodeObservationEvidence
    kernel.condition reference

/-- The cylinder event used to read the kernel's outcome after both locks. -/
def outcomeEvent (kernel : Kernel S) (reference : S.Assignment) :
    S.Assignment -> Bool :=
  Kernel.agreesOn kernel.outcome reference

end Kernel

/-- Executing the action lock installs exactly the kernel intervention. -/
theorem Kernel.actionRecord_intervention
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) (i : Fin S.count) :
    (kernel.actionRecord model reference).intervention.value i =
      kernel.intervention reference i := by
  simp [Kernel.actionRecord, CausalEpistemicRecord.initial,
    CausalEpistemicRecord.interveneNodes, HardIntervention.setNodes,
    HardIntervention.empty, Kernel.intervention,
    FiniteLatentSCM.noIntervention]

/-- Local support of a kernel entails positivity of its conditioning cylinder. -/
theorem Kernel.supported_condition_positive
    (model : ExactModel S) (kernel : Kernel S) (reference : S.Assignment)
    (supported :
      ProbabilityTerm.SupportedAt model (.kernel kernel) reference) :
    (kernel.distribution model reference).EventPositive
      (kernel.conditionEvent reference) := by
  rcases supported with ⟨value, equivalent⟩
  let denominator :=
    (kernel.distribution model reference).probVal
      (kernel.conditionEvent reference)
  by_cases positive : 0 < denominator.num
  · simpa [denominator, FiniteProbRecord.EventPositive,
      FiniteProbRecord.probVal] using positive
  · simp only [ProbabilityTerm.denote, Kernel.denote,
      ProbabilityResult.divide, denominator, dif_neg positive] at equivalent
    cases equivalent

/--
The action record and the kernel distribution assign the same mass to every
observed event.  The proof is pointwise so it remains suitable for an
intensional/setoid presentation.
-/
noncomputable def Kernel.actionRecord_probability
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    QProb.Equiv
      ((kernel.actionRecord model reference).observedValue event)
      ((kernel.distribution model reference).probVal event) := by
  have interventionEqual :
      (kernel.actionRecord model reference).intervention.value =
        kernel.intervention reference := by
    funext i
    exact kernel.actionRecord_intervention model reference i
  change QProb.Equiv
    ((model.prior.map
      (model.evalUnder
        (kernel.actionRecord model reference).intervention.value)).probVal event)
    ((kernel.distribution model reference).probVal event)
  rw [interventionEqual]
  by_cases hasAction : kernel.hasAction = true
  · simpa [Kernel.distribution, hasAction,
      FiniteLatentSCM.interventionalDist] using
      (QProb.equiv_refl
        ((model.prior.map
          (model.evalUnder (kernel.intervention reference))).probVal event))
  · have noAction : forall i, kernel.action i = false :=
      (finAny_eq_false_iff kernel.action).mp (by
        cases value : kernel.hasAction <;> simp_all [Kernel.hasAction])
    have noIntervention :
        kernel.intervention reference = FiniteLatentSCM.noIntervention S := by
      funext i
      simp [Kernel.intervention, FiniteLatentSCM.noIntervention, noAction i]
    rw [noIntervention]
    simpa [Kernel.distribution, hasAction,
      FiniteLatentSCM.observationalDist, FiniteLatentSCM.eval] using
      (QProb.equiv_refl
        ((model.prior.map
          (model.evalUnder (FiniteLatentSCM.noIntervention S))).probVal event))

namespace Kernel

/-- The empty epistemic source from which a kernel action is atomically compiled. -/
def atomicSource (model : ExactModel S) (_kernel : Kernel S) :
    CausalMode S :=
  ⟨"kernel/atomic-source", CausalEpistemicRecord.initial model⟩

/-- The structural edit path implementing all action coordinates of a kernel. -/
def atomicBaseExecution (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    AtomicIntervention.Execution (kernel.atomicSource model) :=
  AtomicIntervention.compile (kernel.atomicSource model)
    (kernel.intervention reference)

/-- Constructive unit-level semantics before endpoint probability reindexing. -/
noncomputable def atomicBaseDeterministicRealizes
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation
      (kernel.atomicBaseExecution model reference)
      (fun assignment =>
        model.evalUnder (kernel.intervention reference) assignment) :=
  AtomicIntervention.compileDeterministicRealizes
    (kernel.atomicSource model) (kernel.intervention reference)

/-- The fresh kernel source has no residual compact intervention. -/
theorem atomicSource_noActiveIntervention
    (model : ExactModel S) (kernel : Kernel S) :
    AtomicIntervention.NoActiveIntervention (kernel.atomicSource model) := by
  intro child
  rfl

/--
Atomic kernel compilation preserves the source's empty intervention, thereby
certifying that endpoint clearing removes only an already absorbed override.
-/
noncomputable def atomicBaseEndpointInterventionAbsorbed
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation.EndpointInterventionAbsorbed
      (kernel.atomicBaseDeterministicRealizes model reference) :=
  AtomicIntervention.compileEndpointInterventionAbsorbed
    (kernel.atomicSource model) (kernel.intervention reference)
    (kernel.atomicSource_noActiveIntervention model)

/--
The complete atomic kernel execution, closed by a proof-carrying probability
reindexing transition so its target is the semantic endpoint record.
-/
noncomputable def atomicExecution (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    AtomicIntervention.Execution (kernel.atomicSource model) :=
  (kernel.atomicBaseDeterministicRealizes model reference).canonicalExecution
    (kernel.atomicBaseEndpointInterventionAbsorbed model reference)

/-- Constructive semantics of the closed atomic kernel execution. -/
noncomputable def atomicDeterministicRealizes
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation
      (kernel.atomicExecution model reference)
      (fun assignment =>
        model.evalUnder (kernel.intervention reference) assignment) :=
  (kernel.atomicBaseDeterministicRealizes model reference).canonicalRealizes
    (kernel.atomicBaseEndpointInterventionAbsorbed model reference)

/--
The ordinary kernel route closes from the model prior through the exact latent
assignment computed by atomic compilation.
-/
@[simp] theorem atomicEndpoint_belief_provenance
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    (kernel.atomicExecution model reference).target.record.belief =
      model.prior.map
        (kernel.atomicBaseDeterministicRealizes model reference).assignment :=
  rfl

/-- Probability-bearing record obtained from the actual atomic action endpoint. -/
noncomputable def atomicRecord (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    CausalEpistemicRecord (kernel.atomicExecution model reference).signature :=
  (kernel.atomicExecution model reference).target.record

/-- Transport an observed event to the coordinates of the atomic endpoint. -/
noncomputable def atomicEvent (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    (kernel.atomicExecution model reference).signature.Assignment -> Bool :=
  AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointEvent
    (kernel.atomicExecution model reference) event

end Kernel

/--
Every event read from the atomically edited SCM has the ordinary kernel-action
probability. This is the bridge from structural execution to kernel semantics.
-/
theorem Kernel.atomicRecord_probability
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    QProb.Equiv
      ((kernel.atomicRecord model reference).observedValue
        (kernel.atomicEvent model reference event))
      ((kernel.distribution model reference).probVal event) := by
  exact QProb.equiv_trans
    (AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointRecord_observedValue
      (kernel.atomicDeterministicRealizes model reference) event)
    (by
      change QProb.Equiv
        (model.prior.probVal
          (fun assignment =>
            event (model.evalUnder (kernel.intervention reference) assignment)))
        ((kernel.distribution model reference).probVal event)
      exact QProb.equiv_trans
        (QProb.equiv_symm
          ((kernel.actionRecord model reference).observedDist_probVal event))
        (kernel.actionRecord_probability model reference event))

/--
A kernel action certificate whose execution is definitionally the canonical
atomic structural compiler.
-/
structure AtomicKernelActionRealization
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) where
  deterministic :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation
      (kernel.atomicExecution model reference)
      (fun assignment =>
        model.evalUnder (kernel.intervention reference) assignment)

namespace AtomicKernelActionRealization

variable {S : ObservedSignature} {model : ExactModel S}
  {kernel : Kernel S} {reference : S.Assignment}

noncomputable def canonical (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    AtomicKernelActionRealization model kernel reference where
  deterministic := kernel.atomicDeterministicRealizes model reference

theorem probability
    (realization : AtomicKernelActionRealization model kernel reference)
    (event : S.Assignment -> Bool) :
    QProb.Equiv
      (realization.deterministic.endpointRecord.observedValue
        (kernel.atomicEvent model reference event))
      ((kernel.distribution model reference).probVal event) := by
  exact QProb.equiv_trans
    (AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointRecord_observedValue
      realization.deterministic event)
    (by
      change QProb.Equiv
        (model.prior.probVal
          (fun assignment =>
            event (model.evalUnder (kernel.intervention reference) assignment)))
        ((kernel.distribution model reference).probVal event)
      exact QProb.equiv_trans
        (QProb.equiv_symm
          ((kernel.actionRecord model reference).observedDist_probVal event))
        (kernel.actionRecord_probability model reference event))

end AtomicKernelActionRealization

/-- Kernel support supplies the positivity required by the observation step. -/
theorem Kernel.observationEvidence_positive
    (model : ExactModel S) (kernel : Kernel S) (reference : S.Assignment)
    (supported :
      ProbabilityTerm.SupportedAt model (.kernel kernel) reference) :
    (kernel.actionRecord model reference).belief.EventPositive
      (kernel.observationEvidence model reference) := by
  have distributionPositive :=
    kernel.supported_condition_positive model reference supported
  have distributionNumPositive :
      0 < ((kernel.distribution model reference).probVal
        (kernel.conditionEvent reference)).num := by
    simpa [FiniteProbRecord.EventPositive, FiniteProbRecord.probVal] using
      distributionPositive
  have actionNumPositive :
      0 < ((kernel.actionRecord model reference).observedValue
        (kernel.conditionEvent reference)).num :=
    (QProb.equiv_num_pos_iff
      (kernel.actionRecord_probability model reference
        (kernel.conditionEvent reference))).mpr distributionNumPositive
  simpa [Kernel.observationEvidence,
    CausalEpistemicRecord.nodeObservationEvidence,
    CausalEpistemicRecord.observedValue,
    CausalEpistemicRecord.observedDist, FiniteProbRecord.EventPositive,
    FiniteProbRecord.probVal, FiniteProbRecord.map,
    FiniteProbRecord.eventMass_map_labels] using actionNumPositive

namespace Kernel

/-- Execute the observation lock after the action lock. -/
def observedRecord (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment)
    (positive :
      (kernel.actionRecord model reference).belief.EventPositive
        (kernel.observationEvidence model reference)) :
    CausalEpistemicRecord S :=
  (kernel.actionRecord model reference).conditionLatent
    (kernel.observationEvidence model reference) positive

end Kernel

/--
Executing a supported kernel's action and observation locks computes the same
conditional rational as the kernel semantics.
-/
noncomputable def Kernel.observedRecord_outcome_probability
    (model : ExactModel S) (kernel : Kernel S) (reference : S.Assignment)
    (supported :
      ProbabilityTerm.SupportedAt model (.kernel kernel) reference) :
    let positive := kernel.observationEvidence_positive model reference supported
    QProb.Equiv
      ((kernel.observedRecord model reference positive).observedValue
        (kernel.outcomeEvent reference))
      (QProb.div
        ((kernel.distribution model reference).probVal
          (kernel.numeratorEvent reference))
        ((kernel.distribution model reference).probVal
          (kernel.conditionEvent reference))
        (by
          have h := kernel.supported_condition_positive model reference supported
          simpa [FiniteProbRecord.EventPositive, FiniteProbRecord.probVal]
            using h)) := by
  let action := kernel.actionRecord model reference
  let evidence := kernel.observationEvidence model reference
  let positive := kernel.observationEvidence_positive model reference supported
  let outcomeOnLatent : model.latent.Assignment -> Bool :=
    fun latent => kernel.outcomeEvent reference
      (model.evalUnder action.intervention.value latent)
  have observedToBelief :
      QProb.Equiv
        ((kernel.observedRecord model reference positive).observedValue
          (kernel.outcomeEvent reference))
        ((action.conditionLatent evidence positive).belief.probVal
          outcomeOnLatent) := by
    simpa [Kernel.observedRecord, action, evidence, outcomeOnLatent,
      CausalEpistemicRecord.conditionLatent] using
      ((kernel.observedRecord model reference positive).observedDist_probVal
        (kernel.outcomeEvent reference))
  have beliefToRatio :
      QProb.Equiv
        ((action.conditionLatent evidence positive).belief.probVal
          outcomeOnLatent)
        (QProb.div
          (action.belief.probVal
            (fun latent => evidence latent && outcomeOnLatent latent))
          (action.belief.probVal evidence) positive) :=
    action.conditionLatent_probVal evidence outcomeOnLatent positive
  have numeratorToAction :
      QProb.Equiv
        (action.belief.probVal
          (fun latent => evidence latent && outcomeOnLatent latent))
        (action.observedValue (kernel.numeratorEvent reference)) := by
    exact QProb.equiv_trans
      (FiniteProbRecord.probVal_congr action.belief _ _ (fun latent => by
        simp [evidence, outcomeOnLatent, Kernel.observationEvidence,
          CausalEpistemicRecord.nodeObservationEvidence,
          Kernel.outcomeEvent, Kernel.numeratorEvent, Bool.and_comm,
          action, Kernel.actionRecord, CausalEpistemicRecord.initial,
          CausalEpistemicRecord.interveneNodes]))
      (QProb.equiv_symm
        (action.observedDist_probVal (kernel.numeratorEvent reference)))
  have denominatorToAction :
      QProb.Equiv (action.belief.probVal evidence)
        (action.observedValue (kernel.conditionEvent reference)) := by
    simpa [evidence, Kernel.observationEvidence,
      CausalEpistemicRecord.nodeObservationEvidence,
      Kernel.conditionEvent] using
      (QProb.equiv_symm
        (action.observedDist_probVal (kernel.conditionEvent reference)))
  have numeratorToDistribution :
      QProb.Equiv
        (action.belief.probVal
          (fun latent => evidence latent && outcomeOnLatent latent))
        ((kernel.distribution model reference).probVal
          (kernel.numeratorEvent reference)) :=
    QProb.equiv_trans numeratorToAction
      (kernel.actionRecord_probability model reference
        (kernel.numeratorEvent reference))
  have denominatorToDistribution :
      QProb.Equiv (action.belief.probVal evidence)
        ((kernel.distribution model reference).probVal
          (kernel.conditionEvent reference)) :=
    QProb.equiv_trans denominatorToAction
      (kernel.actionRecord_probability model reference
        (kernel.conditionEvent reference))
  have distributionPositive :
      0 < ((kernel.distribution model reference).probVal
        (kernel.conditionEvent reference)).num := by
    have h := kernel.supported_condition_positive model reference supported
    simpa [FiniteProbRecord.EventPositive, FiniteProbRecord.probVal] using h
  exact QProb.equiv_trans observedToBelief
    (QProb.equiv_trans beliefToRatio
      (QProb.div_congr numeratorToDistribution denominatorToDistribution
        positive distributionPositive))

/--
A supported kernel together with its concrete intervention/observation
execution and the value computed by both presentations.
-/
structure KernelOperationRealization (model : ExactModel S)
    (kernel : Kernel S) (reference : S.Assignment) where
  atomicAction : AtomicKernelActionRealization model kernel reference
  value : QProb
  denotation : ProbabilityResult.Equivalent
    (kernel.denote model reference) (some value)
  conditionPositive :
    (kernel.actionRecord model reference).belief.EventPositive
      (kernel.observationEvidence model reference)
  operationValue : QProb.Equiv
    ((kernel.observedRecord model reference conditionPositive).observedValue
      (kernel.outcomeEvent reference))
    value

namespace KernelOperationRealization

variable {S : ObservedSignature} {model : ExactModel S}
  {kernel : Kernel S} {reference : S.Assignment}

/-- Construct the operation realization carried implicitly by local support. -/
noncomputable def ofSupported
    (supported :
      ProbabilityTerm.SupportedAt model (.kernel kernel) reference) :
    KernelOperationRealization model kernel reference := by
  rcases supported with ⟨value, denotation⟩
  let restoredSupport :
      ProbabilityTerm.SupportedAt model (.kernel kernel) reference :=
    ⟨value, denotation⟩
  let conditionPositive :=
    kernel.observationEvidence_positive model reference restoredSupport
  refine
    { atomicAction :=
        AtomicKernelActionRealization.canonical model kernel reference
      value := value
      denotation := denotation
      conditionPositive := conditionPositive
      operationValue := ?_ }
  have operationToRatio :=
    kernel.observedRecord_outcome_probability model reference restoredSupport
  have distributionPositive :
      0 < ((kernel.distribution model reference).probVal
        (kernel.conditionEvent reference)).num := by
    have h := kernel.supported_condition_positive model reference restoredSupport
    simpa [FiniteProbRecord.EventPositive, FiniteProbRecord.probVal] using h
  have ratioToValue :
      QProb.Equiv
        (QProb.div
          ((kernel.distribution model reference).probVal
            (kernel.numeratorEvent reference))
          ((kernel.distribution model reference).probVal
            (kernel.conditionEvent reference)) distributionPositive)
        value := by
    simp only [ProbabilityTerm.denote, Kernel.denote,
      ProbabilityResult.divide] at denotation
    rw [dif_pos distributionPositive] at denotation
    cases denotation with
    | value equivalent => exact equivalent
  exact QProb.equiv_trans operationToRatio ratioToValue

/-- Numerator mass read from the actual structurally edited endpoint. -/
noncomputable def atomicNumerator
    (realization : KernelOperationRealization model kernel reference) : QProb :=
  realization.atomicAction.deterministic.endpointRecord.observedValue
    (kernel.atomicEvent model reference (kernel.numeratorEvent reference))

/-- Denominator mass read from the actual structurally edited endpoint. -/
noncomputable def atomicDenominator
    (realization : KernelOperationRealization model kernel reference) : QProb :=
  realization.atomicAction.deterministic.endpointRecord.observedValue
    (kernel.atomicEvent model reference (kernel.conditionEvent reference))

theorem atomicNumerator_probability
    (realization : KernelOperationRealization model kernel reference) :
    QProb.Equiv realization.atomicNumerator
      ((kernel.distribution model reference).probVal
        (kernel.numeratorEvent reference)) :=
  realization.atomicAction.probability (kernel.numeratorEvent reference)

theorem atomicDenominator_probability
    (realization : KernelOperationRealization model kernel reference) :
    QProb.Equiv realization.atomicDenominator
      ((kernel.distribution model reference).probVal
        (kernel.conditionEvent reference)) :=
  realization.atomicAction.probability (kernel.conditionEvent reference)

theorem atomicDenominator_positive
    (realization : KernelOperationRealization model kernel reference) :
    0 < realization.atomicDenominator.num := by
  have distributionPositive :
      0 < ((kernel.distribution model reference).probVal
        (kernel.conditionEvent reference)).num := by
    have supported :
        ProbabilityTerm.SupportedAt model (.kernel kernel) reference :=
      ⟨realization.value, realization.denotation⟩
    have positive :=
      kernel.supported_condition_positive model reference supported
    simpa [FiniteProbRecord.EventPositive, FiniteProbRecord.probVal]
      using positive
  exact (QProb.equiv_num_pos_iff
    realization.atomicDenominator_probability).mpr distributionPositive

/--
The value carried by a kernel certificate is the conditional ratio computed
from the atomically edited endpoint, not merely from the compact override.
-/
theorem atomicConditionedValue
    (realization : KernelOperationRealization model kernel reference) :
    QProb.Equiv
      (QProb.div realization.atomicNumerator realization.atomicDenominator
        realization.atomicDenominator_positive)
      realization.value := by
  have distributionPositive :
      0 < ((kernel.distribution model reference).probVal
        (kernel.conditionEvent reference)).num := by
    have supported :
        ProbabilityTerm.SupportedAt model (.kernel kernel) reference :=
      ⟨realization.value, realization.denotation⟩
    have positive :=
      kernel.supported_condition_positive model reference supported
    simpa [FiniteProbRecord.EventPositive, FiniteProbRecord.probVal]
      using positive
  have endpointToDistribution :
      QProb.Equiv
        (QProb.div realization.atomicNumerator realization.atomicDenominator
          realization.atomicDenominator_positive)
        (QProb.div
          ((kernel.distribution model reference).probVal
            (kernel.numeratorEvent reference))
          ((kernel.distribution model reference).probVal
            (kernel.conditionEvent reference))
          distributionPositive) :=
    QProb.div_congr realization.atomicNumerator_probability
      realization.atomicDenominator_probability
      realization.atomicDenominator_positive distributionPositive
  have distributionToValue :
      QProb.Equiv
        (QProb.div
          ((kernel.distribution model reference).probVal
            (kernel.numeratorEvent reference))
          ((kernel.distribution model reference).probVal
            (kernel.conditionEvent reference))
          distributionPositive)
        realization.value := by
    have denotation := realization.denotation
    simp only [Kernel.denote, ProbabilityResult.divide] at denotation
    rw [dif_pos distributionPositive] at denotation
    cases denotation with
    | value equivalent => exact equivalent
  exact QProb.equiv_trans endpointToDistribution distributionToValue

/-- The first concrete step realizes the intervention lock. -/
def actionTransition
    (_realization : KernelOperationRealization model kernel reference) :
    CausalTransition S :=
  CausalTransition.intervening "kernel" "kernel/action"
    (CausalEpistemicRecord.initial model) kernel.action reference

theorem actionTransition_realizes
    (realization : KernelOperationRealization model kernel reference) :
    CausalTransition.Realizes realization.actionTransition
      (.intervene kernel.action) :=
  by
    simpa [actionTransition] using
      (CausalTransition.intervening_realizes_intervention
        "kernel" "kernel/action" (CausalEpistemicRecord.initial model)
          kernel.action reference)

/-- The second concrete step realizes the observation lock. -/
def observationTransition
    (realization : KernelOperationRealization model kernel reference) :
    CausalTransition S :=
  CausalTransition.observing "kernel/action" "kernel/action+observation"
    (kernel.actionRecord model reference) kernel.condition reference
      realization.conditionPositive

theorem observationTransition_realizes
    (realization : KernelOperationRealization model kernel reference) :
    CausalTransition.Realizes realization.observationTransition
      (.observe kernel.condition) :=
  by
    simpa [observationTransition] using
      (CausalTransition.observing_realizes_observation
        "kernel/action" "kernel/action+observation"
          (kernel.actionRecord model reference) kernel.condition reference
          realization.conditionPositive)

end KernelOperationRealization

/--
One Pearl rule cell with executable realizations of both endpoint kernels and
the semantic equality supplied by the finite primitive soundness interface.
-/
structure OperationRealizedModalRuleCell
    (G : ObservedGraph S) (model : ExactModel S)
    {source target : CausalQueryMode S}
    (cell : ModalRuleCell G source target) (assignment : S.Assignment) where
  sourceRealization :
    KernelOperationRealization model source.toKernel assignment
  targetRealization :
    KernelOperationRealization model target.toKernel assignment
  valuesEquivalent :
    QProb.Equiv sourceRealization.value targetRealization.value

namespace OperationRealizedModalRuleCell

variable {S : ObservedSignature} {G : ObservedGraph S}
  {model : ExactModel S} {source target : CausalQueryMode S}
  {cell : ModalRuleCell G source target} {assignment : S.Assignment}

/-- Primitive soundness turns a supported modal cell into an operation cell. -/
noncomputable def ofSupported
    (semantics : LocalPrimitiveSoundness G model)
    (sourceSupported :
      ProbabilityTerm.SupportedAt model (.kernel source.toKernel) assignment)
    (targetSupported :
      ProbabilityTerm.SupportedAt model (.kernel target.toKernel) assignment) :
    OperationRealizedModalRuleCell G model cell assignment := by
  let sourceRealization :=
    KernelOperationRealization.ofSupported sourceSupported
  let targetRealization :=
    KernelOperationRealization.ofSupported targetSupported
  have endpointsEquivalent : ProbabilityResult.Equivalent
      (some sourceRealization.value) (some targetRealization.value) :=
    ProbabilityResult.trans
      (ProbabilityResult.symm sourceRealization.denotation)
      (ProbabilityResult.trans
        (semantics.doRule assignment cell.toDoRule
          sourceSupported targetSupported)
        targetRealization.denotation)
  have valuesEquivalent :
      QProb.Equiv sourceRealization.value targetRealization.value := by
    cases endpointsEquivalent with
    | value equivalent => exact equivalent
  exact ⟨sourceRealization, targetRealization, valuesEquivalent⟩

end OperationRealizedModalRuleCell

namespace ModalDerivationTrace

variable {S : ObservedSignature} {G : ObservedGraph S}
  {model : ExactModel S} {assignment : S.Assignment}

/--
Recursive operation realizations for every Pearl-rule leaf of a modal trace.
Probability-algebra constructors retain their existing support tree; only
kernel-to-kernel rule cells generate executable endpoint obligations.
This traversal intentionally follows the already constructed trace: it consumes
the matching local-support subtree to produce a payload indexed by that explicit,
inspectable modal annotation.
-/
noncomputable def OperationRealizations
    (assignment : S.Assignment)
    (semantics : LocalPrimitiveSoundness G model)
    {left right : ProbabilityTerm S}
    {derivation : DoCalculusDerivation G left right}
    (trace : ModalDerivationTrace G derivation)
    (supported : LocalDerivationSupport model assignment derivation) : Type :=
  match trace with
  | .refl _ => Unit
  | .symm inner =>
      inner.OperationRealizations assignment semantics supported.2.2
  | .trans first second =>
      first.OperationRealizations assignment semantics supported.2.2.1 ×
        second.OperationRealizations assignment semantics supported.2.2.2
  | .doRule _ cell =>
      OperationRealizedModalRuleCell G model cell assignment
  | .marginalization .. => Unit
  | .conditioning .. => Unit
  | .chain .. => Unit
  | .marginalizeCongr nodes inner =>
      forall variant,
        (member : variant ∈
          ProbabilityTerm.marginalAssignments S nodes assignment) ->
          inner.OperationRealizations variant semantics
            (supported.2.2 variant member)
  | .evaluateAtCongr fixed inner =>
      inner.OperationRealizations fixed semantics supported.2.2
  | .addCongr first second =>
      first.OperationRealizations assignment semantics supported.2.2.1 ×
        second.OperationRealizations assignment semantics supported.2.2.2
  | .multiplyCongr first second =>
      first.OperationRealizations assignment semantics supported.2.2.1 ×
        second.OperationRealizations assignment semantics supported.2.2.2
  | .divideCongr numerator denominator =>
      numerator.OperationRealizations assignment semantics supported.2.2.1 ×
        denominator.OperationRealizations assignment semantics supported.2.2.2

/-- Construct all operation realizations from the existing recursive support. -/
noncomputable def realizeOperations
    (assignment : S.Assignment)
    (semantics : LocalPrimitiveSoundness G model)
    {left right : ProbabilityTerm S}
    {derivation : DoCalculusDerivation G left right}
    (trace : ModalDerivationTrace G derivation)
    (supported : LocalDerivationSupport model assignment derivation) :
    trace.OperationRealizations assignment semantics supported := by
  induction trace generalizing assignment with
  | refl => exact Unit.unit
  | symm inner ih => exact ih assignment supported.2.2
  | trans first second firstIH secondIH =>
      exact ⟨firstIH assignment supported.2.2.1,
        secondIH assignment supported.2.2.2⟩
  | doRule application cell =>
      exact OperationRealizedModalRuleCell.ofSupported semantics
        supported.1 supported.2.1
  | marginalization => exact Unit.unit
  | conditioning => exact Unit.unit
  | chain => exact Unit.unit
  | marginalizeCongr nodes inner ih =>
      exact fun variant member =>
        ih variant (supported.2.2 variant member)
  | evaluateAtCongr fixed inner ih =>
      exact ih fixed supported.2.2
  | addCongr first second firstIH secondIH =>
      exact ⟨firstIH assignment supported.2.2.1,
        secondIH assignment supported.2.2.2⟩
  | multiplyCongr first second firstIH secondIH =>
      exact ⟨firstIH assignment supported.2.2.1,
        secondIH assignment supported.2.2.2⟩
  | divideCongr numerator denominator numeratorIH denominatorIH =>
      exact ⟨numeratorIH assignment supported.2.2.1,
        denominatorIH assignment supported.2.2.2⟩

end ModalDerivationTrace

end Causality
end Thesis
