import Thesis.Causality.Learning
import Thesis.CausalTransport.ModalRealization

namespace Thesis
namespace Causality

open Probability

/-!
Certificate transport for conservative terminal learning.

The low-level signature/model extension remains in `Learning`; this module is
the separate bridge to published completeness and operation-realized modal
certificates.
-/

/-! ## Identifiability under conservative terminal extension -/

/-- Identifiability of an old joint query survives conservative terminal learning. -/
theorem TerminalVariableSpec.liftJointQuery_identifiable
    (spec : TerminalVariableSpec S) (G : ObservedGraph S)
    (query : JointKernelQuery S)
    (identifiable : TypeTheoreticIdentifiable G query) :
    TypeTheoreticIdentifiable (spec.extendObservedGraph G)
      (spec.liftJointQuery query) := by
  intro left right leftCompatible rightCompatible observational assignment
  have restrictedEquivalent := identifiable
    (spec.restrictModel left) (spec.restrictModel right)
    (spec.restrictModel_compatible left G leftCompatible)
    (spec.restrictModel_compatible right G rightCompatible)
    (spec.restrictModel_observationalAgreement left right observational)
    (spec.restrictAssignment assignment)
  rcases restrictedEquivalent with ⟨restrictedEquivalent⟩
  exact ⟨ProbabilityResult.trans
    (spec.liftJointQuery_denote left query assignment)
    (ProbabilityResult.trans restrictedEquivalent
      (ProbabilityResult.symm
        (spec.liftJointQuery_denote right query assignment)))⟩

/-- Conditional identifiability, including support, survives terminal learning. -/
theorem TerminalVariableSpec.liftConditionalQuery_identifiable
    (spec : TerminalVariableSpec S) (G : ObservedGraph S)
    (query : ConditionalKernelQuery S)
    (identifiable : TypeTheoreticConditionalIdentifiable G query) :
    TypeTheoreticConditionalIdentifiable (spec.extendObservedGraph G)
      (spec.liftConditionalQuery query) := by
  intro left right leftCompatible rightCompatible observational assignment
    leftSupported rightSupported
  let leftBridge := spec.liftConditionalQuery_denote left query assignment
  let rightBridge := spec.liftConditionalQuery_denote right query assignment
  have restrictedLeftSupported : query.sourceTerm.SupportedAt
      (spec.restrictModel left) (spec.restrictAssignment assignment) := by
    rcases leftSupported with ⟨value, supported⟩
    exact ⟨value, ProbabilityResult.trans
      (ProbabilityResult.symm leftBridge) supported⟩
  have restrictedRightSupported : query.sourceTerm.SupportedAt
      (spec.restrictModel right) (spec.restrictAssignment assignment) := by
    rcases rightSupported with ⟨value, supported⟩
    exact ⟨value, ProbabilityResult.trans
      (ProbabilityResult.symm rightBridge) supported⟩
  have restrictedEquivalent := identifiable
    (spec.restrictModel left) (spec.restrictModel right)
    (spec.restrictModel_compatible left G leftCompatible)
    (spec.restrictModel_compatible right G rightCompatible)
    (spec.restrictModel_observationalAgreement left right observational)
    (spec.restrictAssignment assignment) restrictedLeftSupported
      restrictedRightSupported
  rcases restrictedEquivalent with ⟨restrictedEquivalent⟩
  exact ⟨ProbabilityResult.trans leftBridge
    (ProbabilityResult.trans restrictedEquivalent
      (ProbabilityResult.symm rightBridge))⟩

namespace TerminalVariableSpec

/--
Run published completeness on the internally proved learned identifiability
statement, then realize every resulting modal rule cell by record operations.
-/
noncomputable def liftJointQuery_operationRealized
    (spec : TerminalVariableSpec S) (G : ObservedGraph S)
    (complete : PublishedCompleteness spec.extendSignature
      (spec.extendObservedGraph G))
    (sound : PublishedSoundness spec.extendSignature
      (spec.extendObservedGraph G))
    (query : JointKernelQuery S)
    (identifiable : TypeTheoreticIdentifiable G query) :
    OperationRealizedJointCertificate sound (spec.liftJointQuery query) :=
  ((transport_joint_completeness complete (spec.liftJointQuery query)
    (spec.liftJointQuery_identifiable G query identifiable)).toModal).toOperationRealized
      sound

noncomputable def liftConditionalQuery_operationRealized
    (spec : TerminalVariableSpec S) (G : ObservedGraph S)
    (complete : PublishedCompleteness spec.extendSignature
      (spec.extendObservedGraph G))
    (sound : PublishedSoundness spec.extendSignature
      (spec.extendObservedGraph G))
    (query : ConditionalKernelQuery S)
    (identifiable : TypeTheoreticConditionalIdentifiable G query) :
    OperationRealizedConditionalCertificate sound
      (spec.liftConditionalQuery query) :=
  ((transport_conditional_completeness complete (spec.liftConditionalQuery query)
    (spec.liftConditionalQuery_identifiable G query identifiable)).toModal).toOperationRealized
      sound

end TerminalVariableSpec

namespace CausalEditTransition

/--
The complete joint proof package around one learning/forgetting cycle.
Its certificate concerns the lifted query in the learned signature; the two
transition equalities prevent unrelated dependent-signature edits from being
substituted for learning or forgetting.
-/
structure TerminalLearningJointTransport
    (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (learnedName restoredName : String) (G : ObservedGraph S)
    (sound : PublishedSoundness spec.extendSignature
      (spec.extendObservedGraph G)) (query : JointKernelQuery S) where
  learning : CausalEditTransition S spec.extendSignature
  learning_is_terminal : learning = learnTerminal mode spec learnedName
  sourceCompatible : mode.CompatibleWith G
  learnedCompatible : learning.target.CompatibleWith
    (spec.extendObservedGraph G)
  certificate : OperationRealizedJointCertificate sound
    (spec.liftJointQuery query)
  forgetting : CausalEditTransition spec.extendSignature S
  forgetting_is_terminal :
    forgetting = forgetTerminal mode spec learnedName restoredName
  restoredCompatible : forgetting.target.CompatibleWith G
  currentBeliefPreserved : forall event : S.Assignment -> Bool,
    QProb.Equiv
      (learning.target.record.observedValue (spec.liftEvent event))
      (mode.record.observedValue event)

structure TerminalLearningConditionalTransport
    (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (learnedName restoredName : String) (G : ObservedGraph S)
    (sound : PublishedSoundness spec.extendSignature
      (spec.extendObservedGraph G)) (query : ConditionalKernelQuery S) where
  learning : CausalEditTransition S spec.extendSignature
  learning_is_terminal : learning = learnTerminal mode spec learnedName
  sourceCompatible : mode.CompatibleWith G
  learnedCompatible : learning.target.CompatibleWith
    (spec.extendObservedGraph G)
  certificate : OperationRealizedConditionalCertificate sound
    (spec.liftConditionalQuery query)
  forgetting : CausalEditTransition spec.extendSignature S
  forgetting_is_terminal :
    forgetting = forgetTerminal mode spec learnedName restoredName
  restoredCompatible : forgetting.target.CompatibleWith G
  currentBeliefPreserved : forall event : S.Assignment -> Bool,
    QProb.Equiv
      (learning.target.record.observedValue (spec.liftEvent event))
      (mode.record.observedValue event)

noncomputable def terminalLearningJointTransport
    (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (learnedName restoredName : String) (G : ObservedGraph S)
    (complete : PublishedCompleteness spec.extendSignature
      (spec.extendObservedGraph G))
    (sound : PublishedSoundness spec.extendSignature
      (spec.extendObservedGraph G))
    (query : JointKernelQuery S)
    (currentCompatible : mode.CompatibleWith G)
    (identifiable : TypeTheoreticIdentifiable G query) :
    TerminalLearningJointTransport mode spec learnedName restoredName G sound
      query where
  learning := learnTerminal mode spec learnedName
  learning_is_terminal := rfl
  sourceCompatible := currentCompatible
  learnedCompatible :=
    spec.extendModel_compatible mode.record.model G currentCompatible
  certificate := spec.liftJointQuery_operationRealized G complete sound query
    identifiable
  forgetting := forgetTerminal mode spec learnedName restoredName
  forgetting_is_terminal := rfl
  restoredCompatible := currentCompatible
  currentBeliefPreserved := fun event =>
    learnTerminal_observedValue_old mode spec learnedName event

noncomputable def terminalLearningConditionalTransport
    (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (learnedName restoredName : String) (G : ObservedGraph S)
    (complete : PublishedCompleteness spec.extendSignature
      (spec.extendObservedGraph G))
    (sound : PublishedSoundness spec.extendSignature
      (spec.extendObservedGraph G))
    (query : ConditionalKernelQuery S)
    (currentCompatible : mode.CompatibleWith G)
    (identifiable : TypeTheoreticConditionalIdentifiable G query) :
    TerminalLearningConditionalTransport mode spec learnedName restoredName G
      sound query where
  learning := learnTerminal mode spec learnedName
  learning_is_terminal := rfl
  sourceCompatible := currentCompatible
  learnedCompatible :=
    spec.extendModel_compatible mode.record.model G currentCompatible
  certificate := spec.liftConditionalQuery_operationRealized G complete sound
    query identifiable
  forgetting := forgetTerminal mode spec learnedName restoredName
  forgetting_is_terminal := rfl
  restoredCompatible := currentCompatible
  currentBeliefPreserved := fun event =>
    learnTerminal_observedValue_old mode spec learnedName event

end CausalEditTransition

end Causality
end Thesis
