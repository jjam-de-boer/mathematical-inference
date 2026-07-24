import Thesis.Causality.ExecutedMultiworld

namespace Thesis
namespace Causality

open Probability

universe u

/-!
Modal construction for finite counterfactual semantics.

The direct `TwinNetwork` remains the independent reference semantics. This
module supplies the proof-carrying modal construction around it: structural
intervention transitions for every potential-outcome occurrence, two ordered
executions ending in actual epistemic records, and an
abduction-action-prediction theorem connecting those records to both query and
twin-network semantics.
-/

/-! ## Modal traces for arbitrary finite counterfactual events -/

structure ModalCounterfactualAtomTrace {S : ObservedSignature}
    (mode : CausalMode S)
    (atom : CounterfactualAtom S) where
  execution : AtomicIntervention.Execution mode
  realizes : execution = AtomicIntervention.compile mode atom.action
  semantics : AtomicIntervention.Execution.RealizesEvaluation execution
    (fun assignment => mode.record.model.evalUnder atom.action assignment)
  deterministicSemantics :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation execution
      (fun assignment => mode.record.model.evalUnder atom.action assignment)
  referenceTransition : CausalEditTransition S
    (SurgicalIntervention.signature mode.record.model atom.action)
  referenceRealizes : referenceTransition =
    SurgicalIntervention.transition mode atom.action
    "potential-outcome"

noncomputable def ModalCounterfactualAtomTrace.canonical (mode : CausalMode S)
    (atom : CounterfactualAtom S) :
    ModalCounterfactualAtomTrace mode atom where
  execution := AtomicIntervention.compile mode atom.action
  realizes := rfl
  semantics := AtomicIntervention.compileRealizes mode atom.action
  deterministicSemantics :=
    AtomicIntervention.compileDeterministicRealizes mode atom.action
  referenceTransition := SurgicalIntervention.transition mode atom.action
    "potential-outcome"
  referenceRealizes := rfl

inductive ModalCounterfactualEventTrace {S : ObservedSignature}
    (mode : CausalMode S) : CounterfactualEvent S -> Type 1
  | truth : ModalCounterfactualEventTrace mode .truth
  | falsity : ModalCounterfactualEventTrace mode .falsity
  | atomic (counterfactualAtom : CounterfactualAtom S)
      (trace : ModalCounterfactualAtomTrace mode counterfactualAtom) :
      ModalCounterfactualEventTrace mode (.atom counterfactualAtom)
  | conj {left right : CounterfactualEvent S}
      (leftTrace : ModalCounterfactualEventTrace mode left)
      (rightTrace : ModalCounterfactualEventTrace mode right) :
      ModalCounterfactualEventTrace mode (.conj left right)
  | disj {left right : CounterfactualEvent S}
      (leftTrace : ModalCounterfactualEventTrace mode left)
      (rightTrace : ModalCounterfactualEventTrace mode right) :
      ModalCounterfactualEventTrace mode (.disj left right)
  | neg {event : CounterfactualEvent S}
      (trace : ModalCounterfactualEventTrace mode event) :
      ModalCounterfactualEventTrace mode (.neg event)

namespace ModalCounterfactualEventTrace

noncomputable def canonical (mode : CausalMode S) :
    (event : CounterfactualEvent S) -> ModalCounterfactualEventTrace mode event
  | CounterfactualEvent.truth => .truth
  | CounterfactualEvent.falsity => .falsity
  | CounterfactualEvent.atom atom => .atomic atom (.canonical mode atom)
  | CounterfactualEvent.conj left right =>
      .conj (canonical mode left) (canonical mode right)
  | CounterfactualEvent.disj left right =>
      .disj (canonical mode left) (canonical mode right)
  | CounterfactualEvent.neg event => .neg (canonical mode event)

end ModalCounterfactualEventTrace

structure ModalCounterfactualQueryTrace (mode : CausalMode S)
    (query : CounterfactualQuery S) where
  outcome : ModalCounterfactualEventTrace mode query.outcome
  condition : ModalCounterfactualEventTrace mode query.condition
  combinedOccurrences :
    (occurrence : Fin query.combinedEvent.atoms.length) ->
      ModalCounterfactualAtomTrace mode
        (query.combinedEvent.atoms.get occurrence)

noncomputable def ModalCounterfactualQueryTrace.canonical (mode : CausalMode S)
    (query : CounterfactualQuery S) : ModalCounterfactualQueryTrace mode query where
  outcome := ModalCounterfactualEventTrace.canonical mode query.outcome
  condition := ModalCounterfactualEventTrace.canonical mode query.condition
  combinedOccurrences := fun occurrence =>
    ModalCounterfactualAtomTrace.canonical mode
      (query.combinedEvent.atoms.get occurrence)

/-! ## Combined occurrence-indexed modal construction -/

/--
The primary modal multiworld certificate retains both independently executed
construction routes. Neither endpoint is supplied in advance: each is the
target of its recorded dependent-signature causal-edit path.
-/
structure ModalCombinedCounterfactualConstruction
    (mode : CausalMode S) (query : CounterfactualQuery S) where
  fromFactual :
    ExecutedOccurrenceConstruction mode query.combinedEvent
  fromFactual_eq : fromFactual =
    ExecutedOccurrenceConstruction.canonical mode query.combinedEvent
  fromEmpty :
    FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent
  fromEmpty_eq : fromEmpty =
    FromEmptyExecutedOccurrenceConstruction.canonical
      mode query.combinedEvent

noncomputable def ModalCombinedCounterfactualConstruction.canonical
    (mode : CausalMode S) (query : CounterfactualQuery S) :
    ModalCombinedCounterfactualConstruction mode query where
  fromFactual :=
    ExecutedOccurrenceConstruction.canonical mode query.combinedEvent
  fromFactual_eq := rfl
  fromEmpty :=
    FromEmptyExecutedOccurrenceConstruction.canonical
      mode query.combinedEvent
  fromEmpty_eq := rfl

/--
One retained trace occurrence is matched to its contribution in both complete
atomic construction routes. The actions are occurrence-indexed, so repeated
syntactic atoms remain distinct even when their action functions agree.
-/
structure ModalCounterfactualOccurrencePathMatch
    {S : ObservedSignature} {mode : CausalMode S}
    {query : CounterfactualQuery S}
    (trace : ModalCounterfactualQueryTrace mode query)
    (construction : ModalCombinedCounterfactualConstruction mode query)
    (occurrence : Fin query.combinedEvent.atoms.length) : Prop where
  traceCanonical :
    (trace.combinedOccurrences occurrence).execution =
      AtomicIntervention.compile mode
        (query.combinedEvent.atoms.get occurrence).action
  fromFactualCanonical :
    construction.fromFactual.atomic =
      AtomicIntervention.compile
        construction.fromFactual.linked.reindexBeliefTransition.target
        construction.fromFactual.linked.combinedAction
  fromEmptyCanonical :
    construction.fromEmpty.atomic =
      AtomicIntervention.compile
        construction.fromEmpty.linked.reindexBeliefTransition.target
        construction.fromEmpty.linked.combinedAction
  fromFactualEndpoint : forall
      (assignment : mode.record.model.latent.Assignment)
      (node : Fin S.count),
    OccurrenceMultiworld.Encoding.decodeAssignment
        construction.fromFactual.World
        (construction.fromFactual.coordinates.untransportObserved
          (construction.fromFactual.target.record.model.eval
            (construction.fromFactual.endpointAssignment assignment)))
        ⟨.counterfactual occurrence, node⟩ =
      mode.record.model.evalUnder
        (query.combinedEvent.atoms.get occurrence).action assignment node
  fromEmptyEndpoint : forall
      (assignment : mode.record.model.latent.Assignment)
      (node : Fin S.count),
    OccurrenceMultiworld.Encoding.decodeAssignment
        construction.fromEmpty.World
        (construction.fromEmpty.coordinates.untransportObserved
          (construction.fromEmpty.target.record.model.eval
            (construction.fromEmpty.endpointAssignment assignment)))
        ⟨.counterfactual occurrence, node⟩ =
      mode.record.model.evalUnder
        (query.combinedEvent.atoms.get occurrence).action assignment node

theorem ModalCombinedCounterfactualConstruction.occurrencePathMatch
    {S : ObservedSignature} {mode : CausalMode S}
    {query : CounterfactualQuery S}
    (trace : ModalCounterfactualQueryTrace mode query)
    (construction : ModalCombinedCounterfactualConstruction mode query)
    (occurrence : Fin query.combinedEvent.atoms.length) :
    ModalCounterfactualOccurrencePathMatch trace construction occurrence where
  traceCanonical := (trace.combinedOccurrences occurrence).realizes
  fromFactualCanonical := construction.fromFactual.atomic_eq
  fromEmptyCanonical := construction.fromEmpty.atomic_eq
  fromFactualEndpoint := fun assignment node =>
    construction.fromFactual.endpoint_counterfactualOccurrence
      assignment occurrence node
  fromEmptyEndpoint := fun assignment node =>
    construction.fromEmpty.endpoint_counterfactualOccurrence
      assignment occurrence node

/-- Both actual endpoints compute the same occurrence assignment. -/
theorem ModalCombinedCounterfactualConstruction.endpointEvaluations_agree
    (construction : ModalCombinedCounterfactualConstruction mode query)
    (assignment : mode.record.model.latent.Assignment) :
    construction.fromFactual.coordinates.untransportObserved
        (construction.fromFactual.target.record.model.eval
          (construction.fromFactual.endpointAssignment assignment)) =
      construction.fromEmpty.coordinates.untransportObserved
        (construction.fromEmpty.target.record.model.eval
          (construction.fromEmpty.endpointAssignment assignment)) :=
  executedRoutes_endpoint_eval_agree
    construction.fromFactual construction.fromEmpty assignment

/-- Denominator read from the record produced by atomic execution. -/
noncomputable def
    ModalCombinedCounterfactualConstruction.endpointDenominator
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    QProb :=
  construction.fromFactual.denominator

/-- Numerator read from the record produced by atomic execution. -/
noncomputable def ModalCombinedCounterfactualConstruction.endpointNumerator
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    QProb :=
  construction.fromFactual.numerator

noncomputable def ModalCombinedCounterfactualConstruction.endpointDenote
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    ProbabilityResult.Result :=
  construction.fromFactual.denote

theorem ModalCombinedCounterfactualConstruction.endpointDenominator_equiv
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    QProb.Equiv construction.endpointDenominator
      (query.denominator mode.record.model) :=
  construction.fromFactual.denominator_equiv

theorem ModalCombinedCounterfactualConstruction.endpointNumerator_equiv
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    QProb.Equiv construction.endpointNumerator
      (query.numerator mode.record.model) :=
  construction.fromFactual.numerator_equiv

theorem ModalCombinedCounterfactualConstruction.emptyDenominator_equiv
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    QProb.Equiv construction.fromEmpty.denominator
      construction.endpointDenominator :=
  QProb.equiv_symm
    (executedRoutes_denominator_equiv
      construction.fromFactual construction.fromEmpty)

theorem ModalCombinedCounterfactualConstruction.emptyNumerator_equiv
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    QProb.Equiv construction.fromEmpty.numerator
      construction.endpointNumerator :=
  QProb.equiv_symm
    (executedRoutes_numerator_equiv
      construction.fromFactual construction.fromEmpty)

noncomputable def ModalCombinedCounterfactualConstruction.semanticAgreement
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    ProbabilityResult.Equivalent construction.endpointDenote
      (query.denote mode.record.model) :=
  construction.fromFactual.semanticAgreement

noncomputable def ModalCombinedCounterfactualConstruction.endpoint_semantics
    (construction : ModalCombinedCounterfactualConstruction mode query) :
    ProbabilityResult.Equivalent
      construction.endpointDenote
      (query.denote mode.record.model) :=
  construction.semanticAgreement

/--
For a supported one-action query, the executed modal endpoint also agrees with
the independently defined shared-root twin network.
-/
noncomputable def
    ModalCombinedCounterfactualConstruction.singleAction_semantics_eq_twinNetwork
    (mode : CausalMode S) (evidence : S.Assignment -> Bool)
    (hEvidence : mode.record.model.CounterfactualSupported evidence)
    (action : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool)
    (construction : ModalCombinedCounterfactualConstruction mode
      (CounterfactualQuery.singleAction evidence action outcome)) :
    ProbabilityResult.Equivalent
      construction.endpointDenote
      (some
        ((mode.record.model.twinNetwork action).abductedCounterfactualValue
          evidence hEvidence outcome)) :=
  ProbabilityResult.trans construction.semanticAgreement
    (CounterfactualQuery.singleAction_denote_eq_twinNetwork
      mode.record.model evidence hEvidence action outcome)

/-! ## Abduction, action and prediction -/

namespace AbductionActionPrediction

def latentEvidencePositive (M : ExactModel S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence) :
    M.prior.EventPositive (fun u => evidence (M.eval u)) := by
  simpa [FiniteLatentSCM.CounterfactualSupported,
    FiniteLatentSCM.observationalDist, FiniteProbRecord.EventPositive,
    FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] using hEvidence

def initialMode (M : ExactModel S) : CausalMode S :=
  ⟨"factual", CausalEpistemicRecord.initial M⟩

/-- Abduction updates only the epistemic belief over shared latent roots. -/
def abduction (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence) : CausalTransition S :=
  CausalTransition.conditioning "factual" "abducted"
    (CausalEpistemicRecord.initial M) (fun u => evidence (M.eval u))
    (latentEvidencePositive M evidence hEvidence)

/-- The compact, one-shot surgery retained as a reference implementation. -/
def compactAction (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) :
    CausalEditTransition S (SurgicalIntervention.signature M intervention) :=
  SurgicalIntervention.transition
    (abduction M evidence hEvidence).target intervention "acted"

/-- The primitive action stage: set equations, then cut each incoming link. -/
def atomicAction (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) :
    AtomicIntervention.Execution (abduction M evidence hEvidence).target :=
  AtomicIntervention.compile (abduction M evidence hEvidence).target intervention

/-- The action stage of AAP is, by definition, the compiled atomic edit path. -/
abbrev action (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) :=
  atomicAction M evidence hEvidence intervention

def atomicActionRealizes (M : ExactModel S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) :
    AtomicIntervention.Execution.RealizesEvaluation
      (atomicAction M evidence hEvidence intervention)
      (fun assignment => M.evalUnder intervention assignment) :=
  AtomicIntervention.compileRealizes
    (abduction M evidence hEvidence).target intervention

noncomputable def atomicActionDeterministicRealizes
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) :
    AtomicIntervention.Execution.DeterministicRealizesEvaluation
      (atomicAction M evidence hEvidence intervention)
      (fun assignment => M.evalUnder intervention assignment) :=
  AtomicIntervention.compileDeterministicRealizes
    (abduction M evidence hEvidence).target intervention

/-- The acted epistemic record at the endpoint of the primitive edit program. -/
noncomputable def actedRecord
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) :
    CausalEpistemicRecord
      (atomicAction M evidence hEvidence intervention).signature :=
  (atomicActionDeterministicRealizes M evidence hEvidence intervention).endpointRecord

/-- The compact surgery is semantically equivalent to the primary atomic action. -/
theorem action_semanticallyEquivalent_compactAction
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (assignment : M.latent.Assignment) :
    Exists fun targetAssignment :
        (atomicAction M evidence hEvidence intervention).target.record.model.latent.Assignment =>
      (atomicAction M evidence hEvidence intervention).target.record.model.eval
          targetAssignment =
        (atomicAction M evidence hEvidence intervention).transportedObserved
          ((compactAction M evidence hEvidence intervention).target.record.model.eval
            assignment) :=
  AtomicIntervention.compile_semanticallyEquivalent_surgery
    (abduction M evidence hEvidence).target intervention assignment

/-- Probability read from the compact one-shot reference constructor. -/
def compactPrediction (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) : QProb :=
  (compactAction M evidence hEvidence intervention).target.record.observedValue
    outcome

theorem compactPrediction_eq_counterfactualValue
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    QProb.Equiv
      (compactPrediction M evidence hEvidence intervention outcome)
      (M.counterfactualValue evidence hEvidence intervention outcome) := by
  exact QProb.equiv_trans
    ((compactAction M evidence hEvidence intervention).target.record.observedDist_probVal
      outcome)
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr
        (M.prior.conditionOn (fun u => evidence (M.eval u))
          (latentEvidencePositive M evidence hEvidence)) _ _ (fun u => by
            congr 1
            exact SurgicalIntervention.eval_eq_evalUnder M intervention u))
      (QProb.equiv_refl _))

noncomputable def prediction (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) : QProb :=
  (actedRecord M evidence hEvidence intervention).observedValue
    (AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointEvent
      (atomicAction M evidence hEvidence intervention) outcome)

/-- Probability read from the atomic endpoint computes AAP. -/
theorem prediction_eq_counterfactualValue
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    QProb.Equiv (prediction M evidence hEvidence intervention outcome)
      (M.counterfactualValue evidence hEvidence intervention outcome) := by
  exact QProb.equiv_trans
    (AtomicIntervention.Execution.DeterministicRealizesEvaluation.endpointRecord_observedValue
        (atomicActionDeterministicRealizes M evidence hEvidence intervention)
        outcome)
    (QProb.equiv_refl _)

/-- The primitive endpoint and compact reference preserve every outcome probability. -/
theorem prediction_eq_compactPrediction
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    QProb.Equiv (prediction M evidence hEvidence intervention outcome)
      (compactPrediction M evidence hEvidence intervention outcome) :=
  QProb.equiv_trans
    (prediction_eq_counterfactualValue M evidence hEvidence intervention outcome)
    (QProb.equiv_symm
      (compactPrediction_eq_counterfactualValue M evidence hEvidence
        intervention outcome))

/-- The query language, modal AAP execution and direct helper agree. -/
noncomputable def singleAction_query_eq_prediction
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    ProbabilityResult.Equivalent
      ((CounterfactualQuery.singleAction evidence intervention outcome).denote M)
      (some (prediction M evidence hEvidence intervention outcome)) :=
  ProbabilityResult.trans
    (CounterfactualQuery.singleAction_denote_eq_counterfactualValue
      M evidence hEvidence intervention outcome)
    (.value (QProb.equiv_symm
      (prediction_eq_counterfactualValue M evidence hEvidence intervention
        outcome)))

/-- The modal AAP execution also agrees with the independent direct twin. -/
theorem prediction_eq_twinNetwork
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    QProb.Equiv (prediction M evidence hEvidence intervention outcome)
      ((M.twinNetwork intervention).abductedCounterfactualValue
        evidence hEvidence outcome) :=
  QProb.equiv_trans
    (prediction_eq_counterfactualValue M evidence hEvidence intervention outcome)
    (QProb.equiv_symm
      ((M.twinNetwork intervention).abductedCounterfactualValue_eq_counterfactualValue
        evidence hEvidence outcome))

end AbductionActionPrediction

end Causality
end Thesis
