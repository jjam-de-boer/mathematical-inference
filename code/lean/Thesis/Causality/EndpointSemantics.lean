import Thesis.Causality.Structural

namespace Thesis
namespace Causality

open Probability

/-!
Current-state semantics for proof-carrying causal edit paths.

The published identification layer interprets kernels at an initial SCM.  The
definitions here instead read a query at an epistemic endpoint: its current
latent belief is retained, its accumulated hard intervention is retained, and
any action named by the queried kernel overrides the same coordinates.  This
is executable endpoint semantics, not a completeness theorem for arbitrary
epistemic programs.
-/

namespace HardIntervention

/-- Apply a later partial intervention over an accumulated intervention. -/
def overlay (base : HardIntervention S)
    (later : (node : Fin S.count) -> Option (S.Value node)) :
    HardIntervention S where
  value := fun node =>
    match later node with
    | some value => some value
    | none => base.value node

@[simp] theorem overlay_some (base : HardIntervention S)
    (later : (node : Fin S.count) -> Option (S.Value node))
    (node : Fin S.count) (value : S.Value node)
    (selected : later node = some value) :
    (base.overlay later).value node = some value := by
  simp [overlay, selected]

@[simp] theorem overlay_none (base : HardIntervention S)
    (later : (node : Fin S.count) -> Option (S.Value node))
    (node : Fin S.count) (unselected : later node = none) :
    (base.overlay later).value node = base.value node := by
  simp [overlay, unselected]

@[simp] theorem overlay_noIntervention (base : HardIntervention S) :
    base.overlay (FiniteLatentSCM.noIntervention S) = base := by
  apply HardIntervention.extensional
  intro node
  simp [overlay, FiniteLatentSCM.noIntervention]

end HardIntervention

/-!
A record-level endpoint query keeps numerator and denominator events explicit.
This form covers ordinary kernels, AAP outcomes and occurrence-indexed
counterfactual queries without pretending that all three share one syntax.
-/
structure EndpointQuery (S : ObservedSignature) where
  numerator : S.Assignment -> Bool
  denominator : S.Assignment -> Bool

namespace EndpointQuery

def denote (query : EndpointQuery S) (record : CausalEpistemicRecord S) :
    ProbabilityResult.Result :=
  ProbabilityResult.divide
    (some (record.observedDist.probVal query.numerator))
    (some (record.observedDist.probVal query.denominator))

def unconditional (event : S.Assignment -> Bool) : EndpointQuery S where
  numerator := event
  denominator := Probability.topEvent

/-- An unconditional endpoint query is exactly the current observed-event value. -/
noncomputable def unconditional_denote
    (record : CausalEpistemicRecord S)
    (event : S.Assignment -> Bool) :
    ProbabilityResult.Equivalent
      ((EndpointQuery.unconditional event).denote record)
      (some (record.observedValue event)) := by
  let denominator :=
    record.observedDist.probVal Probability.topEvent
  have normalized : QProb.Equiv denominator QProb.one := by
    simpa [denominator] using record.observedDist.normalization
  have positive : 0 < denominator.num :=
    (QProb.equiv_num_pos_iff normalized).mpr (by decide)
  simp only [EndpointQuery.denote, EndpointQuery.unconditional,
    ProbabilityResult.divide]
  rw [dif_pos positive]
  exact .value
    (QProb.div_equiv_of_den_equiv_one
      (record.observedDist.probVal event) denominator positive normalized)

end EndpointQuery

namespace CausalEpistemicRecord

/-- Execute one later action while retaining the current model and belief. -/
def executeAction (record : CausalEpistemicRecord S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    CausalEpistemicRecord S :=
  { record with intervention := record.intervention.overlay action }

@[simp] theorem executeAction_model (record : CausalEpistemicRecord S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    (record.executeAction action).model = record.model :=
  rfl

@[simp] theorem executeAction_belief (record : CausalEpistemicRecord S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    (record.executeAction action).belief = record.belief :=
  rfl

@[simp] theorem executeAction_noIntervention
    (record : CausalEpistemicRecord S) :
    record.executeAction (FiniteLatentSCM.noIntervention S) = record := by
  cases record
  unfold executeAction
  rw [HardIntervention.overlay_noIntervention]

/-- Partial probability of an outcome conditioned inside the current state. -/
def eventDenote (record : CausalEpistemicRecord S)
    (outcome condition : S.Assignment -> Bool) :
    ProbabilityResult.Result :=
  (EndpointQuery.mk
    (fun sample => outcome sample && condition sample) condition).denote record

end CausalEpistemicRecord

namespace Kernel

/-- The current epistemic record after applying the kernel's action lock. -/
def endpointActionRecord (kernel : Kernel S)
    (record : CausalEpistemicRecord S) (reference : S.Assignment) :
    CausalEpistemicRecord S :=
  record.executeAction (kernel.intervention reference)

/-- Distribution obtained from the endpoint belief and accumulated action. -/
def endpointDistribution (kernel : Kernel S)
    (record : CausalEpistemicRecord S) (reference : S.Assignment) :
    FiniteProbRecord S.Assignment :=
  (kernel.endpointActionRecord record reference).observedDist

/-- Interpret a kernel at a current epistemic endpoint. -/
def endpointDenote (kernel : Kernel S)
    (record : CausalEpistemicRecord S) (reference : S.Assignment) :
    ProbabilityResult.Result :=
  (EndpointQuery.mk
    (kernel.numeratorEvent reference)
    (kernel.conditionEvent reference)).denote
      (kernel.endpointActionRecord record reference)

/--
At an initial mode, endpoint evaluation recovers the ordinary model-level
kernel distribution eventwise.
-/
theorem endpointDistribution_initial_probVal
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    QProb.Equiv
      ((kernel.endpointDistribution (CausalEpistemicRecord.initial model)
        reference).probVal event)
      ((kernel.distribution model reference).probVal event) := by
  have interventionEqual :
      ((CausalEpistemicRecord.initial model).intervention.overlay
        (kernel.intervention reference)).value =
        kernel.intervention reference := by
    funext node
    cases selected : kernel.intervention reference node with
    | none =>
        simp [HardIntervention.overlay, CausalEpistemicRecord.initial,
          HardIntervention.empty, FiniteLatentSCM.noIntervention, selected]
    | some value =>
        simp [HardIntervention.overlay, selected]
  change QProb.Equiv
    ((model.prior.map
      (model.evalUnder
        ((CausalEpistemicRecord.initial model).intervention.overlay
          (kernel.intervention reference)).value)).probVal event)
    ((kernel.distribution model reference).probVal event)
  rw [interventionEqual]
  by_cases hasAction : kernel.hasAction = true
  · simpa [Kernel.distribution, hasAction,
      FiniteLatentSCM.interventionalDist] using
      (QProb.equiv_refl
        ((model.prior.map
          (model.evalUnder (kernel.intervention reference))).probVal event))
  · have noAction : forall node, kernel.action node = false :=
      (finAny_eq_false_iff kernel.action).mp (by
        cases value : kernel.hasAction <;>
          simp_all [Kernel.hasAction])
    have noIntervention :
        kernel.intervention reference =
          FiniteLatentSCM.noIntervention S := by
      funext node
      simp [Kernel.intervention, FiniteLatentSCM.noIntervention,
        noAction node]
    rw [noIntervention]
    simpa [Kernel.distribution, hasAction,
      FiniteLatentSCM.observationalDist, FiniteLatentSCM.eval] using
      (QProb.equiv_refl
        ((model.prior.map
          (model.evalUnder
            (FiniteLatentSCM.noIntervention S))).probVal event))

/-- Initial endpoint semantics agrees with the existing kernel denotation. -/
noncomputable def endpointDenote_initial
    (model : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      (kernel.endpointDenote (CausalEpistemicRecord.initial model) reference)
      (kernel.denote model reference) :=
  ProbabilityResult.divide_congr
    (.value (kernel.endpointDistribution_initial_probVal model reference
      (kernel.numeratorEvent reference)))
    (.value (kernel.endpointDistribution_initial_probVal model reference
      (kernel.conditionEvent reference)))

end Kernel

namespace JointKernelQuery

def endpointDenote (query : JointKernelQuery S)
    (record : CausalEpistemicRecord S) (reference : S.Assignment) :
    ProbabilityResult.Result :=
  query.operationKernel.endpointDenote record reference

noncomputable def endpointDenote_initial (query : JointKernelQuery S)
    (model : ExactModel S) (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      (query.endpointDenote (CausalEpistemicRecord.initial model) reference)
      (query.sourceTerm.denote model reference) := by
  simpa [endpointDenote, JointKernelQuery.sourceTerm_eq_operationKernel,
    ProbabilityTerm.denote] using
    (query.operationKernel.endpointDenote_initial model reference)

end JointKernelQuery

namespace ConditionalKernelQuery

def endpointDenote (query : ConditionalKernelQuery S)
    (record : CausalEpistemicRecord S) (reference : S.Assignment) :
    ProbabilityResult.Result :=
  query.operationKernel.endpointDenote record reference

noncomputable def endpointDenote_initial (query : ConditionalKernelQuery S)
    (model : ExactModel S) (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      (query.endpointDenote (CausalEpistemicRecord.initial model) reference)
      (query.sourceTerm.denote model reference) := by
  simpa [endpointDenote, ConditionalKernelQuery.sourceTerm_eq_operationKernel,
    ProbabilityTerm.denote] using
    (query.operationKernel.endpointDenote_initial model reference)

end ConditionalKernelQuery

namespace CausalEditPath

/-- Evaluate an explicit endpoint query at the path's certified target record. -/
def endpointDenote
    {S T : ObservedSignature} {source : CausalMode S}
    {target : CausalMode T} (_path : CausalEditPath source target)
    (query : EndpointQuery T) : ProbabilityResult.Result :=
  query.denote target.record

/--
Evaluate a kernel at the actual endpoint certified by a dependent-signature edit
path.  The endpoint record contains the accumulated belief and intervention;
the path is retained as the proof-carrying provenance of that state.
-/
def endpointKernelDenote
    {S T : ObservedSignature} {source : CausalMode S}
    {target : CausalMode T} (_path : CausalEditPath source target)
    (kernel : Kernel T) (reference : T.Assignment) :
    ProbabilityResult.Result :=
  kernel.endpointDenote target.record reference

def endpointJointDenote
    {S T : ObservedSignature} {source : CausalMode S}
    {target : CausalMode T} (path : CausalEditPath source target)
    (query : JointKernelQuery T) (reference : T.Assignment) :
    ProbabilityResult.Result :=
  path.endpointKernelDenote query.operationKernel reference

def endpointConditionalDenote
    {S T : ObservedSignature} {source : CausalMode S}
    {target : CausalMode T} (path : CausalEditPath source target)
    (query : ConditionalKernelQuery T) (reference : T.Assignment) :
    ProbabilityResult.Result :=
  path.endpointKernelDenote query.operationKernel reference

@[simp] theorem nil_endpointKernelDenote
    (mode : CausalMode S) (kernel : Kernel S)
    (reference : S.Assignment) :
    (CausalEditPath.nil mode).endpointKernelDenote kernel reference =
      kernel.endpointDenote mode.record reference :=
  rfl

end CausalEditPath

end Causality
end Thesis
