import Thesis.Causality.ModeIndexedIdentification
import Thesis.Causality.CurrentBelief
import Thesis.CausalTransport.GuardedPrintedSoundness

namespace Thesis.Causality
open Probability CertifiedQuery

/-!
# Public mode inference with an explicit semantic target

The low-level graph program proposes a formula.  Here its literal successful
output is turned into an applied, class-indexed certificate using the proved
guarded-ID soundness theorem.  Its class consists of models with the declared
projected graph; its local domain is the printed expression's actual support.
Thus observational zeros are retained and a missing conditioner yields an
undefined result, rather than an invented number or a positivity assumption.

Population inference always reads the stored SCM's prior.  A separate current-
belief entry point first constructs the intervention-preserving shared-response
SCM.  Its conservative graph can fail to identify a query even when the
original population graph identified it.  Direct evaluation under the fully
specified mode is a third, explicitly model-conditional operation: a computed
answer in that one model is never promoted to class-wide identification.

Formula replacements and bound fallbacks are accepted only with certificates
already applied to this exact source, model and reference.  There is no path
from raw formula syntax or a pair of rational endpoints to a certified answer.
-/

variable {S : ObservedSignature.{0}}

/-- Inspect the partial computation to construct its value-and-equality
witness.  This is finite case analysis on an `Option`, not choice from a
propositional existence statement. -/
def ProbabilityTerm.supported? (term : ProbabilityTerm S) (model : ExactModel S)
    (reference : S.Assignment) : Option (term.SupportedAt model reference) :=
  match computed : term.denote model reference with
  | none => none
  | some value => some ⟨value, by rw [computed]; exact .value (QProb.equiv_refl _)⟩

/-- The engine's soundness proof is uniform over the projected graph class.
The domain carries the exact support witness of its literal printed formula;
it need not require positivity of the complete observational joint. -/
noncomputable def jointFormulaCertificate (graph : ObservedGraph S)
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel graph query = .identified term) :
    FormulaCertificate query.sourceTerm where
  models := fun model => HasProjectedGraph model graph
  domain := fun model reference => term.SupportedAt model reference
  formula := term
  actionFree := identifyGuardedJointKernel_identified_actionFree graph query result
  sound := fun model member reference supported =>
    identifyGuardedJointKernel_soundAt_of_printed_support query result model member reference supported

/-- Conditional certification additionally keeps the original causal
conditioner's support. A defined printed quotient does not create support
for a target that was never defined in the intervened model. -/
noncomputable def conditionalFormulaCertificate (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel graph query = .identified term) :
    FormulaCertificate query.sourceTerm where
  models := fun model => HasProjectedGraph model graph
  domain := fun model reference =>
    query.sourceTerm.SupportedAt model reference × term.SupportedAt model reference
  formula := term
  actionFree := identifyGuardedConditionalKernel_identified_actionFree graph query result
  sound := fun model member reference supported =>
    identifyGuardedConditionalKernel_soundAt_of_printed_support query result model member reference
      supported.1 supported.2

namespace ModeQueryPolicy

/-- Population identification with permission checking and certified optional
extensions. Every successful numerical branch retains the theorem that
licenses it; diagnostic branches make no numerical causal assertion. -/
noncomputable def identifyJoint (policy : ModeQueryPolicy S) (query : JointKernelQuery S)
    (reference : S.Assignment)
    (bounds : Option (BoundsCertificate.At query.sourceTerm policy.mode.model reference))
    (replacement : Option (FormulaCertificate.At query.sourceTerm policy.mode.model reference)) :
    Answer query.sourceTerm policy.mode.model reference :=
  if policy.jointAdmissible query then
    match replacement with
    | some evidence =>
        match evidence.value with
        | none => .undefined
        | some _ => .identified evidence
    | none =>
        match result : identifyGuardedJointKernel policy.graph query with
        | .identified term =>
            match term.supported? policy.mode.model reference with
            | none => .undefined
            | some supported =>
                .identified ⟨jointFormulaCertificate policy.graph query result,
                  fun _ _ => rfl, supported⟩
        | .failed failure =>
            match bounds with
            | some evidence => .bounded evidence
            | none => .failed failure
        | .unfinished => .unfinished
  else .modeUnsupported

/-- Conditional population identification follows the same certificate
boundary, and checks both source and printed support before accepting a
numerical result. Bounds are meaningful only when their target is defined. -/
noncomputable def identifyConditional (policy : ModeQueryPolicy S)
    (query : ConditionalKernelQuery S) (reference : S.Assignment)
    (bounds : Option (BoundsCertificate.At query.sourceTerm policy.mode.model reference)) :
    Answer query.sourceTerm policy.mode.model reference :=
  if policy.conditionalAdmissible query then
    match result : identifyGuardedConditionalKernel policy.graph query with
    | .identified term =>
        match query.sourceTerm.supported? policy.mode.model reference,
          term.supported? policy.mode.model reference with
        | some sourceSupported, some printedSupported =>
            .identified ⟨conditionalFormulaCertificate policy.graph query result,
              fun _ _ => rfl, ⟨sourceSupported, printedSupported⟩⟩
        | _, _ => .undefined
    | .failed failure =>
        match bounds with
        | some evidence => .bounded evidence
        | none => .failed failure
    | .unfinished => .unfinished
  else .modeUnsupported

/-- Apply graphical identification to a valid representation of the current
belief. Experimental access is transported unchanged; the represented graph
and observed law are both read from the newly constructed SCM. -/
noncomputable def identifyCurrentJoint (policy : ModeQueryPolicy S)
    (query : JointKernelQuery S) (reference : S.Assignment) :
    Answer query.sourceTerm policy.mode.currentModel reference :=
  let represented : ModeQueryPolicy S :=
    { mode := ⟨policy.mode.currentModel, policy.mode.currentModel.prior⟩
      intervenable := policy.intervenable }
  represented.identifyJoint query reference none none

/-- Direct calculation in one fully specified epistemic model. This API
returns the target value itself, not a formula certificate over a graph class.
The current-belief preservation theorem relates it to executed interventions. -/
def evaluateCurrentJoint (policy : ModeQueryPolicy S)
    (query : JointKernelQuery S) (reference : S.Assignment) : ProbabilityResult.Result :=
  query.sourceTerm.denote policy.mode.currentModel reference

/-- Access restrictions are checked before any identification work. A denied
action is a policy result, independently of its graphical identifiability. -/
theorem identifyJoint_modeUnsupported (policy : ModeQueryPolicy S)
    (query : JointKernelQuery S) (reference : S.Assignment)
    (bounds : Option (BoundsCertificate.At query.sourceTerm policy.mode.model reference))
    (replacement : Option (FormulaCertificate.At query.sourceTerm policy.mode.model reference))
    (denied : policy.jointAdmissible query = false) :
    policy.identifyJoint query reference bounds replacement = .modeUnsupported := by
  simp [identifyJoint, denied]

end ModeQueryPolicy

namespace WorkspaceQueryPolicy

/-- Workspace access is interpreted through the finished population policy.
The compact intervention note does not silently widen experimental access. -/
noncomputable def identifyJoint (policy : WorkspaceQueryPolicy S)
    (query : JointKernelQuery S) (reference : S.Assignment)
    (bounds : Option (BoundsCertificate.At query.sourceTerm policy.state.model reference))
    (replacement : Option (FormulaCertificate.At query.sourceTerm policy.state.model reference)) :
    Answer query.sourceTerm policy.state.model reference :=
  policy.toQueryPolicy.identifyJoint query reference bounds replacement

end WorkspaceQueryPolicy
end Thesis.Causality
