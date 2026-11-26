import Thesis.CausalTransport.CertifiedModeInference

namespace Thesis.Causality.ModeQueryPolicy
open Probability

/-!
# Executable presentations of certificate-backed mode inference

The public inference adapter retains class membership, local support and a
uniform soundness map in a dependent certificate. Some of those maps live
in `Type`, so the existing constructive soundness assembly is marked
noncomputable. A command-line client only needs the formula, value and
diagnostic branch. This module computes that presentation directly and
proves that it is exactly the projection of the certificate-backed adapter.

The worker below is not another certificate constructor. It accepts neither
raw overrides nor supplied endpoints, and its result cannot be used as a
class-wide proof. The equality theorem connects every displayed successful
branch with the existing indexed answer, without compiling its proof data
into the executable or assuming soundness of a second identification engine.
-/

variable {S : ObservedSignature.{0}}

/-- Run the permission, guarded-ID and printed-support computations needed
for the ordinary population answer, erasing only the certificate payload.
The table read is the generative population law, even when the mode's
current latent belief differs from that population prior. -/
def jointPresentation (policy : ModeQueryPolicy S) (query : JointKernelQuery S)
    (reference : S.Assignment) : ModeIndexedAnswer S :=
  if policy.jointAdmissible query then
    match identifyGuardedJointKernel policy.graph query with
    | .identified term =>
        match query.sourceTerm.supported? policy.mode.model reference,
          term.supported? policy.mode.model reference with
        | some _, some _ => .identified term
            (term.observationalDenote policy.mode.model.observationalDist reference)
        | _, _ => .undefined
    | .failed failure => .failed failure
    | .unfinished => .unfinished
  else .modeUnsupported

/-- The executable computation is the literal presentation of the indexed
public answer with no override or bounds fallback. This theorem covers
diagnostics and undefined values as well as successful identification. -/
theorem jointPresentation_certified (policy : ModeQueryPolicy S)
    (query : JointKernelQuery S) (reference : S.Assignment) :
    displayAnswer (policy.identifyJoint query reference none none) =
      policy.jointPresentation query reference := by
  by_cases admitted : policy.jointAdmissible query = true
  · -- Simplification removes the absent override and bounds before splitting
    -- the engine's dependent match.
    simp only [identifyJoint, jointPresentation, admitted, if_true]
    split
    · split <;> simp_all only [displayAnswer, CertifiedQuery.FormulaCertificate.At.value,
        jointFormulaCertificate]
    · simp_all only [displayAnswer]
    · simp_all only [displayAnswer]
  · simp [identifyJoint, jointPresentation, admitted, displayAnswer]

/-- Use the same executable presentation after representing the current
belief by its full shared-response law. The conservative graph is computed
from that representation, rather than inherited from the population SCM. -/
def currentJointPresentation (policy : ModeQueryPolicy S) (query : JointKernelQuery S)
    (reference : S.Assignment) : ModeIndexedAnswer S :=
  let represented : ModeQueryPolicy S :=
    { mode := ⟨policy.mode.currentModel, policy.mode.currentModel.prior⟩
      intervenable := policy.intervenable }
  represented.jointPresentation query reference

/-- Current-belief display has the same connection to its own represented
model's certificate. A population success need not remain a success here. -/
theorem currentJointPresentation_certified (policy : ModeQueryPolicy S)
    (query : JointKernelQuery S) (reference : S.Assignment) :
    displayAnswer (policy.identifyCurrentJoint query reference) =
      policy.currentJointPresentation query reference :=
  jointPresentation_certified _ _ _

/-- The same conservative representation supports conditional identification.
The underlying adapter checks the source conditioner in the represented
model as well as the printed observational formula's local support. -/
noncomputable def identifyCurrentConditional (policy : ModeQueryPolicy S)
    (query : ConditionalKernelQuery S) (reference : S.Assignment) :
    CertifiedQuery.Answer query.sourceTerm policy.mode.currentModel reference :=
  let represented : ModeQueryPolicy S :=
    { mode := ⟨policy.mode.currentModel, policy.mode.currentModel.prior⟩
      intervenable := policy.intervenable }
  represented.identifyConditional query reference none

/-- Direct evaluation of the current-belief conditional. Unsupported
conditioning stays `none`; a defined zero remains a rational result.
The computation answers the supplied model, independently of graphical
identification or access to a physical experiment. -/
def evaluateCurrentConditional (policy : ModeQueryPolicy S) (query : ConditionalKernelQuery S)
    (reference : S.Assignment) : ProbabilityResult.Result :=
  query.sourceTerm.denote policy.mode.currentModel reference

end Thesis.Causality.ModeQueryPolicy
