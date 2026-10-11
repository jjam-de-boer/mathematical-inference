import Thesis.CausalTransport.HiddenDAGIdentification
import Thesis.Examples.HiddenDAGSoundness

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGIdentification

open Probability HiddenDAGCollapse

/-!
# Positive ID/IDC certificates beyond canonical collapsed roots

The five-node hidden graph from `HiddenDAGCollapse` still collapses to a root
with three observed children.  Give every node its own independent unbiased
bit as its equation.  The declared parents are unused in this particular
model, which is allowed: graph compatibility does not require faithfulness.
Its observed joint is positive, but its declared collapsed incidence remains
noncanonical.  Thus the positive-certificate adapter cannot accidentally
obtain its support by requiring canonical graph-model membership.

Both regressions use literal outputs of the corrected identification engines.
The joint query sets the descendant `Y` and asks for `X`; the conditional query
also conditions on `Z`.  Their original full-model semantics are proved by
the generic compiler adapter, not by checking only their numerical answers.
The support-only regression exercises a guarded congruence nested beneath
finite marginalization, evaluation, symmetry, transitivity and endpoint
reindexing.  A final negative check retains the old fixture's observational
zero, so the positivity premise is not made vacuous by the new terminology.
-/

/-- Retain all finite presentations, the original hidden graph and its
independent prior, while using each node's private bit for its equation. -/
def positiveModel : FiniteHiddenDAGSCM signature projection :=
  { HiddenDAGCollapse.model with mechanism := fun _node _parents seed => seed }

/-- Check positivity on the explicit observed assignment enumeration, then
use its completeness.  This avoids a classical quantifier decision over the
dependent assignment function type. -/
theorem positiveModel_positive : positiveModel.ObservationallyPositive := by
  have checked : signature.assignmentEnumeration.all (fun assignment =>
      decide (0 < (positiveModel.observationalDist.probVal
        (FiniteProbRecord.singletonEvent assignment)).num)) = true := by
    decide +kernel
  intro assignment
  exact of_decide_eq_true ((List.all_eq_true.mp checked) assignment
    (signature.assignmentEnumeration_complete assignment))

/-- Mechanism simplification does not delete declared incidence.  The
actual positive model still has a three-child root and is noncanonical. -/
theorem positiveModel_collapsed_not_canonical :
    ¬ positiveModel.toLatentRootSCM.IsCanonicalSemiMarkovian := by
  intro canonical
  have incident :
      positiveModel.toLatentRootSCM.latent.incident u x = true ∧
        positiveModel.toLatentRootSCM.latent.incident u y = true ∧
          positiveModel.toLatentRootSCM.latent.incident u z = true := by
    decide +kernel
  rcases canonical u x y z incident.1 incident.2.1 incident.2.2 with same | same | same
  · exact (by decide : x ≠ y) same
  · exact (by decide : x ≠ z) same
  · exact (by decide : y ≠ z) same

def jointQuery : JointKernelQuery signature where
  outcome := NodeSet.singleton x
  action := NodeSet.singleton y
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

/-- Read the actual successful formula; the fallback makes the read total
and is separately ruled out by `joint_identified`. -/
def jointFormula : ProbabilityTerm signature :=
  match identifyJointKernel projection.observedGraph jointQuery with
  | .identified term => term
  | _ => unitProbabilityTerm signature

theorem joint_identified :
    identifyJointKernel projection.observedGraph jointQuery = .identified jointFormula := by
  rfl

/-- This proof interprets the entire ID certificate in the original full
model.  A hand-provided rule-3 identity or canonical membership is not used. -/
noncomputable def joint_soundAt (assignment : signature.Assignment) :
    positiveModel.TermEquivalentAt jointQuery.sourceTerm jointFormula assignment :=
  identifyJointKernel_hiddenDAG_soundAt jointQuery joint_identified
    positiveModel positiveModel_positive assignment

def conditionalQuery : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton x
  action := NodeSet.singleton y
  condition := NodeSet.singleton z
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

/-- Again retain the actual recursive IDC output rather than prescribing a
formula whose syntax merely happens to have the expected numerical value. -/
def conditionalFormula : ProbabilityTerm signature :=
  match identifyConditionalKernel projection.observedGraph conditionalQuery with
  | .identified term => term
  | _ => unitProbabilityTerm signature

theorem conditional_identified :
    identifyConditionalKernel projection.observedGraph conditionalQuery =
      .identified conditionalFormula := by
  rfl

noncomputable def conditional_soundAt (assignment : signature.Assignment) :
    positiveModel.TermEquivalentAt conditionalQuery.sourceTerm conditionalFormula assignment :=
  identifyConditionalKernel_hiddenDAG_soundAt conditionalQuery conditional_identified
    positiveModel positiveModel_positive assignment

/-- The other model may use different hidden and noise finite sizes.  Its
observed positivity is transferred from the concrete left model. -/
noncomputable def conditional_identifiableAt
    (other : FiniteHiddenDAGSCM signature projection)
    (observational : positiveModel.ObservationalAgreement other)
    (assignment : signature.Assignment) :
    ProbabilityResult.Equivalent (positiveModel.termDenote conditionalQuery.sourceTerm assignment)
      (other.termDenote conditionalQuery.sourceTerm assignment) :=
  identifyConditionalKernel_hiddenDAG_identifiableAt conditionalQuery conditional_identified
    positiveModel other observational positiveModel_positive assignment

/-! ## Recursive support, independent of denotational soundness -/

/-- Nest a genuine guarded congruence under several structural constructors.
Reindexing here is reflexive, but retains an inspectable `eqCongr` node. -/
def nestedDerivation (assignment : signature.Assignment) :=
  let guarded := HiddenDAGSoundness.guardedCongruence
  let marginal := DoCalculusDerivation.marginalizeCongr NodeSet.full guarded
  let evaluated := DoCalculusDerivation.evaluateAtCongr assignment marginal
  DoCalculusDerivation.eqCongr rfl rfl
    (DoCalculusDerivation.trans evaluated (DoCalculusDerivation.symm evaluated))

/-- The support tree includes all finite substitutions and the guarded
factor subtree.  It is reconstructed without calling a soundness theorem or
a certificate's canonical-class support field. -/
noncomputable def nested_supported (assignment : signature.Assignment) :
    HiddenDAGLocalDerivationSupport positiveModel assignment (nestedDerivation assignment) :=
  HiddenDAGLocalDerivationSupport.ofObservationallyPositive positiveModel positiveModel_positive
    (nestedDerivation assignment) ⟨trivial, trivial⟩ assignment

/-- The old zero-containing model is not covered by the positivity adapter.
Every atom lies inside its null `Y = true` cylinder, contradicting positivity
at the all-true reference if the premise were supplied. -/
theorem zero_model_not_positive : ¬ HiddenDAGCollapse.model.ObservationallyPositive := by
  intro positive
  have cylinder :=
    (FiniteHiddenDAGSCM.observationallyPositive_to_collapsed positive).cylinder_positive
      (NodeSet.singleton y) HiddenDAGSoundness.reference
  rw [HiddenDAGCollapse.model.toLatentRootSCM_observationalDist,
    HiddenDAGSoundness.observational_action_is_null] at cylinder
  exact Nat.not_lt_zero 0 cylinder

/-- A literal zero remains outside the positive fragment.  Probability
zeros in general models have not been reclassified as syntactically absent. -/
theorem literal_zero_not_zeroFree : ¬ (ProbabilityTerm.zero (S := signature)).ZeroFree :=
  fun impossible => impossible

end HiddenDAGIdentification
end Examples
end Causality
end Thesis
