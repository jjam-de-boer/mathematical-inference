import Thesis.CausalTransport.HiddenDAGAdmissibleCompleteness
import Thesis.Examples.GuardedIdentificationKernel

namespace Thesis
namespace Causality
namespace Examples
namespace AdmissibleFrontDoorBoundary

open Probability
open GuardedKernelZeroRegression (signature fullGraph projection query guardedFormula guarded_identified)

/-!
# Positive action overlap does not fill a missing front-door mediator cell

Retain the original finite graph `U -> X -> M -> Y`, with hidden `U` also
feeding `Y,Z`.  The observed projection contains `X <-> Y` and the usual
front-door path, with the extra observed `Z` copied from `U`.  The same
guarded joint query asks for `Y,Z` under `do(X)` and succeeds structurally.

Both models now use the deterministic mediator `M = X` and retain an
unbiased hidden `U`, with `X = U` and `Z = U`.  The first sets `Y = false`;
the second sets `Y = M xor U`.  Their entire observed records coincide:
factually `M = X = U`, so `Y` is false in both.  Under `do(X = true)`, however,
`Y = true,Z = false` has probability zero in the first and one half in the
second.  Both action values have positive observed probability, at every
parent context (there are no observed parents of `X`).

Thus the earlier null-action example is not the only obstacle to a raw
zero-class success equivalence.  Even a genuinely admissible external action
does not make the crossed mediator/action conditionals in the front-door
formula meaningful.  The exact guarded output is undefined here, and its
used-conditional predicate correctly rejects the application.  This is why
the papers' restriction to admissible *used conditionals* cannot be dropped
or inferred from the external query boundary alone.

The computations below cover only the explicitly enumerated small Boolean
fixture.  Whole observed-record equality and primitive-domain separation are
proved for the actual original-DAG records.  No classical function equality,
arbitrary conditional completion or hand-picked model-family interface is
assumed.
-/

private def fullU : Fin fullGraph.count := ⟨0, by decide⟩
private def fullX : Fin fullGraph.count := ⟨1, by decide⟩
private def fullM : Fin fullGraph.count := ⟨2, by decide⟩

/-- Preserve all declared graph inputs and independent finite noise records.
Only the mediator equation is changed to the deterministic copy of `X`.
Unused private noises and unused allowed parents remain legitimate SCM data. -/
def constantModel : FiniteHiddenDAGSCM signature projection := {
  GuardedKernelZeroRegression.model with
  mechanism := fun node parents seed =>
    if atU : node.val = 0 then seed
    else if atX : node.val = 1 then
      parents fullU (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, fullU, atX])
    else if atM : node.val = 2 then
      parents fullX (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, fullX, atM])
    else if atY : node.val = 3 then false
    else parents fullU (by
      have bounded : node.val < 5 := node.isLt
      have atZ : node.val = 4 := by omega
      simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, fullU, atZ])
}

/-- The changed outcome equation reads only its two declared parents.
It cancels factually but not when the mediator inherits a hard-set `X`.
All other mechanisms and the complete finite prior stay identical. -/
def parityModel : FiniteHiddenDAGSCM signature projection := {
  constantModel with
  mechanism := fun node parents seed =>
    if atY : node.val = 3 then
      Bool.xor
        (parents fullM (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, fullM, atY]))
        (parents fullU (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, fullU, atY]))
    else constantModel.mechanism node parents seed
}

/-- Set `X = true` and request `Y = true,Z = false`.  The unused mediator
reference coordinate remains true; its value is not a conditioning event. -/
def reference : signature.Assignment := fun node => if node.val = 3 then false else true

/-- Check all actual noise assignments and observed coordinates, then use
the constructive product-enumeration completeness theorem.  The result is
equality of whole records, not merely agreement on the queried outcome. -/
theorem observational_records_equal : constantModel.observationalDist = parityModel.observationalDist := by
  have checked : (FiniteProduct.enumeration 5 (fun _ => Bool) (fun _ => [false, true])).all
      (fun unit => finAll signature.count (fun node => decide
        (constantModel.evalObserved (HardIntervention.empty signature) unit node =
          parityModel.evalObserved (HardIntervention.empty signature) unit node))) = true := by
    decide +kernel
  change constantModel.prior.map (constantModel.evalObserved (HardIntervention.empty signature)) =
    constantModel.prior.map (parityModel.evalObserved (HardIntervention.empty signature))
  apply congrArg (FiniteProbRecord.map constantModel.prior)
  funext unit node
  have listed := FiniteProduct.enumeration_complete 5 (fun _ => Bool) (fun _ => [false, true])
    (by intro _ value; cases value <;> simp) unit
  exact of_decide_eq_true ((finAll_eq_true_iff _).mp ((List.all_eq_true.mp checked) unit listed) node)

theorem observational_agreement : constantModel.ObservationalAgreement parityModel := by
  intro event
  change QProb.Equiv (constantModel.observationalDist.probVal event) (parityModel.observationalDist.probVal event)
  rw [observational_records_equal]
  exact QProb.equiv_refl _

private def valueTest (result : ProbabilityResult.Result) (expected : QProb) : Bool :=
  match result with
  | none => false
  | some value => decide (QProb.Equiv value expected)

/-- Read the displayed representative by case analysis on the actual result;
cross multiplication checks its rational value without choosing a witness
from existence or assuming a particular unreduced denominator. -/
private def equivalentOfValueTest (result : ProbabilityResult.Result) (expected : QProb)
    (checked : valueTest result expected = true) : ProbabilityResult.Equivalent result (some expected) := by
  cases result with
  | none => cases checked
  | some value => exact .value (of_decide_eq_true checked)

noncomputable def constant_effect : ProbabilityResult.Equivalent
    (constantModel.kernelDenote query.operationKernel reference) (some QProb.zero) :=
  equivalentOfValueTest _ _ (by decide +kernel)

noncomputable def parity_effect : ProbabilityResult.Equivalent
    (parityModel.kernelDenote query.operationKernel reference) (some ⟨1, 2, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

/-- With no observed action parents, finite positivity at every displayed
action cell supplies every supported-parent context constructively. -/
private theorem actionAdmissibleEverywhere (model : FiniteHiddenDAGSCM signature projection)
    (checked : signature.assignmentEnumeration.all
      (fun assignment => decide (0 < (model.observationalDist.probVal
        (Kernel.agreesOn (NodeSet.union query.action (signature.actionParents query.action)) assignment)).num)) = true) :
    forall assignment, HiddenDAGAdmissibleDomain.JointAdmissibleAt model query assignment := by
  intro assignment
  apply (model.observationalActionAdmissibleOnParentSupport_iff_collapsed query.action assignment).mpr
  apply Thesis.Causality.ObservationalActionAdmissibleOnParentSupport.of_noParents
  · exact (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  · apply (model.observationalActionAdmissibleAt_iff_collapsed query.action assignment).mp
    change 0 < (model.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union query.action (signature.actionParents query.action)) assignment)).num
    exact of_decide_eq_true ((List.all_eq_true.mp checked) assignment
      (signature.assignmentEnumeration_complete assignment))

theorem constant_action_admissible : forall assignment,
    HiddenDAGAdmissibleDomain.JointAdmissibleAt constantModel query assignment :=
  actionAdmissibleEverywhere constantModel (by decide +kernel)

theorem parity_action_admissible : forall assignment,
    HiddenDAGAdmissibleDomain.JointAdmissibleAt parityModel query assignment :=
  actionAdmissibleEverywhere parityModel (by decide +kernel)

/-- The exhibited reference already separates defined hard-interventional
values.  Retaining it explicitly avoids selecting a cell from a negated
universal statement and will also reject printed admissibility below. -/
private theorem values_separated : ¬ Nonempty (ProbabilityResult.Equivalent
    (constantModel.kernelDenote query.operationKernel reference)
    (parityModel.kernelDenote query.operationKernel reference)) := by
  rintro ⟨atReference⟩
  let forced := ProbabilityResult.trans (ProbabilityResult.symm constant_effect)
    (ProbabilityResult.trans atReference parity_effect)
  cases forced with
  | value rational => exact (by decide : ¬ QProb.Equiv QProb.zero ⟨1, 2, by decide⟩) rational

/-- The disagreement is between two defined hard-interventional values,
not a mismatch in support domains.  All external action tests pass. -/
theorem query_separated : ¬ constantModel.KernelResultEquivalent parityModel query.operationKernel :=
  fun equivalent => values_separated (equivalent reference)

noncomputable def counterexample : HiddenDAGAdmissibleJointCounterexample projection query where
  left := constantModel
  right := parityModel
  observationally_equal := observational_agreement
  left_admissible := constant_action_admissible
  right_admissible := parity_action_admissible
  query_separated := query_separated

/-- A successful front-door graph is not identifiable throughout the domain
containing only the external primitive query conditions.  Additional
used-conditional qualifications are mathematically essential at zeros. -/
theorem not_identifiable_primitive_domain : ¬ HiddenDAGAdmissibleDomain.jointIdentifiable projection query :=
  counterexample.not_identifiable

theorem actual_guarded_success : identifyGuardedJointKernel projection.observedGraph query = .identified guardedFormula :=
  guarded_identified

/-- The exact primitive demand predicate detects the missing internal
conditionals.  If it held, the verified native certificate would identify
the two genuinely different values.  This negative use of soundness does
not use causal soundness to assume or construct positive support. -/
theorem used_conditionals_not_admissible : ¬ constantModel.UsedConditionalsAdmissibleAt guardedFormula reference := by
  intro admissible
  let certificate := identifyGuardedJointKernel_admissibleCertificate query guarded_identified
  exact values_separated ⟨certificate.identifiableAt constantModel parityModel observational_agreement reference
    (constant_action_admissible reference) admissible⟩

/-- Undefinedness is a consequence of the exact proved admissibility/support
equivalence and the exhibited pair, not an expensive normalization of the
entire returned AST.  A `some` branch supplies its own representative
directly and contradicts the preceding rejection theorem. -/
theorem guarded_formula_is_undefined : (constantModel.termDenote guardedFormula reference).isNone = true := by
  cases result : constantModel.termDenote guardedFormula reference with
  | none => rfl
  | some value =>
      exact False.elim (used_conditionals_not_admissible
        ((constantModel.usedConditionalsAdmissibleAt_iff_supported guardedFormula reference).mpr
          ⟨value, by rw [result]; exact .value (QProb.equiv_refl value)⟩))

end AdmissibleFrontDoorBoundary
end Examples
end Causality
end Thesis
