import Thesis.Examples.Fixtures.FrontDoor
import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ProbabilityTermEquality
import Thesis.Causality.ObservationalEvaluation

namespace Thesis
namespace Causality
namespace Examples
namespace FrontDoorIdentification

open Probability

/-!
# Current ID values and action augmentation on the front-door fixture

These checks exercise the actual current engine, including literal equality
between its returned syntax and the compact finite spelling used for numerical
evaluation. They retain both the front-door query and the nonempty additional-
action branch. No legacy program or causal soundness theorem is imported to
justify the checked values: the source model and its observational table are
compared directly by finite kernel computations.
-/

/-! ## Positive correctness regression for the current-kernel replacement -/

/-- Extract the replacement engine's actual returned expression.  The
following branch equation checks that the fallback is not used. -/
def kernelEngineFormula : ProbabilityTerm signature :=
  match identifyJointKernel graph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

set_option maxRecDepth 100000 in
/-- The replacement handles the full front-door query, not a manually
supplied adjustment expression or a special-case model branch. -/
theorem kernelEngine_identified :
    identifyJointKernel graph query = .identified kernelEngineFormula := by rfl

/-!
The engine's node selections are functions computed by recursive graph
search. Their extensions on these three nodes are small, but carrying their
unevaluated search closures into every denotation reduction needlessly
repeats that search and can exhaust the native stack on macOS.

The following private spelling retains every constructor, including empty
marginalizations and the precise order of nested products and quotients.
It is not an independently supplied adjustment formula: the finite syntax
comparison below proves literal equality to the actual engine output before
the numerical regression uses it. Thus a changed engine output cannot pass
merely because this displayed expression still has the expected value.
-/

/-- The complete observed table, with its eight natural cell weights. This
does not replace the causal model: the event-agreement proof below checks
every cell against the actual two-root model before reusing the table. -/
private def observedTable : FiniteProbRecord signature.Assignment where
  atoms := [(assignmentOf false false false, 9), (assignmentOf false false true, 3),
    (assignmentOf false true false, 3), (assignmentOf false true true, 1),
    (assignmentOf true false false, 1), (assignmentOf true false true, 3),
    (assignmentOf true true false, 3), (assignmentOf true true true, 9)]
  den := 32
  den_pos := by decide
  total_mass := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Eight concrete singleton checks determine every observational event.
No causal or faithfulness premise is used to justify this finite table. -/
private theorem observedTable_agrees (event : Event signature.Assignment) :
    QProb.Equiv (model.observationalDist.probVal event) (observedTable.probVal event) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons _ _
    signature.assignmentEnumeration signature.assignmentEnumeration_nodup
    signature.assignmentEnumeration_complete ?_ event
  intro assignment
  rw [assignment_eq assignment]
  cases assignment x <;> cases assignment mediator <;> cases assignment y <;>
    decide +kernel

private def compactKernelEngineFormula : ProbabilityTerm signature :=
  let joint : ProbabilityTerm signature :=
    .kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩
  .marginalize (NodeSet.singleton mediator)
    (.multiply
      (.marginalize NodeSet.empty
        (.divide
          (.marginalize NodeSet.empty
            (.marginalize (NodeSet.singleton y) joint))
          (.marginalize (NodeSet.singleton mediator)
            (.marginalize (NodeSet.singleton y) joint))))
      (.marginalize NodeSet.empty
        (.marginalize (NodeSet.singleton x)
          (.multiply
            (.divide (.marginalize NodeSet.empty joint)
              (.marginalize (NodeSet.singleton y) joint))
            (.divide
              (.marginalize
                (NodeSet.union (NodeSet.singleton mediator) (NodeSet.singleton y)) joint)
              (.marginalize NodeSet.full joint))))))

set_option maxRecDepth 100000 in
/-- Materialize the finite node selections without changing the returned
syntax. The comparison is kernel checked, not a native-evaluation axiom. -/
private theorem kernelEngineFormula_eq_compact :
    kernelEngineFormula = compactKernelEngineFormula :=
  (ProbabilityTerm.equal_eq_true_iff _ _).mp (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Prefix quotients of the actual current kernel yield the correct `1/2`,
in contrast to the legacy output `9/16`. Kernel-checked table evaluation
checks the entire expression, including its nested sums and divisions.
Literal syntax equality and checked observational event equality connect
this computation to the original engine and model. Neither step appeals
to the causal soundness or completeness theorems under regression. -/
noncomputable def kernelEngineAtReferenceHalf :
    ProbabilityResult.Equivalent (kernelEngineFormula.denote model reference)
      (some ⟨1, 2, by decide⟩) := by
  rw [kernelEngineFormula_eq_compact]
  have actionFree : compactKernelEngineFormula.ActionFree := by
    simp [compactKernelEngineFormula, ProbabilityTerm.ActionFree, NodeSet.empty]
  rw [← ProbabilityTerm.observationalDenote_eq_scm model _ actionFree reference]
  exact ProbabilityResult.trans
    (ProbabilityTerm.observationalDenote_congr model.observationalDist
      observedTable observedTable_agrees compactKernelEngineFormula reference)
    (equivalentOfValueTest _ _ (by decide +kernel))

/-- The replacement formula and the requested interventional source agree
at the regression assignment.  This is a checked instance, not the general
semantic soundness or completeness theorem for all ID runs. -/
noncomputable def kernelEngine_equivalent_source :
    ProbabilityTerm.EquivalentAt model query.sourceTerm kernelEngineFormula
      reference :=
  ProbabilityResult.trans sourceAtReferenceHalf
    (ProbabilityResult.symm kernelEngineAtReferenceHalf)

/-! ## A regression that actually exercises action augmentation -/

/-- Intervene on the mediator rather than on `X`.  All three vertices are
ordinary ancestors of `Y`, but cutting incoming arrows at `M` removes `X`
from that ancestor set.  The additional-action branch must therefore run. -/
def mediatorQuery : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton mediator
  action_outcome_disjoint := by
    intro node selected
    have equal := (NodeSet.singleton_eq_true_iff mediator node).mp selected
    subst node
    rfl

set_option maxRecDepth 100000 in
/-- The incoming-cut test adds exactly `X`, rather than shrinking the
current distribution by observationally marginalizing it away. -/
theorem mediatorAdditionalAction_members :
    NodeSet.members (identificationAdditionalAction graph NodeSet.full
      mediatorQuery.outcome mediatorQuery.action) = [x] := by rfl

/-- The actual replacement output for the mediator intervention.  This
case uses augmentation followed by the ordinary recursive ID branches. -/
def kernelMediatorFormula : ProbabilityTerm signature :=
  match identifyJointKernel graph mediatorQuery with
  | .identified term => term
  | _ => unitProbabilityTerm signature

set_option maxRecDepth 100000 in
/-- The query is identified by the generic engine with its public bound. -/
theorem kernelMediator_identified :
    identifyJointKernel graph mediatorQuery = .identified kernelMediatorFormula := by rfl

set_option maxRecDepth 100000 in
/-- The mediator is an unused allowed parent of `Y` in this compatible
model, so intervening on it also leaves the outcome probability at `1/2`. -/
def mediatorSourceAtReferenceHalf :
    ProbabilityResult.Equivalent (mediatorQuery.sourceTerm.denote model reference)
      (some ⟨1, 2, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The complete generated expression after action augmentation agrees
with the source value; the test checks all subsequent restrictions and
current-input quotients as well, not just the Boolean `W` selection. -/
def kernelMediatorAtReferenceHalf :
    ProbabilityResult.Equivalent (kernelMediatorFormula.denote model reference)
      (some ⟨1, 2, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

/-- Checked source/output agreement for the nonempty-`W` regression. -/
def kernelMediator_equivalent_source :
    ProbabilityTerm.EquivalentAt model mediatorQuery.sourceTerm kernelMediatorFormula
      reference :=
  ProbabilityResult.trans mediatorSourceAtReferenceHalf
    (ProbabilityResult.symm kernelMediatorAtReferenceHalf)

end FrontDoorIdentification
end Examples
end Causality
end Thesis
