import Thesis.CausalTransport.ConditionalCompilation
import Thesis.Examples.KernelSuccessCompilation
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalCompilation

open Probability
open CurrentKernelFailureExtraction
open FrontDoorIdentification

/-!
# Regression checks for recursive conditional identification

The first graph has `X → Z → Y` and `X ↔ Z`.  Its joint numerator
`P(Y,Z | do(X))` fails ID, but `P(Y | do(X),Z)` succeeds after exchanging `Z`
for an intervention.  This distinguishes genuine IDC from a Bayes-only
wrapper.  A longer chain retains a second conditioner while exchanging the
first, then exchanges that second node on the changed query.

The front-door example takes the terminal Bayes branch without a promotion:
its denominator is compiled from the successful joint numerator rather than
identified independently.  Empty conditioners, empty signatures, insufficient
fuel, and a real terminal failure exercise the remaining control-flow edges.
Every displayed certificate is produced by the general fuel induction.
-/

/-! ## A removable conditioner rescues a failed joint numerator -/

/-- Inspect only the result tag; no equality decision on probability terms
or their function-valued node selections is needed. -/
def failedResult (result : IdentificationOutcome S) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

def exchangeSignature := chainSignature 3
def exchangeGraph := partitionGraph exchangeSignature (fun node => decide (node.val = 2))
def exchangeX : Fin exchangeSignature.count := ⟨0, by decide⟩
def exchangeZ : Fin exchangeSignature.count := ⟨1, by decide⟩
def exchangeY : Fin exchangeSignature.count := ⟨2, by decide⟩

def exchangeQuery : ConditionalKernelQuery exchangeSignature where
  action := NodeSet.singleton exchangeX
  outcome := NodeSet.singleton exchangeY
  condition := NodeSet.singleton exchangeZ
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

set_option maxRecDepth 100000 in
theorem joint_numerator_fails :
    failedResult (identifyJointKernel exchangeGraph exchangeQuery.jointNumerator) = true := by decide +kernel

theorem conditioner_is_exchangeable :
    conditionalExchangeTest exchangeGraph exchangeQuery exchangeZ = true := by decide +kernel

def exchangeFormula : ProbabilityTerm exchangeSignature :=
  match identifyConditionalKernel exchangeGraph exchangeQuery with
  | .identified term => term
  | _ => .zero

set_option maxRecDepth 100000 in
theorem exchange_identified : identifyConditionalKernel exchangeGraph exchangeQuery =
    .identified exchangeFormula := rfl

noncomputable def exchangeCertificate :=
  identifyConditionalKernelPublishedCertificate (C := GraphModelClass.positive exchangeGraph)
    exchangeGraph.dSeparationCorrectness (fun member => member.2)
    exchangeQuery exchange_identified

theorem exchangeCertificate_formula : exchangeCertificate.formula = exchangeFormula := rfl

theorem exchange_identifiable :
    (GraphModelClass.positive exchangeGraph).conditionalIdentifiable exchangeQuery :=
  identifyConditionalKernel_identified_identifiable (C := GraphModelClass.positive exchangeGraph)
    exchangeGraph.dSeparationCorrectness
    (fun member => member.2) exchangeQuery exchange_identified

/-! ## Successive promotions keep the nonempty remaining given-set -/

def repeatedSignature := chainSignature 4
def repeatedGraph : ObservedGraph repeatedSignature where
  bidirected := fun left right => decide (left ≠ right) &&
    (decide (left.val < 2) && decide (right.val < 2))
  bidirected_symmetric := by
    intro left right edge
    simpa only [ne_comm, Bool.and_comm] using edge
  bidirected_irreflexive := by intro node; simp
def repeatedX : Fin repeatedSignature.count := ⟨0, by decide⟩
def firstZ : Fin repeatedSignature.count := ⟨1, by decide⟩
def secondZ : Fin repeatedSignature.count := ⟨2, by decide⟩
def repeatedY : Fin repeatedSignature.count := ⟨3, by decide⟩

def repeatedQuery : ConditionalKernelQuery repeatedSignature where
  action := NodeSet.singleton repeatedX
  outcome := NodeSet.singleton repeatedY
  condition := fun node => decide (node.val = 1 || node.val = 2)
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := by
    intro node selected
    have same : node = repeatedX := of_decide_eq_true selected
    subst node
    rfl
  outcome_condition_disjoint := by
    intro node selected
    have same : node = repeatedY := of_decide_eq_true selected
    subst node
    rfl

theorem first_selected : repeatedQuery.condition firstZ = true := rfl
def afterFirst := repeatedQuery.exchangeCondition firstZ first_selected

theorem remaining_conditioner : afterFirst.condition secondZ = true := rfl
theorem first_test : conditionalExchangeTest repeatedGraph repeatedQuery firstZ = true := by decide +kernel
theorem second_test : conditionalExchangeTest repeatedGraph afterFirst secondZ = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem first_search_node :
    (conditionalExchangeStep? repeatedGraph repeatedQuery).map (fun step => step.node) = some firstZ := rfl

set_option maxRecDepth 100000 in
theorem second_search_node :
    (conditionalExchangeStep? repeatedGraph afterFirst).map (fun step => step.node) = some secondZ := rfl

def repeatedFormula : ProbabilityTerm repeatedSignature :=
  match identifyConditionalKernel repeatedGraph repeatedQuery with
  | .identified term => term
  | _ => .zero

set_option maxRecDepth 100000 in
theorem repeated_identified : identifyConditionalKernel repeatedGraph repeatedQuery =
    .identified repeatedFormula := rfl

noncomputable def repeatedCertificate :=
  identifyConditionalKernelPublishedCertificate (C := GraphModelClass.positive repeatedGraph)
    repeatedGraph.dSeparationCorrectness (fun member => member.2)
    repeatedQuery repeated_identified

set_option maxRecDepth 100000 in
theorem repeatedCertificate_formula : repeatedCertificate.formula = repeatedFormula := rfl

/-! ## Terminal Bayes uses a recursively identified front-door numerator -/

def frontDoorConditionalQuery : ConditionalKernelQuery signature where
  action := NodeSet.singleton x
  outcome := NodeSet.singleton mediator
  condition := NodeSet.singleton y
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

/-- The incoming `M → Y` edge remains when `Y`'s outgoing edges are cut.
The conditioner cannot be exchanged, so this nonempty-action query genuinely
uses the Bayes fallback on `P(M,Y | do(X))`. -/
theorem frontDoor_no_exchange : conditionalExchangeStep? graph frontDoorConditionalQuery = none := by decide +kernel

def frontDoorConditionalFormula : ProbabilityTerm signature :=
  match identifyConditionalKernel graph frontDoorConditionalQuery with
  | .identified term => term
  | _ => .zero

set_option maxRecDepth 100000 in
theorem frontDoor_conditional_identified : identifyConditionalKernel graph frontDoorConditionalQuery =
    .identified frontDoorConditionalFormula := rfl

noncomputable def frontDoorConditionalCertificate :=
  identifyConditionalKernelPublishedCertificate (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    frontDoorConditionalQuery frontDoor_conditional_identified

theorem frontDoorConditionalCertificate_formula :
    frontDoorConditionalCertificate.formula = frontDoorConditionalFormula := rfl

/-- The generic compiler is correct throughout the positive compatible class,
not merely at the numerical regression model below. -/
noncomputable def frontDoor_conditional_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (assignment : signature.Assignment)
    (supported : frontDoorConditionalQuery.sourceTerm.SupportedAt model assignment) :
    ProbabilityTerm.EquivalentAt model frontDoorConditionalQuery.sourceTerm
      frontDoorConditionalFormula assignment :=
  identifyConditionalKernel_identified_soundAt (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness
    (fun member => member.2) frontDoorConditionalQuery frontDoor_conditional_identified
    model member assignment supported

/-- In the original positive front-door regression model, fixing `X = true`
leaves the mediator noise independent of `Y`; hence the requested conditional
has value three quarters.  The computed IDC formula agrees exactly. -/
def threeQuarters : QProb := ⟨3, 4, by decide⟩

/-- Inspect the partial finite value before checking its rational
cross-product.  As in the joint front-door regression, this avoids selecting
a supported value from a proposition or deciding an evidence-carrying type. -/
private def valueTest (result : ProbabilityResult.Result) (expected : QProb) : Bool :=
  match result with
  | none => false
  | some value => decide (QProb.Equiv value expected)

private def equivalentOfValueTest (result : ProbabilityResult.Result) (expected : QProb)
    (checked : valueTest result expected = true) :
    ProbabilityResult.Equivalent result (some expected) := by
  cases result with
  | none => cases checked
  | some value => exact .value (of_decide_eq_true checked)

set_option maxRecDepth 100000 in
def frontDoor_conditional_source_value : ProbabilityResult.Equivalent
    (frontDoorConditionalQuery.sourceTerm.denote model reference) (some threeQuarters) :=
  equivalentOfValueTest _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
def frontDoor_conditional_formula_value : ProbabilityResult.Equivalent
    (frontDoorConditionalFormula.denote model reference) (some threeQuarters) :=
  equivalentOfValueTest _ _ (by decide +kernel)

/-! ## Empty conditioner, empty signature, and honest failure sentinels -/

def emptyConditionQuery : ConditionalKernelQuery signature where
  action := query.action
  outcome := query.outcome
  condition := NodeSet.empty
  action_outcome_disjoint := query.action_outcome_disjoint
  action_condition_disjoint := NodeSet.disjoint_empty_right _
  outcome_condition_disjoint := NodeSet.disjoint_empty_right _

def emptyConditionFormula : ProbabilityTerm signature :=
  match identifyConditionalKernel graph emptyConditionQuery with
  | .identified term => term
  | _ => .zero

set_option maxRecDepth 100000 in
theorem empty_condition_identified : identifyConditionalKernel graph emptyConditionQuery =
    .identified emptyConditionFormula := rfl

noncomputable def emptyConditionCertificate :=
  identifyConditionalKernelPublishedCertificate (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    emptyConditionQuery empty_condition_identified

def zeroQuery : ConditionalKernelQuery CurrentKernelCompilation.zeroSignature where
  action := NodeSet.empty
  outcome := NodeSet.empty
  condition := NodeSet.empty
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := NodeSet.disjoint_empty_left _

theorem zero_ne_unfinished : identifyConditionalKernel CurrentKernelCompilation.zeroGraph zeroQuery ≠ .unfinished :=
  identifyConditionalKernel_ne_unfinished _ _

def zeroFormula : ProbabilityTerm CurrentKernelCompilation.zeroSignature :=
  match identifyConditionalKernel CurrentKernelCompilation.zeroGraph zeroQuery with
  | .identified term => term
  | _ => .zero

theorem zero_identified : identifyConditionalKernel CurrentKernelCompilation.zeroGraph zeroQuery =
    .identified zeroFormula := rfl

noncomputable def zeroCertificate :=
  identifyConditionalKernelPublishedCertificate
    (C := GraphModelClass.positive CurrentKernelCompilation.zeroGraph)
    CurrentKernelCompilation.zeroGraph.dSeparationCorrectness (fun member => member.2)
    zeroQuery zero_identified

theorem zeroCertificate_formula : zeroCertificate.formula = zeroFormula := rfl

set_option maxRecDepth 100000 in
theorem insufficient_fuel : identifyConditionalKernelFuel 1 repeatedGraph repeatedQuery = .unfinished := rfl

def failedConditionalQuery : ConditionalKernelQuery immediateSignature where
  action := immediateQuery.action
  outcome := immediateQuery.outcome
  condition := NodeSet.empty
  action_outcome_disjoint := immediateQuery.action_outcome_disjoint
  action_condition_disjoint := NodeSet.disjoint_empty_right _
  outcome_condition_disjoint := NodeSet.disjoint_empty_right _

set_option maxRecDepth 100000 in
theorem terminal_failure_retained :
    failedResult (identifyConditionalKernel immediateGraph failedConditionalQuery) = true := by decide +kernel

end CurrentConditionalCompilation
end Examples
end Causality
end Thesis
