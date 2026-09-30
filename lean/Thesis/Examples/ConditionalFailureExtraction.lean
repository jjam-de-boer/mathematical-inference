import Thesis.CausalTransport.ConditionalFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureExtraction

/-!
# Regression checks for conditional failure and countermodel transport

The first three vertices form the confounded chain `A → B → Y`, with one
bidirected component on them.  The last two vertices are isolated.  Joint ID
fails on `P(Y | do(A,B))`; adding either or both isolated vertices as
conditioners causes IDC to exchange them before reaching the same kind of
joint obstruction.  We check the actual engine failures and invoke the full
fuel-inductive provenance extractor, rather than a bounded failure unpacker.

The semantic checks use positive full-alphabet carrier countermodels for the
terminal's *original numerator*: its extracted common roots are among its
queried outcomes.  A checked finite trace transports the same two models to
the source conditional.  No model-class premise, observational-equivalence
premise, or completed-completeness interface is supplied by the fixture.
The explicit trace additionally documents both exchanges and the remaining
conditioner after the first; it is not a replacement for the general extractor.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## A confounded chain with two genuinely isolated conditioners -/

def signature : ObservedSignature where
  count := 5
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (child.val = parent.val + 1) && decide (child.val < 3)
  directed_earlier := by
    intro parent child edge
    have next := of_decide_eq_true (Bool.and_eq_true_iff.mp edge).1
    omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right) && decide (left.val < 3) && decide (right.val < 3)
  bidirected_symmetric := by
    intro left right edge
    simpa only [ne_comm, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm] using edge
  bidirected_irreflexive := by intro node; simp

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := by intro _; change false ∈ [false, true]; decide +kernel
  second_enumerated := by intro _; change true ∈ [false, true]; decide +kernel
  different := fun _ => Bool.false_ne_true

def outcome : NodeSet signature := NodeSet.singleton ⟨2, by decide⟩
def action : NodeSet signature := fun node => decide (node.val < 2)
def forestHost : NodeSet signature := fun node => decide (node.val < 3)
def firstConditioner : Fin signature.count := ⟨3, by decide⟩
def secondConditioner : Fin signature.count := ⟨4, by decide⟩

def emptyQuery : ConditionalKernelQuery signature where
  outcome := outcome
  action := action
  condition := NodeSet.empty
  action_outcome_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel
  action_condition_disjoint := NodeSet.disjoint_empty_right _
  outcome_condition_disjoint := NodeSet.disjoint_empty_right _

def oneExchangeQuery : ConditionalKernelQuery signature where
  outcome := outcome
  action := action
  condition := NodeSet.singleton firstConditioner
  action_outcome_disjoint := emptyQuery.action_outcome_disjoint
  action_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel
  outcome_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

def twoExchangeQuery : ConditionalKernelQuery signature where
  outcome := outcome
  action := action
  condition := fun node => decide (3 ≤ node.val)
  action_outcome_disjoint := emptyQuery.action_outcome_disjoint
  action_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel
  outcome_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

/-! ## Engine equations and the general provenance extractor -/

/-- Compare computed failure coordinates by their finite Boolean tests,
not by a classical decision procedure for equality of node-set functions. -/
private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed fail => NodeSet.equal fail.remaining forestHost && NodeSet.equal fail.free outcome
  | _ => false

private theorem failureOfTest (result : IdentificationOutcome signature)
    (checked : failureTest result = true) : result = .failed ⟨forestHost, outcome⟩ := by
  cases result with
  | identified _ => cases checked
  | unfinished => cases checked
  | failed fail =>
      have coordinates := Bool.and_eq_true_iff.mp checked
      have large := (NodeSet.equal_eq_true_iff _ _).mp coordinates.1
      have small := (NodeSet.equal_eq_true_iff _ _).mp coordinates.2
      cases fail with
      | mk remaining free =>
          cases large
          cases small
          rfl

theorem empty_failed : identifyConditionalKernel graph emptyQuery =
    .failed ⟨forestHost, outcome⟩ := failureOfTest _ (by decide +kernel)

theorem one_exchange_failed : identifyConditionalKernel graph oneExchangeQuery =
    .failed ⟨forestHost, outcome⟩ := failureOfTest _ (by decide +kernel)

theorem two_exchanges_failed : identifyConditionalKernel graph twoExchangeQuery =
    .failed ⟨forestHost, outcome⟩ := failureOfTest _ (by decide +kernel)

noncomputable def emptyExtraction := identifyConditionalKernelFailed emptyQuery empty_failed
noncomputable def oneExchangeExtraction := identifyConditionalKernelFailed oneExchangeQuery one_exchange_failed
noncomputable def twoExchangeExtraction := identifyConditionalKernelFailed twoExchangeQuery two_exchanges_failed

/-- The public extractor retains the exact terminal forest coordinates even
when promotions and joint ancestral pruning precede the failure. -/
theorem two_exchange_large : twoExchangeExtraction.hedge.witness.large = forestHost :=
  twoExchangeExtraction.hedge.large_eq

theorem two_exchange_small : twoExchangeExtraction.hedge.witness.small = outcome :=
  twoExchangeExtraction.hedge.small_eq

/-- Every remaining terminal conditioner is uniformly non-exchangeable.
This checks the extractor's exhausted-search interface without making an
equality decision on its proof-bearing terminal query. -/
theorem two_exchange_terminal_exhausted (node : Fin signature.count)
    (selected : twoExchangeExtraction.terminal.condition node = true) :
    conditionalExchangeTest graph twoExchangeExtraction.terminal node = false :=
  twoExchangeExtraction.exchangeTest_false node selected

/-! ## A two-exchange trace, including its nonempty intermediate given-set -/

def firstStep : ConditionalExchangeStep graph twoExchangeQuery where
  node := firstConditioner
  selected := by decide +kernel
  separated := by decide +kernel

def afterFirst := twoExchangeQuery.exchangeCondition firstStep.node firstStep.selected

def secondStep : ConditionalExchangeStep graph afterFirst where
  node := secondConditioner
  selected := by decide +kernel
  separated := by decide +kernel

def afterSecond := afterFirst.exchangeCondition secondStep.node secondStep.selected

/-- These are the first nodes selected by the actual finite search, not
arbitrarily chosen rules that happen to hold in the graph. -/
theorem first_search_node :
    (conditionalExchangeStep? graph twoExchangeQuery).map (fun step => step.node) =
      some firstConditioner := by decide +kernel

theorem second_search_node :
    (conditionalExchangeStep? graph afterFirst).map (fun step => step.node) =
      some secondConditioner := by decide +kernel

theorem intermediate_conditioner_retained : afterFirst.condition secondConditioner = true := by decide +kernel
theorem terminal_condition_empty : NodeSet.isEmpty afterSecond.condition = true := by decide +kernel

def exchangeTrace : ConditionalExchangeTrace graph twoExchangeQuery afterSecond :=
  .exchange firstStep (.exchange secondStep (.refl afterSecond))

theorem terminal_joint_failed : identifyJointKernel graph afterSecond.jointNumerator =
    .failed ⟨forestHost, outcome⟩ := failureOfTest _ (by decide +kernel)

noncomputable def terminalHedge := identifyJointKernelFailedHedge afterSecond.jointNumerator terminal_joint_failed

/-- The exact small-forest coordinate puts all common roots among the
terminal's outcomes.  No readout routing premise is hidden in the example. -/
theorem terminal_roots_in_outcome : NodeSet.Subset terminalHedge.witness.roots
    afterSecond.jointNumerator.outcome := by
  intro node root
  have inSmall := ((terminalHedge.witness.small_forest.roots_exact node).mp root).1
  have smallEqual : terminalHedge.witness.small = outcome := terminalHedge.small_eq
  have inOutcome : outcome node = true := by
    rw [← smallEqual]
    exact inSmall
  exact NodeSet.subset_union_left afterSecond.outcome afterSecond.condition node
    inOutcome

noncomputable def terminalJointCounterexample :=
  terminalHedge.witness.positiveCounterexampleOfRootsSubsetOutcome rich terminal_roots_in_outcome

/-- This conversion itself uses no positivity assumption; the pair's
positive membership is simply retained from the carrier construction. -/
noncomputable def terminalConditionalCounterexample :=
  ConditionalCounterexampleIn.ofJointNumeratorOfEmptyCondition
    afterSecond terminal_condition_empty terminalJointCounterexample

/-- A real positive countermodel for the original nonempty-condition query,
using the same pair after both checked rule-2 exchanges. -/
noncomputable def originalConditionalCounterexample :=
  exchangeTrace.transportCounterexample (C := GraphModelClass.positive graph)
    (fun member => member.2) terminalConditionalCounterexample

theorem original_query_not_identifiable :
    Not ((GraphModelClass.positive graph).conditionalIdentifiable twoExchangeQuery) :=
  originalConditionalCounterexample.not_identifiable

/-- Transport does not create replacement models or weaken their class. -/
theorem original_left_unchanged : originalConditionalCounterexample.left =
    terminalJointCounterexample.left := rfl

theorem original_right_unchanged : originalConditionalCounterexample.right =
    terminalJointCounterexample.right := rfl

/-! ## Universe-polymorphic provenance remains independent of the final assembler -/

universe u

noncomputable def failureAtHigherUniverse {S : ObservedSignature.{u}}
    {G : ObservedGraph S} (query : ConditionalKernelQuery S) {fail : IdentificationFail S}
    (result : identifyConditionalKernel G query = .failed fail) :
    ConditionalKernelFailure G query fail := identifyConditionalKernelFailed query result

end CurrentConditionalFailureExtraction
end Examples
end Causality
end Thesis
