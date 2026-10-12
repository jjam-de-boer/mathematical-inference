import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.CausalTransport.DSeparation

namespace Thesis
namespace Causality

/-!
# Shared graph-only compilation of a conditioner promotion

Positive and local-support IDC use the same executable exchange search and
the same rule-2 application.  This small module owns their common graph
bridge without importing soundness, joint success compilation or completeness.
The other conditioners remain in the given-set throughout; no empty-set
shortcut or extra graph-separation hypothesis is introduced.
-/

/-- All four rule blocks are disjoint when one selected conditioner is
promoted.  The remaining conditioner is not replaced by an empty set. -/
def ConditionalExchangeStep.disjoint
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (step : ConditionalExchangeStep graph query) :
    FourWayDisjoint query.action query.outcome (NodeSet.singleton step.node)
      (NodeSet.diff query.condition (NodeSet.singleton step.node)) where
  xy := query.action_outcome_disjoint
  xz := by
    intro node action
    cases singleton : NodeSet.singleton step.node node with
    | false => rfl
    | true =>
        have same : node = step.node := of_decide_eq_true singleton
        subst node
        have excluded := query.action_condition_disjoint step.node action
        rw [step.selected] at excluded
        contradiction
  xw := NodeSet.disjoint_of_subset_right query.action_condition_disjoint
    (NodeSet.diff_subset_left _ _)
  yz := by
    intro node outcome
    cases singleton : NodeSet.singleton step.node node with
    | false => rfl
    | true =>
        have same : node = step.node := of_decide_eq_true singleton
        subst node
        have excluded := query.outcome_condition_disjoint step.node outcome
        rw [step.selected] at excluded
        contradiction
  yw := NodeSet.disjoint_of_subset_right query.outcome_condition_disjoint
    (NodeSet.diff_subset_left _ _)
  zw := by
    intro node singleton
    simp only [NodeSet.diff, singleton, Bool.not_true, Bool.and_false]

/-- Compile the recorded executable graph test into the corresponding path
do-rule.  Rule 2 is oriented from the promoted kernel to the original kernel;
both success compilers explicitly use its symmetric direction. -/
def ConditionalExchangeStep.pathRule
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (step : ConditionalExchangeStep graph query)
    (correct : DSeparationCorrectness graph) :
    PathDoRuleApplication graph
      (query.exchangeCondition step.node step.selected).operationKernel
      query.operationKernel := by
  have application := DoRuleApplication.rule2
    (G := graph) (separation := pathRuleSeparation graph)
    query.action query.outcome (NodeSet.singleton step.node)
    (NodeSet.diff query.condition (NodeSet.singleton step.node)) step.disjoint
    (correct.pathDSeparated_of_dSeparated step.separated)
  have partition : NodeSet.union (NodeSet.singleton step.node)
      (NodeSet.diff query.condition (NodeSet.singleton step.node)) = query.condition :=
    query.exchangeCondition_partition step.node step.selected
  simpa only [rule2Left, rule2Right, partition,
    ConditionalKernelQuery.operationKernel,
    ConditionalKernelQuery.exchangeCondition] using application

end Causality
end Thesis
