import Thesis.CausalTransport.Soundness

namespace Thesis
namespace Causality

/-!
# Conditional agreement descends to every sub-outcome

The same conditioning set and complete action set are retained when only
some queried outcomes are read.  This is the conditional counterpart of the
joint marginal adapter in `Soundness`, with one important support distinction:
conditional `ValueEquivalent` promises agreement only on common support.
Strict observational positivity supplies that support at all the finitely
enumerated marginal cells of the two actual SCMs.

The proof uses the already proved finite marginalization semantics, not a
completeness interface.  Hidden pointwise equivalences are opened only inside
the finite sum proof, which itself returns `Nonempty`; no family of witnesses
is chosen.  A separated conditional marginal consequently refutes agreement
of the entire original outcome tuple in the same model pair.
-/

variable {S : ObservedSignature}

/-- Restrict only the outcome, retaining the original action and conditioner.
The three disjointness fields descend from the original query. -/
def ConditionalKernelQuery.restrictOutcome (query : ConditionalKernelQuery S)
    (outcome : NodeSet S) (subset : NodeSet.Subset outcome query.outcome) : ConditionalKernelQuery S where
  outcome := outcome
  action := query.action
  condition := query.condition
  action_outcome_disjoint := NodeSet.disjoint_of_subset_right query.action_outcome_disjoint subset
  action_condition_disjoint := query.action_condition_disjoint
  outcome_condition_disjoint := query.outcome_condition_disjoint.of_subset_left subset

/-- Agreement on a positive conditional kernel implies agreement on every
outcome marginal with the very same conditioner.  In particular, equality of
the conditioner marginals is neither supplied nor inferred. -/
theorem ConditionalKernelQuery.valueEquivalent_restrictOutcome
    (query : ConditionalKernelQuery S) (left right : ExactModel S)
    (leftPositive : ObservationallyPositive left) (rightPositive : ObservationallyPositive right)
    (equivalent : query.ValueEquivalent left right)
    (outcome : NodeSet S) (subset : NodeSet.Subset outcome query.outcome) :
    (query.restrictOutcome outcome subset).ValueEquivalent left right := by
  intro reference _ _
  let rest := NodeSet.diff query.outcome outcome
  let restricted := query.restrictOutcome outcome subset
  have unionEq : NodeSet.union outcome rest = query.outcome := NodeSet.union_diff_eq subset
  let disjoint : FourWayDisjoint query.action outcome rest query.condition :=
    { xy := NodeSet.disjoint_of_subset_right query.action_outcome_disjoint subset
      xz := NodeSet.disjoint_of_subset_right query.action_outcome_disjoint (NodeSet.diff_subset_left query.outcome outcome)
      xw := query.action_condition_disjoint
      yz := NodeSet.disjoint_diff query.outcome outcome
      yw := query.outcome_condition_disjoint.of_subset_left subset
      zw := query.outcome_condition_disjoint.of_subset_left (NodeSet.diff_subset_left query.outcome outcome) }
  have leftMarginal := ProbabilityTerm.marginalization_equivalentAt left query.action outcome rest query.condition
    reference disjoint (leftPositive.kernelPositiveSupportedValue restricted.operationKernel reference).toSupported
  have rightMarginal := ProbabilityTerm.marginalization_equivalentAt right query.action outcome rest query.condition
    reference disjoint (rightPositive.kernelPositiveSupportedValue restricted.operationKernel reference).toSupported
  have leftMarginal' : ProbabilityResult.Equivalent (restricted.sourceTerm.denote left reference)
      ((ProbabilityTerm.marginalize rest query.sourceTerm).denote left reference) := by
    simpa only [restricted, ConditionalKernelQuery.restrictOutcome, ConditionalKernelQuery.sourceTerm, unionEq] using leftMarginal
  have rightMarginal' : ProbabilityResult.Equivalent (restricted.sourceTerm.denote right reference)
      ((ProbabilityTerm.marginalize rest query.sourceTerm).denote right reference) := by
    simpa only [restricted, ConditionalKernelQuery.restrictOutcome, ConditionalKernelQuery.sourceTerm, unionEq] using rightMarginal
  have middle : Nonempty (ProbabilityResult.Equivalent
      ((ProbabilityTerm.marginalize rest query.sourceTerm).denote left reference)
      ((ProbabilityTerm.marginalize rest query.sourceTerm).denote right reference)) := by
    simpa only [ProbabilityTerm.denote] using ProbabilityResult.sum_map_congr_nonempty
      (ProbabilityTerm.marginalAssignments S rest reference)
      (fun variant => query.sourceTerm.denote left variant) (fun variant => query.sourceTerm.denote right variant)
      (fun variant => equivalent variant
        (leftPositive.kernelPositiveSupportedValue query.operationKernel variant).toSupported
        (rightPositive.kernelPositiveSupportedValue query.operationKernel variant).toSupported)
  rcases middle with ⟨between⟩
  exact ⟨ProbabilityResult.trans leftMarginal' (ProbabilityResult.trans between (ProbabilityResult.symm rightMarginal'))⟩

/-- Restore all original outcomes after constructing a separated conditional
marginal.  No model, class membership, observed law, action, or conditioner is
replaced at this assembly boundary. -/
noncomputable def ConditionalCounterexampleIn.ofRestrictedOutcome
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S) (outcome : NodeSet S) (subset : NodeSet.Subset outcome query.outcome)
    (marginal : ConditionalCounterexampleIn C (query.restrictOutcome outcome subset)) : ConditionalCounterexampleIn C query where
  left := marginal.left
  right := marginal.right
  left_mem := marginal.left_mem
  right_mem := marginal.right_mem
  observationally_equal := marginal.observationally_equal
  query_separated := fun equivalent => marginal.query_separated
    (query.valueEquivalent_restrictOutcome marginal.left marginal.right
      (obsPositive marginal.left_mem) (obsPositive marginal.right_mem) equivalent outcome subset)

end Causality
end Thesis
