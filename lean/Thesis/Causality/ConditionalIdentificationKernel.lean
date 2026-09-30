import Thesis.Causality.IdentificationKernel

namespace Thesis
namespace Causality

/-!
# Recursive conditional identification over the corrected joint engine

IDC first exchanges a removable observed conditioner for an intervention by
rule 2.  It repeats that search on the changed query: removing one conditioner
changes both the mutilated graph and the remaining conditioning set.  Only
when no exchange is available does it identify the joint numerator and divide
by its marginal denominator.

The older `identifyConditional` implements only a Bayes fallback and calls the
legacy joint engine.  This independent entry point uses `identifyJointKernel`
and retains every successful rule-2 test in an inspectable exchange step.
It never tests semantic identifiability or selects data from an existential
proposition.  The finite member enumeration determines which eligible node is
exchanged first.

The terminal denominator is a marginal of the *identified numerator*, not a
second potentially failing ID invocation.  `ConditionalCompilation` proves
termination and constructs a supported published derivation for every success.
Success correctness is distinct from conditional completeness: the latter
still needs a non-identifiability proof for an irreducible failed terminal
query, as well as the general positive hedge countermodel.
-/

/-! ## Exchanging one selected conditioner -/

/-- Promote one observed conditioner to an intervention.  Membership supplies
the disjointness facts needed by the new query; arbitrary already-intervened
or outcome vertices cannot be passed as an exchange candidate. -/
def ConditionalKernelQuery.exchangeCondition (query : ConditionalKernelQuery S)
    (node : Fin S.count) (selected : query.condition node = true) :
    ConditionalKernelQuery S where
  outcome := query.outcome
  action := NodeSet.union query.action (NodeSet.singleton node)
  condition := NodeSet.diff query.condition (NodeSet.singleton node)
  action_outcome_disjoint := NodeSet.disjoint_union_left_of
    query.action_outcome_disjoint (by
      intro other singleton
      have same : other = node := of_decide_eq_true singleton
      subst other
      cases outcome : query.outcome node with
      | false => rfl
      | true =>
          have excluded := query.outcome_condition_disjoint node outcome
          rw [selected] at excluded
          contradiction)
  action_condition_disjoint := NodeSet.disjoint_union_left_of
    (NodeSet.disjoint_of_subset_right query.action_condition_disjoint
      (NodeSet.diff_subset_left _ _)) (by
      intro other singleton
      simp only [NodeSet.diff, singleton, Bool.not_true, Bool.and_false])
  outcome_condition_disjoint := NodeSet.disjoint_of_subset_right
    query.outcome_condition_disjoint (NodeSet.diff_subset_left _ _)

/-- The singleton being exchanged and the remaining conditioner exactly
partition the original conditioner.  This is the rule-2 source-kernel bridge,
not a simplification that discards a nonempty given-set. -/
theorem ConditionalKernelQuery.exchangeCondition_partition
    (query : ConditionalKernelQuery S) (node : Fin S.count)
    (selected : query.condition node = true) :
    NodeSet.union (NodeSet.singleton node)
      (query.exchangeCondition node selected).condition = query.condition := by
  apply NodeSet.union_diff_eq
  intro other singleton
  have same : other = node := of_decide_eq_true singleton
  subst other
  exact selected

/-- Each promotion strictly decreases the finite conditioner size.  The
proof compares Boolean selections and uses the selected node to refute set
equality; it does not use classical empty-list characterizations. -/
theorem ConditionalKernelQuery.exchangeCondition_size_lt
    (query : ConditionalKernelQuery S) (node : Fin S.count)
    (selected : query.condition node = true) :
    (NodeSet.members (query.exchangeCondition node selected).condition).length <
      (NodeSet.members query.condition).length := by
  apply NodeSet.length_members_lt_of_subset_of_equal_false
    (NodeSet.diff_subset_left _ _)
  cases equal : NodeSet.equal
      (query.exchangeCondition node selected).condition query.condition with
  | false => exact equal
  | true =>
      have atNode := congrFun ((NodeSet.equal_eq_true_iff _ _).mp equal) node
      simp [ConditionalKernelQuery.exchangeCondition, NodeSet.diff,
        NodeSet.singleton, selected] at atNode

/-! ## Finite executable search with retained side-condition evidence -/

/-- Rule 2's actual IDC test for a single conditioner.  The other conditioners
remain in the given-set; only the candidate's outgoing edges are removed. -/
def conditionalExchangeTest (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node : Fin S.count) : Bool :=
  graph.dSeparated
    (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
    query.outcome (NodeSet.singleton node)
    (NodeSet.union query.action
      (NodeSet.diff query.condition (NodeSet.singleton node)))

/-- One finite-search result, with both query membership and the successful
graph test retained.  Proof fields justify the typed query update and the
later path-rule compilation; they introduce no additional semantic premise. -/
structure ConditionalExchangeStep (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) where
  node : Fin S.count
  selected : query.condition node = true
  separated : conditionalExchangeTest graph query node = true

/-- Find the first eligible conditioner in the signature's established
topological enumeration.  `find?` provides the node itself, so the accompanying
membership and test proofs need no proposition-to-data choice principle. -/
def conditionalExchangeStep? (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) : Option (ConditionalExchangeStep graph query) :=
  match found : (NodeSet.members query.condition).find?
      (conditionalExchangeTest graph query) with
  | none => none
  | some node => some {
      node := node
      selected := (NodeSet.mem_members_iff _ _).mp
        (List.mem_of_find?_eq_some found)
      separated := List.find?_some found
    }

/-- An exhausted search excludes every eligible singleton exchange, not just
the first member of the conditioner.  The finite-list search characterization
used here has only the permitted extensional axiom dependencies. -/
theorem conditionalExchangeStep?_none_excludes_all
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (exhausted : conditionalExchangeStep? graph query = none)
    (node : Fin S.count) (selected : query.condition node = true) :
    conditionalExchangeTest graph query node = false := by
  unfold conditionalExchangeStep? at exhausted
  split at exhausted
  · rename_i found
    have excluded := (List.find?_eq_none.mp found) node
      ((NodeSet.mem_members_iff _ _).mpr selected)
    cases tested : conditionalExchangeTest graph query node with
    | false => rfl
    | true => exact False.elim (excluded tested)
  · cases exhausted

/-! ## Recursive IDC and its exact Bayes output -/

/-- The Bayes fallback reuses the identified joint expression in numerator
and denominator.  The removed block is exactly the outcome block, but the
set-difference spelling agrees literally with the generic marginal compiler. -/
def conditionalBayesTermFrom (query : ConditionalKernelQuery S)
    (numerator : ProbabilityTerm S) : ProbabilityTerm S :=
  .divide numerator
    (.marginalize (NodeSet.diff query.jointNumerator.outcome query.condition) numerator)

/-- Fuel-bounded conditional identification.  Every recursive invocation
promotes one conditioner; the terminal invocation delegates to the corrected
joint engine.  A terminal `failed` records that joint failure, not yet a proof
that the original conditional query is non-identifiable. -/
def identifyConditionalKernelFuel (fuel : Nat) (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) : IdentificationOutcome S :=
  match fuel with
  | 0 => .unfinished
  | fuel + 1 =>
      match conditionalExchangeStep? graph query with
      | some step => identifyConditionalKernelFuel fuel graph
          (query.exchangeCondition step.node step.selected)
      | none =>
          match identifyJointKernel graph query.jointNumerator with
          | .identified numerator => .identified (conditionalBayesTermFrom query numerator)
          | .failed fail => .failed fail
          | .unfinished => .unfinished

/-- Public recursive IDC uses one fuel unit per possible promotion and one
for the terminal joint call.  No fixed-depth stack of exchanges is assumed. -/
def identifyConditionalKernel (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) : IdentificationOutcome S :=
  identifyConditionalKernelFuel ((NodeSet.members query.condition).length + 1)
    graph query

/-- Rule-2 promotions change only the query; every successful final expression
is action-free because its Bayes numerator comes from corrected joint ID. -/
theorem identifyConditionalKernelFuel_identified_actionFree
    (fuel : Nat) (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    {term : ProbabilityTerm S}
    (result : identifyConditionalKernelFuel fuel graph query = .identified term) :
    term.ActionFree := by
  induction fuel generalizing query term with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      cases step : conditionalExchangeStep? graph query with
      | some exchange =>
          exact inductionHypothesis _ (by
            simpa only [identifyConditionalKernelFuel, step] using result)
      | none =>
          cases joint : identifyJointKernel graph query.jointNumerator with
          | identified numerator =>
              have same : conditionalBayesTermFrom query numerator = term := by
                simpa only [identifyConditionalKernelFuel, step, joint,
                  IdentificationOutcome.identified.injEq] using result
              rw [← same]
              let free := identifyJointKernel_identified_actionFree graph _ joint
              exact ⟨free, free⟩
          | failed fail => simp only [identifyConditionalKernelFuel, step, joint] at result; cases result
          | unfinished => simp only [identifyConditionalKernelFuel, step, joint] at result; cases result

/-- The public entry point inherits the action-free successful-output
invariant.  Semantic validity is proved separately with a support tree. -/
theorem identifyConditionalKernel_identified_actionFree
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    {term : ProbabilityTerm S}
    (result : identifyConditionalKernel graph query = .identified term) :
    term.ActionFree :=
  identifyConditionalKernelFuel_identified_actionFree _ _ _ result

end Causality
end Thesis
