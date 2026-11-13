import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.CausalTransport.GuardedIdentificationKernel

namespace Thesis
namespace Causality

/-!
# Guarded IDC with the established finite exchange search

Only the terminal joint expression changes from corrected positive IDC:
the same rule-2 conditioner promotions end at guarded joint ID, and Bayes
uses the literal returned numerator and its marginal.  Null conditioners
remain undefined; no fallback value is assigned to their quotient.

The identified constructor is a candidate expression until the separate
local-support compiler supplies its derivation and demanded support data.
The results here establish action-free syntax, actual finite termination,
and identical decisions including the exact joint failure witness.  Thus
existing failure-to-countermodel transport needs no new nested unpackers.
-/

/-- The actual recursive conditional program, with no fixed bound on the
number of successful promotions and no second joint denominator call. -/
def identifyGuardedConditionalKernelFuel (fuel : Nat) (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) : IdentificationOutcome S :=
  match fuel with
  | 0 => .unfinished
  | fuel + 1 =>
      match conditionalExchangeStep? graph query with
      | some step => identifyGuardedConditionalKernelFuel fuel graph
          (query.exchangeCondition step.node step.selected)
      | none =>
          match identifyGuardedJointKernel graph query.jointNumerator with
          | .identified numerator => .identified (conditionalBayesTermFrom query numerator)
          | .failed fail => .failed fail
          | .unfinished => .unfinished

def identifyGuardedConditionalKernel (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) : IdentificationOutcome S :=
  identifyGuardedConditionalKernelFuel ((NodeSet.members query.condition).length + 1) graph query

/-- Every candidate is action-free, including after arbitrarily many
promotions.  This says nothing yet about a displayed denominator's support. -/
theorem identifyGuardedConditionalKernelFuel_identified_actionFree
    (fuel : Nat) (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernelFuel fuel graph query = .identified term) : term.ActionFree := by
  induction fuel generalizing query term with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      cases found : conditionalExchangeStep? graph query with
      | some step =>
          exact inductionHypothesis _ (by simpa only [identifyGuardedConditionalKernelFuel, found] using result)
      | none =>
          cases joint : identifyGuardedJointKernel graph query.jointNumerator with
          | identified numerator =>
              have same : conditionalBayesTermFrom query numerator = term := by
                simpa only [identifyGuardedConditionalKernelFuel, found, joint,
                  IdentificationOutcome.identified.injEq] using result
              rw [← same]
              let free := identifyGuardedJointKernel_identified_actionFree graph _ joint
              exact ⟨free, free⟩
          | failed _fail => simp only [identifyGuardedConditionalKernelFuel, found, joint] at result; cases result
          | unfinished => simp only [identifyGuardedConditionalKernelFuel, found, joint] at result; cases result

theorem identifyGuardedConditionalKernel_identified_actionFree
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel graph query = .identified term) : term.ActionFree :=
  identifyGuardedConditionalKernelFuel_identified_actionFree _ _ _ result

/-- Formula changes cannot change an exchange decision or a terminal joint
failure.  Comparing the actual computed outcomes requires no equality
instance for probability terms or functional node sets. -/
theorem identifyGuardedConditionalKernelFuel_decision_eq
    (fuel : Nat) (graph : ObservedGraph S) (query : ConditionalKernelQuery S) :
    (identifyGuardedConditionalKernelFuel fuel graph query).decision =
      (identifyConditionalKernelFuel fuel graph query).decision := by
  induction fuel generalizing query with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases found : conditionalExchangeStep? graph query with
      | some step =>
          simpa only [identifyGuardedConditionalKernelFuel, identifyConditionalKernelFuel, found] using
            inductionHypothesis (query.exchangeCondition step.node step.selected)
      | none =>
          have same := identifyGuardedJointKernel_decision_eq graph query.jointNumerator
          cases guarded : identifyGuardedJointKernel graph query.jointNumerator <;>
            cases strict : identifyJointKernel graph query.jointNumerator <;>
            simp only [guarded, strict, IdentificationOutcome.decision] at same <;>
            simp only [identifyGuardedConditionalKernelFuel, identifyConditionalKernelFuel, found,
              guarded, strict, IdentificationOutcome.decision] <;>
            first | exact same | cases same

theorem identifyGuardedConditionalKernel_decision_eq
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S) :
    (identifyGuardedConditionalKernel graph query).decision = (identifyConditionalKernel graph query).decision :=
  identifyGuardedConditionalKernelFuel_decision_eq _ _ _

/-- Strict conditioner decrease and the guarded joint fuel bound rule out
the sentinel.  This theorem depends only on the programs and graph geometry. -/
theorem identifyGuardedConditionalKernelFuel_ne_unfinished
    (fuel : Nat) (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (enough : (NodeSet.members query.condition).length < fuel) :
    identifyGuardedConditionalKernelFuel fuel graph query ≠ .unfinished := by
  induction fuel generalizing query with
  | zero => omega
  | succ fuel inductionHypothesis =>
      cases found : conditionalExchangeStep? graph query with
      | some step =>
          have smaller := query.exchangeCondition_size_lt step.node step.selected
          have enoughNext :
              (NodeSet.members (query.exchangeCondition step.node step.selected).condition).length < fuel := by omega
          simpa only [identifyGuardedConditionalKernelFuel, found] using inductionHypothesis _ enoughNext
      | none =>
          cases joint : identifyGuardedJointKernel graph query.jointNumerator with
          | identified _numerator =>
              simp only [identifyGuardedConditionalKernelFuel, found, joint]
              intro impossible
              cases impossible
          | failed _fail =>
              simp only [identifyGuardedConditionalKernelFuel, found, joint]
              intro impossible
              cases impossible
          | unfinished => exact False.elim (identifyGuardedJointKernel_ne_unfinished graph _ joint)

theorem identifyGuardedConditionalKernel_ne_unfinished
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S) :
    identifyGuardedConditionalKernel graph query ≠ .unfinished :=
  identifyGuardedConditionalKernelFuel_ne_unfinished _ _ _ (Nat.lt_succ_self _)

/-- Retain the exact failure witness, so the proved original-query
conditional countermodels can be reused without weakening their conclusion. -/
theorem identifyGuardedConditionalKernel_failed_iff
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S) (failure : IdentificationFail S) :
    identifyGuardedConditionalKernel graph query = .failed failure ↔
      identifyConditionalKernel graph query = .failed failure := by
  have same := identifyGuardedConditionalKernel_decision_eq graph query
  constructor
  · intro failed
    rw [failed] at same
    cases original : identifyConditionalKernel graph query with
    | identified _term => simp only [original, IdentificationOutcome.decision] at same; cases same
    | unfinished => simp only [original, IdentificationOutcome.decision] at same; cases same
    | failed other =>
        have equal : failure = other := by
          apply KernelIdentificationDecision.failed.inj
          simpa only [original, IdentificationOutcome.decision] using same
        exact congrArg IdentificationOutcome.failed equal.symm
  · intro failed
    rw [failed] at same
    cases guarded : identifyGuardedConditionalKernel graph query with
    | identified _term => simp only [guarded, IdentificationOutcome.decision] at same; cases same
    | unfinished => simp only [guarded, IdentificationOutcome.decision] at same; cases same
    | failed other =>
        have equal : other = failure := by
          apply KernelIdentificationDecision.failed.inj
          simpa only [guarded, IdentificationOutcome.decision] using same
        exact congrArg IdentificationOutcome.failed equal

end Causality
end Thesis
