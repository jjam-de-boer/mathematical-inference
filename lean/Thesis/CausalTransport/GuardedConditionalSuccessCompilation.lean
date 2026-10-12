import Thesis.CausalTransport.GuardedConditionalIdentification
import Thesis.CausalTransport.LocalConditionalCompilation

namespace Thesis
namespace Causality

variable {S : ObservedSignature} {G : ObservedGraph S}

/-!
# Every successful guarded IDC run has a local-data compilation

Fuel induction follows the actual finite exchange search.  Each promotion
uses the shared graph-only rule-2 bridge, keeps the nonempty remaining given
set, and composes its original source support with the nested primitive data.
At termination one successful guarded joint call supplies the numerator;
its existing compilation is marginalized to build the Bayes denominator.

The successful term is aligned literally, not merely compared numerically.
Neither a separate denominator identification call nor a caller-supplied
full conditional support tree is required.  The initial joint invariants are
constructed by the public guarded joint compiler, including at zero cells.
The composed local boundary remains explicit: every demanded conditional
source must be supported, and each displayed Bayes denominator must be
positive.  Global observational positivity is not substituted for those
local conditions, and no unconditional zero-class completeness is claimed.
-/

/-- Keep the computed target alignment alongside the compilation.  This
prevents an unrelated valid conditional formula from being accepted as the
output of the actual program under consideration. -/
structure PublishedLocalConditionalSuccess (G : ObservedGraph S)
    (correct : DSeparationCorrectness G) (query : ConditionalKernelQuery S)
    (term : ProbabilityTerm S) where
  compilation : PublishedLocalConditionalCompilation G correct query
  formula_eq : compilation.formula = term

/-- Make the literal returned expression the displayed target while keeping
the syntactic equality node and exactly the same primitive local data. -/
noncomputable def PublishedLocalConditionalSuccess.aligned
    {correct : DSeparationCorrectness G} {query : ConditionalKernelQuery S} {term : ProbabilityTerm S}
    (success : PublishedLocalConditionalSuccess G correct query term) :
    PublishedLocalConditionalCompilation G correct query :=
  success.compilation.reindex term success.formula_eq.symm

theorem PublishedLocalConditionalSuccess.aligned_formula
    {correct : DSeparationCorrectness G} {query : ConditionalKernelQuery S} {term : ProbabilityTerm S}
    (success : PublishedLocalConditionalSuccess G correct query term) : success.aligned.formula = term := rfl

/-- Compile all successful fuel-bounded guarded IDC invocations, including
arbitrary promotion sequences and an empty conditioner.  The proof follows
computed search outcomes, without selecting data from an existence theorem. -/
noncomputable def identifyGuardedConditionalKernelFuelLocalCompilation
    (correct : DSeparationCorrectness G) (fuel : Nat) (query : ConditionalKernelQuery S)
    {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernelFuel fuel G query = .identified term) :
    PublishedLocalConditionalSuccess G correct query term := by
  induction fuel generalizing query term with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      cases found : conditionalExchangeStep? G query with
      | some step =>
          -- The nested target is unchanged by promotion.  Local data records
          -- the original endpoint and recursively constructs the promoted one.
          let nested := inductionHypothesis (query.exchangeCondition step.node step.selected)
            (by simpa only [identifyGuardedConditionalKernelFuel, found] using result)
          exact ⟨localConditionalExchangeCompilation query step nested.compilation, nested.formula_eq⟩
      | none =>
          cases joint : identifyGuardedJointKernel G query.jointNumerator with
          | identified numerator =>
              -- One actual joint expression appears in both Bayes positions.
              -- The marginal compiler builds the denominator from that input.
              have same : conditionalBayesTermFrom query numerator = term := by
                simpa only [identifyGuardedConditionalKernelFuel, found, joint,
                  IdentificationOutcome.identified.injEq] using result
              let compiled := (identifyGuardedJointKernelLocalCompilation correct query.jointNumerator joint).aligned
              exact ⟨localConditionalBayesCompilation query compiled, same⟩
          | failed _fail => simp only [identifyGuardedConditionalKernelFuel, found, joint] at result; cases result
          | unfinished => simp only [identifyGuardedConditionalKernelFuel, found, joint] at result; cases result

/-- The public conditional call constructs the complete sequence of local
support constructors itself.  Only its actual successful equation and the
proved graph criterion are inputs, not a trace compiler or model regularity. -/
noncomputable def identifyGuardedConditionalKernelLocalCompilation
    (correct : DSeparationCorrectness G) (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel G query = .identified term) :
    PublishedLocalConditionalSuccess G correct query term :=
  identifyGuardedConditionalKernelFuelLocalCompilation correct _ query result

end Causality
end Thesis
