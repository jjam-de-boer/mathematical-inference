import Thesis.CausalTransport.GuardedConditionalIdentification
import Thesis.CausalTransport.LocalConditionalCompilation
import Thesis.CausalTransport.LocalConditionalDataAvailability

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
    PublishedLocalConditionalSuccess G correct query term :=
  match fuel with
  | 0 => by cases result
  | fuel + 1 =>
      match found : conditionalExchangeStep? G query with
      | some step =>
          -- The nested target is unchanged by promotion.  Local data records
          -- the original endpoint and recursively constructs the promoted one.
          let nested := identifyGuardedConditionalKernelFuelLocalCompilation correct fuel
            (query.exchangeCondition step.node step.selected)
            (by simpa only [identifyGuardedConditionalKernelFuel, found] using result)
          ⟨localConditionalExchangeCompilation query step nested.compilation, nested.formula_eq⟩
      | none =>
          match joint : identifyGuardedJointKernel G query.jointNumerator with
          | .identified numerator =>
              -- One actual joint expression appears in both Bayes positions.
              -- The marginal compiler builds the denominator from that input.
              have same : conditionalBayesTermFrom query numerator = term := by
                simpa only [identifyGuardedConditionalKernelFuel, found, joint,
                  IdentificationOutcome.identified.injEq] using result
              let compiled := (identifyGuardedJointKernelLocalCompilation correct query.jointNumerator joint).aligned
              ⟨localConditionalBayesCompilation query compiled, same⟩
          | .failed _fail => by simp only [identifyGuardedConditionalKernelFuel, found, joint] at result; cases result
          | .unfinished => by simp only [identifyGuardedConditionalKernelFuel, found, joint] at result; cases result

/-- The public conditional call constructs the complete sequence of local
support constructors itself.  Only its actual successful equation and the
proved graph criterion are inputs, not a trace compiler or model regularity. -/
noncomputable def identifyGuardedConditionalKernelLocalCompilation
    (correct : DSeparationCorrectness G) (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel G query = .identified term) :
    PublishedLocalConditionalSuccess G correct query term :=
  identifyGuardedConditionalKernelFuelLocalCompilation correct _ query result

/-- Expose the terminal branch's exact primitive data through its proved
search and joint equations.  Clients need not normalize the whole graph
search or a target-equality transport merely to populate the Bayes record. -/
theorem identifyGuardedConditionalKernelFuelLocalCompilation_bayes_data
    (correct : DSeparationCorrectness G) (fuel : Nat) (query : ConditionalKernelQuery S)
    (noExchange : conditionalExchangeStep? G query = none) {numerator term : ProbabilityTerm S}
    (joint : identifyGuardedJointKernel G query.jointNumerator = .identified numerator)
    (result : identifyGuardedConditionalKernelFuel (fuel + 1) G query = .identified term) :
    (identifyGuardedConditionalKernelFuelLocalCompilation correct (fuel + 1) query result).compilation.Data =
      LocalConditionalBayesData query
        (identifyGuardedJointKernelLocalCompilation correct query.jointNumerator joint).aligned := by
  simp only [identifyGuardedConditionalKernelFuelLocalCompilation]
  split
  · rename_i step found
    rw [noExchange] at found
    cases found
  · split
    · rename_i actualNumerator actualJoint
      have same : actualNumerator = numerator :=
        IdentificationOutcome.identified.inj (actualJoint.symm.trans joint)
      cases same
      rfl
    · rename_i _failure failed
      rw [joint] at failed
      cases failed
    · rename_i unfinished
      rw [joint] at unfinished
      cases unfinished

section PrintedDataAvailability

variable {T : ObservedSignature.{0}} {Γ : ObservedGraph T}

/-- Compose conditional availability through every actual fuel-bounded IDC
run.  A promotion carries the unchanged printed target and intrinsically
propagates the original conditioner support.  Terminal Bayes reads its
primitive data from the one actual joint numerator and its displayed
denominator.  The result constructs the existing compiler's `Data`; neither
a whole recursive support tree nor global positivity is an input. -/
noncomputable def identifyGuardedConditionalKernelFuelLocalCompilation_printedAvailable
    (checked : DSeparationCorrectness Γ) (fuel : Nat) (query : ConditionalKernelQuery T)
    {term : ProbabilityTerm T}
    (result : identifyGuardedConditionalKernelFuel fuel Γ query = .identified term) :
    (identifyGuardedConditionalKernelFuelLocalCompilation checked fuel query result).compilation.PrintedAvailable := by
  induction fuel generalizing query term with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      cases found : conditionalExchangeStep? Γ query with
      | some step =>
          let nested := identifyGuardedConditionalKernelFuelLocalCompilation checked fuel
            (query.exchangeCondition step.node step.selected)
            (by simpa only [identifyGuardedConditionalKernelFuel, found] using result)
          have nestedAvailable : nested.compilation.PrintedAvailable := inductionHypothesis
            (query.exchangeCondition step.node step.selected)
            (by simpa only [identifyGuardedConditionalKernelFuel, found] using result)
          have constructed := localConditionalExchangeCompilation_printedAvailable query step nestedAvailable
          simpa only [identifyGuardedConditionalKernelFuelLocalCompilation, found] using constructed
      | none =>
          cases joint : identifyGuardedJointKernel Γ query.jointNumerator with
          | identified numerator =>
              let compiled := (identifyGuardedJointKernelLocalCompilation checked query.jointNumerator joint).aligned
              have jointAvailable : compiled.PrintedAvailable :=
                identifyGuardedJointKernelLocalCompilation_printedAvailable checked query.jointNumerator joint
              have constructed := localConditionalBayesCompilation_printedAvailable query jointAvailable
              simpa only [identifyGuardedConditionalKernelFuelLocalCompilation, found, joint] using constructed
          | failed _failure =>
              simp only [identifyGuardedConditionalKernelFuel, found, joint] at result
              cases result
          | unfinished =>
              simp only [identifyGuardedConditionalKernelFuel, found, joint] at result
              cases result

/-- Defined original and literal returned conditional endpoints supply all
primitive data for public guarded IDC.  The automatic fuel bound and literal
formula alignment are the existing public compiler's ones.  In particular,
the original conditioner is not inferred from printed-expression support,
and action admissibility is not silently equated with this availability
invariant. -/
noncomputable def identifyGuardedConditionalKernelLocalCompilation_printedAvailable
    (checked : DSeparationCorrectness Γ) (query : ConditionalKernelQuery T) {term : ProbabilityTerm T}
    (result : identifyGuardedConditionalKernel Γ query = .identified term) :
    (identifyGuardedConditionalKernelLocalCompilation checked query result).aligned.PrintedAvailable := by
  have available : (identifyGuardedConditionalKernelLocalCompilation checked query result).compilation.PrintedAvailable :=
    identifyGuardedConditionalKernelFuelLocalCompilation_printedAvailable checked _ query result
  exact available.reindex term (identifyGuardedConditionalKernelLocalCompilation checked query result).formula_eq.symm

end PrintedDataAvailability

end Causality
end Thesis
