import Thesis.CausalTransport.LocalConditionalCompilation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {correct : DSeparationCorrectness G}

/-!
# Construct conditional local data from defined endpoints

Conditional identification has one boundary absent from unconditional ID:
the original intervened conditioner must have positive mass.  A defined
printed expression does not, by itself, establish that original source's
support.  `PrintedAvailable` therefore retains source support explicitly and
constructs all other primitive data from the actual printed expression.

For Bayes, the printed quotient exposes its positive denominator and its
numerator's defined value.  The denominator is the existing strict marginal
of that same numerator, so its support supplies every actually listed joint
input variant.  Joint availability constructs their recursive local data;
there is no second denominator identification call or global positivity.

For a conditioner promotion, intrinsic finite SCM composition supplies the
promoted source from the original supported source.  The printed expression
is unchanged.  Neither factual action overlap nor an assumed observational
transfer of causal support is used.

These are constructor preservation results.  The guarded IDC fuel proof in
`GuardedConditionalSuccessCompilation` composes them through its actual
search.  They do not declare the
compiler's `Data` to be the published admissible domain, or assert that action
admissibility alone already defines every returned expression.
-/

/-- Defined original and printed conditional endpoints construct this
compilation's actual data in a model with the stated projected graph.  The
source premise is the original conditioner's admissibility, not positivity
of the outcome or of the complete observational distribution. -/
def PublishedLocalConditionalCompilation.PrintedAvailable
    {query : ConditionalKernelQuery S}
    (input : PublishedLocalConditionalCompilation G correct query) : Type _ :=
  forall model : ExactModel S, HasProjectedGraph model G → forall reference : S.Assignment,
    query.sourceTerm.SupportedAt model reference →
    input.formula.SupportedAt model reference → input.Data model reference

namespace PublishedLocalConditionalCompilation.PrintedAvailable

/-- Literal target reindexing leaves source support and primitive data
unchanged.  Only the displayed-expression support crosses the equality. -/
noncomputable def reindex {query : ConditionalKernelQuery S}
    {input : PublishedLocalConditionalCompilation G correct query} (available : input.PrintedAvailable)
    (formula : ProbabilityTerm S) (formulaEq : formula = input.formula) :
    (input.reindex formula formulaEq).PrintedAvailable :=
  fun model projected reference sourceSupported printedSupported =>
    available model projected reference sourceSupported
      (ProbabilityTerm.SupportedAt.congr formulaEq printedSupported)

end PublishedLocalConditionalCompilation.PrintedAvailable

/-- Read exactly the Bayes compilation's primitive data from its defined
printed quotient.  Positive displayed denominator support gives the actual
enumerated numerator variants, including variants with zero outcome mass.
Availability is requested only of the existing joint input compilation. -/
noncomputable def localConditionalBayesCompilation_printedAvailable
    (query : ConditionalKernelQuery S)
    {numerator : PublishedLocalKernelCompilation G correct query.jointNumerator.outcome query.action}
    (available : numerator.PrintedAvailable) :
    (localConditionalBayesCompilation query numerator).PrintedAvailable := by
  intro model projected reference sourceSupported printedSupported
  have quotient : (ProbabilityTerm.divide numerator.reduction.formula
      (.marginalize (NodeSet.diff query.jointNumerator.outcome query.condition)
        numerator.reduction.formula)).SupportedAt model reference := printedSupported
  let numeratorSupported := ProbabilityTerm.divide_numerator_supportedAt quotient
  let denominator := ProbabilityTerm.divide_denominator_positiveAt quotient
  change LocalConditionalBayesData query numerator model reference
  exact {
    sourceSupported := sourceSupported
    numeratorData := available model projected reference numeratorSupported
    denominatorData := fun variant listed => available model projected variant
      (ProbabilityTerm.marginal_summand_supportedAt
        (NodeSet.diff query.jointNumerator.outcome query.condition)
        numerator.reduction.formula variant listed denominator.toSupported)
    denominatorPositive := denominator
  }

/-- One actual promotion preserves conditional availability.  Original
source support supplies the promoted conditioner through SCM composition;
the nested constructor then supplies all remaining data.  The converse
support implication is neither needed nor asserted. -/
noncomputable def localConditionalExchangeCompilation_printedAvailable
    (query : ConditionalKernelQuery S) (step : ConditionalExchangeStep G query)
    {nested : PublishedLocalConditionalCompilation G correct (query.exchangeCondition step.node step.selected)}
    (available : nested.PrintedAvailable) :
    (localConditionalExchangeCompilation query step nested).PrintedAvailable := by
  intro model projected reference sourceSupported printedSupported
  change LocalConditionalExchangeData step nested model reference
  exact {
    sourceSupported := sourceSupported
    nestedData := available model projected reference
      (query.exchangeCondition_supportedAt step.node step.selected model reference sourceSupported)
      printedSupported
  }

end Causality
end Thesis
