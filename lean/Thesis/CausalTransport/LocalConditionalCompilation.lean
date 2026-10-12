import Thesis.CausalTransport.GuardedKernelSuccessCompilation
import Thesis.CausalTransport.ConditionalExchangeCompilation
import Thesis.Causality.ConditionalSupport

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S} {correct : DSeparationCorrectness G}

/-!
# Compositional local support for conditional exchange and Bayes

A conditional source can be undefined at a null conditioner.  Unlike an
unconditional current-kernel reduction, this compilation therefore records
its actual conditional source and constructs support from explicitly defined
local data.  The data never contains a complete support tree or a semantic
equation: the constructors below build every rule and congruence subtree.

For Bayes, one already compiled joint numerator supplies the denominator by
ordinary marginalization.  Its inherited data is requested at exactly those
finite summands, and only the displayed denominator must be positive.  The
numerator may be zero.  Intrinsic conditional/quotient normalization supplies
the conditioning intermediate, without calling soundness for positivity.

For rule 2, the promoted query's support is obtained from its own compiled
data.  Only the original source's local support is additionally requested.
Observable action-and-condition overlap is a sufficient constructor for that
source support, but is not asserted necessary.  No global observed positivity,
empty-conditioner shortcut or canonical-model assumption is introduced.
-/

/-- A conditional expression and a constructor for its ordinary recursive
support tree from this compilation's primitive local boundary. -/
structure PublishedLocalConditionalCompilation (G : ObservedGraph S)
    (correct : DSeparationCorrectness G) (query : ConditionalKernelQuery S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G query.sourceTerm formula
  Data : ExactModel S → S.Assignment → Type
  supported : forall model reference, Data model reference →
    LocalDerivationSupport model reference (derivation.compile correct)

/-- Retain a literal target-equality node without strengthening the local
boundary.  Source support comes from the existing compilation's data. -/
noncomputable def PublishedLocalConditionalCompilation.reindex
    {query : ConditionalKernelQuery S} (input : PublishedLocalConditionalCompilation G correct query)
    (formula : ProbabilityTerm S) (formulaEq : formula = input.formula) :
    PublishedLocalConditionalCompilation G correct query where
  formula := formula
  actionFree := by rw [formulaEq]; exact input.actionFree
  derivation := DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
    rfl formulaEq input.derivation
  Data := input.Data
  supported := fun model reference data => by
    let inner := input.supported model reference data
    let target := ProbabilityTerm.SupportedAt.congr formulaEq.symm inner.endpoints.2
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    exact ⟨inner.endpoints.1, ⟨target, inner⟩⟩

/-- Primitive Bayes data refers to the same numerator at the reference and
its actual denominator marginal variants.  No second ID invocation, complete
support subtree, positive numerator or everywhere-positive input is a field. -/
structure LocalConditionalBayesData (query : ConditionalKernelQuery S)
    (numerator : PublishedLocalKernelCompilation G correct query.jointNumerator.outcome query.action)
    (model : ExactModel S) (reference : S.Assignment) where
  sourceSupported : query.sourceTerm.SupportedAt model reference
  numeratorData : numerator.Data model reference
  denominatorData : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff query.jointNumerator.outcome query.condition) reference → numerator.Data model variant
  denominatorPositive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize (NodeSet.diff query.jointNumerator.outcome query.condition)
      numerator.reduction.formula).denote model reference)

/-- Compile the literal Bayes quotient from one compiled joint expression.
Both the denominator derivation and its support are built by marginalization
of that same expression.  Source support preserves the meaning of a missing
conditional; the actual displayed denominator positivity remains explicit. -/
noncomputable def localConditionalBayesCompilation
    (query : ConditionalKernelQuery S)
    (numerator : PublishedLocalKernelCompilation G correct query.jointNumerator.outcome query.action) :
    PublishedLocalConditionalCompilation G correct query := by
  let denominator := numerator.marginal query.condition query.jointNumerator.action_outcome_disjoint
    (NodeSet.subset_union_right _ _)
  let four := FourWayDisjoint.of_empty_w query.action query.outcome query.condition
    query.action_outcome_disjoint query.action_condition_disjoint query.outcome_condition_disjoint
  let split := DoCalculusDerivation.conditioning (G := G) (separation := pathRuleSeparation G)
    query.action query.outcome query.condition NodeSet.empty four
  exact {
    formula := conditionalBayesTermFrom query numerator.reduction.formula
    actionFree := ⟨numerator.reduction.actionFree, numerator.reduction.actionFree⟩
    derivation := DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
      (query.sourceTerm_eq_conditioningLeft_empty_w) rfl
      (DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G) split
        (DoCalculusDerivation.divideCongr (G := G) (separation := pathRuleSeparation G)
          numerator.reduction.derivation denominator.reduction.derivation))
    Data := LocalConditionalBayesData query numerator
    supported := fun model reference data => by
      let numeratorSupport := numerator.supported model reference data.numeratorData
      let denominatorSupport := denominator.supported model reference data.denominatorData
      let target := ProbabilityResult.divide_supported_of_positive_denominator
        numeratorSupport.endpoints.2 data.denominatorPositive
      let intermediate := ProbabilityTerm.SupportedAt.of_equivalent
        (Kernel.unconditionalQuotient_equivalentAt model query.operationKernel reference) data.sourceSupported
      have splitSource : (ProbabilityTerm.kernel
          ⟨query.outcome, query.action, NodeSet.union query.condition NodeSet.empty⟩).SupportedAt model reference :=
        ProbabilityTerm.SupportedAt.congr query.sourceTerm_eq_conditioningLeft_empty_w data.sourceSupported
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
      exact ⟨data.sourceSupported, ⟨target,
        ⟨splitSource, ⟨target,
          ⟨⟨splitSource, ⟨intermediate, ()⟩⟩,
            ⟨intermediate, ⟨target, ⟨numeratorSupport, denominatorSupport⟩⟩⟩⟩⟩⟩⟩⟩
  }

theorem localConditionalBayesCompilation_formula (query : ConditionalKernelQuery S)
    (numerator : PublishedLocalKernelCompilation G correct query.jointNumerator.outcome query.action) :
    (localConditionalBayesCompilation query numerator).formula =
      conditionalBayesTermFrom query numerator.reduction.formula := rfl

/-- One promotion's extra local boundary.  The promoted source is supported
by constructing the nested tree, not by adding a second source-tree premise. -/
structure LocalConditionalExchangeData {query : ConditionalKernelQuery S}
    (step : ConditionalExchangeStep G query)
    (nested : PublishedLocalConditionalCompilation G correct (query.exchangeCondition step.node step.selected))
    (model : ExactModel S) (reference : S.Assignment) where
  sourceSupported : query.sourceTerm.SupportedAt model reference
  nestedData : nested.Data model reference

/-- Observable overlap can supply the original conditional endpoint.  This
helper leaves the nested boundary explicit rather than claiming that all its
possibly causal-support fields transfer from observational agreement. -/
noncomputable def LocalConditionalExchangeData.ofOverlap
    {query : ConditionalKernelQuery S} {step : ConditionalExchangeStep G query}
    {nested : PublishedLocalConditionalCompilation G correct (query.exchangeCondition step.node step.selected)}
    {model : ExactModel S} {reference : S.Assignment}
    (overlap : ObservationalCylinderPositiveAt model (NodeSet.union query.action query.condition) reference)
    (nestedData : nested.Data model reference) : LocalConditionalExchangeData step nested model reference where
  sourceSupported := Kernel.supportedAt_of_observational_overlap model query.operationKernel reference overlap
  nestedData := nestedData

/-- Reverse the shared actual rule-2 application and then use the nested
conditional compilation.  Both forward endpoints and the reversed subtree
are retained, including when the conditioned outcome has value zero. -/
noncomputable def localConditionalExchangeCompilation
    (query : ConditionalKernelQuery S) (step : ConditionalExchangeStep G query)
    (nested : PublishedLocalConditionalCompilation G correct (query.exchangeCondition step.node step.selected)) :
    PublishedLocalConditionalCompilation G correct query where
  formula := nested.formula
  actionFree := nested.actionFree
  derivation := DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G)
    (DoCalculusDerivation.symm (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.doRule (G := G) (separation := pathRuleSeparation G) (step.pathRule correct)))
    nested.derivation
  Data := LocalConditionalExchangeData step nested
  supported := fun model reference data => by
    let inner := nested.supported model reference data.nestedData
    let middle := inner.endpoints.1
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    exact ⟨data.sourceSupported, ⟨inner.endpoints.2,
      ⟨⟨data.sourceSupported, ⟨middle, ⟨middle, ⟨data.sourceSupported, ()⟩⟩⟩⟩, inner⟩⟩⟩

end Causality
end Thesis
