import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.CausalTransport.CompletenessAssembly

namespace Thesis
namespace Causality

/-!
# Supported compilation of every successful recursive IDC run

The conditional program has two kinds of steps, both handled uniformly here:
one finite rule-2 exchange, or the terminal Bayes quotient of a corrected joint
ID result.  Induction on its actual fuel covers arbitrary exchange sequences;
no catalogue of one-, two-, or five-step traces is needed.

The terminal denominator is compiled by marginalizing the numerator's existing
certificate.  Its syntax is exactly the expression emitted by IDC.  The
support-sensitive Bayes assembler then supplies the quotient's denominator
positivity at the source support.  At each preceding rule-2 exchange, SCM
consistency and observational positivity supply support of the changed
interventional conditional kernel directly.

This module is an integration boundary, like `CompletenessAssembly`: neither
the main soundness development nor the joint compiler imports it.  Completed
published soundness interprets the resulting derivations, but is not used as a
substitute for the conditional non-identifiability argument.  In particular,
the results below do not inhabit `PublishedCompleteness.conditional_complete`.
-/

/-! ## Termination from strict conditioner decrease -/

/-- Adequate conditional fuel cannot produce the unfinished sentinel.  Only
the conditioner decreases recursively; the joint terminal call has its own
already proved fuel bound. -/
theorem identifyConditionalKernelFuel_ne_unfinished
    (fuel : Nat) (graph : ObservedGraph S) (query : ConditionalKernelQuery S)
    (enough : (NodeSet.members query.condition).length < fuel) :
    identifyConditionalKernelFuel fuel graph query ≠ .unfinished := by
  induction fuel generalizing query with
  | zero => omega
  | succ fuel inductionHypothesis =>
      cases found : conditionalExchangeStep? graph query with
      | some step =>
          have smaller := query.exchangeCondition_size_lt step.node step.selected
          have enoughNext :
              (NodeSet.members (query.exchangeCondition step.node step.selected).condition).length < fuel := by
            omega
          simpa only [identifyConditionalKernelFuel, found] using
            inductionHypothesis _ enoughNext
      | none =>
          cases joint : identifyJointKernel graph query.jointNumerator with
          | identified numerator =>
              simp only [identifyConditionalKernelFuel, found, joint]
              intro impossible
              cases impossible
          | failed fail =>
              simp only [identifyConditionalKernelFuel, found, joint]
              intro impossible
              cases impossible
          | unfinished =>
              exact False.elim (identifyJointKernel_ne_unfinished graph _ joint)

/-- Public IDC reserves exactly one invocation beyond the maximum possible
number of promotions.  Empty conditioners and empty signatures are included. -/
theorem identifyConditionalKernel_ne_unfinished
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S) :
    identifyConditionalKernel graph query ≠ .unfinished :=
  identifyConditionalKernelFuel_ne_unfinished _ _ _ (Nat.lt_succ_self _)

/-! ## Retaining the full rule-2 given-set -/

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
the certificate constructor below explicitly uses its symmetric direction. -/
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

/-- Prepend a verified single-node exchange to an arbitrary nested conditional
certificate.  This works after any number of prior promotions, for any formula
returned by the nested run. -/
noncomputable def exchangeConditionPublishedCertificate
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S) (step : ConditionalExchangeStep graph query)
    (nested : PublishedConditionalCertificate C correct
      (query.exchangeCondition step.node step.selected)) :
    PublishedConditionalCertificate C correct query where
  toPublishedIdentificationCertificate :=
    PublishedIdentificationCertificate.prependSymmetricDoRuleOfPositive
      obsPositive (step.pathRule correct) nested.toGeneric

/-! ## Terminal Bayes compilation from one joint certificate -/

/-- Compile the exact Bayes denominator by marginalizing the existing joint
numerator certificate.  No second identification call or assumed syntactic
shape of the numerator formula is needed. -/
noncomputable def conditionalDenominatorPublishedCertificate
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S)
    (numerator : PublishedJointCertificate C correct query.jointNumerator) :
    PublishedJointCertificate C correct query.jointDenominator where
  toPublishedIdentificationCertificate :=
    currentKernelMarginalPublishedCertificate correct obsPositive
      query.jointNumerator.outcome query.action query.condition
      query.jointNumerator.action_outcome_disjoint
      (NodeSet.subset_union_right _ _) numerator.toGeneric

/-- A terminal identified joint result gives a supported conditional
certificate with exactly the quotient printed by the new IDC engine. -/
noncomputable def conditionalBayesPublishedCertificateFrom
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S)
    (numerator : PublishedJointCertificate C correct query.jointNumerator) :
    PublishedConditionalCertificate C correct query :=
  publishedConditionalCertificateOfJointCertificates graph.publishedSoundness
    correct query numerator
    (conditionalDenominatorPublishedCertificate correct obsPositive query numerator)

/-! ## Full recursive successful-run compilation -/

/-- A published conditional certificate aligned with an actual successful
engine term.  This mirrors `PublishedJointSuccessCompilation`: retaining the
formula equality inside the induction prevents an unrelated certificate from
being accepted as compilation of the computed output. -/
structure PublishedConditionalSuccessCompilation
    {S : ObservedSignature} {graph : ObservedGraph S}
    (C : GraphModelClass graph) (correct : DSeparationCorrectness graph)
    (query : ConditionalKernelQuery S) (term : ProbabilityTerm S) where
  certificate : PublishedConditionalCertificate C correct query
  formula_eq : certificate.formula = term

/-- Every successful fuel-bounded IDC run compiles to a supported published
certificate for its original conditional query.  Induction follows actual
search results and joint outputs, retaining all intermediate support trees. -/
noncomputable def identifyConditionalKernelFuelPublishedCompilation
    {S : ObservedSignature} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (fuel : Nat) (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernelFuel fuel graph query = .identified term) :
    PublishedConditionalSuccessCompilation C correct query term := by
  induction fuel generalizing query term with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      cases found : conditionalExchangeStep? graph query with
      | some step =>
          let nested := inductionHypothesis (query.exchangeCondition step.node step.selected)
            (by simpa only [identifyConditionalKernelFuel, found] using result)
          exact {
            certificate := exchangeConditionPublishedCertificate correct obsPositive
              query step nested.certificate
            formula_eq := nested.formula_eq
          }
      | none =>
          cases joint : identifyJointKernel graph query.jointNumerator with
          | identified numerator =>
              have same : conditionalBayesTermFrom query numerator = term := by
                simpa only [identifyConditionalKernelFuel, found, joint,
                  IdentificationOutcome.identified.injEq] using result
              exact {
                certificate := conditionalBayesPublishedCertificateFrom correct obsPositive query
                  (identifyJointKernelPublishedCertificate correct obsPositive _ joint)
                formula_eq := same
              }
          | failed fail => simp only [identifyConditionalKernelFuel, found, joint] at result; cases result
          | unfinished => simp only [identifyConditionalKernelFuel, found, joint] at result; cases result

/-- Expose the supported certificate with the successful engine output as its
definitionally displayed formula.  The structural compiler supplies the
alignment proof; reindexing does not replace it by semantic equivalence. -/
noncomputable def identifyConditionalKernelFuelPublishedCertificate
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (fuel : Nat) (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernelFuel fuel graph query = .identified term) :
    PublishedConditionalCertificate C correct query where
  toPublishedIdentificationCertificate :=
    let compiled := identifyConditionalKernelFuelPublishedCompilation correct obsPositive fuel query result
    compiled.certificate.toGeneric.reindex rfl compiled.formula_eq.symm

/-- Literal successful-output alignment of the fuel-bounded public wrapper. -/
theorem identifyConditionalKernelFuelPublishedCertificate_formula
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (fuel : Nat) (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernelFuel fuel graph query = .identified term) :
    (identifyConditionalKernelFuelPublishedCertificate correct obsPositive fuel query result).formula = term := rfl

/-- Public successful IDC output has an inspectable derivation and local
support in every member of the selected observationally positive class. -/
noncomputable def identifyConditionalKernelPublishedCertificate
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernel graph query = .identified term) :
    PublishedConditionalCertificate C correct query :=
  identifyConditionalKernelFuelPublishedCertificate correct obsPositive _ query result

/-- The public compiler retains exact syntax as well as a derivation. -/
theorem identifyConditionalKernelPublishedCertificate_formula
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernel graph query = .identified term) :
    (identifyConditionalKernelPublishedCertificate correct obsPositive query result).formula = term := rfl

/-- Every identified conditional expression denotes its requested source
kernel wherever the source is supported.  Published soundness interprets the
compiled derivation; it is not an assumption about the executable engine. -/
noncomputable def identifyConditionalKernel_identified_soundAt
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernel graph query = .identified term)
    (model : ExactModel S) (member : C.Mem model) (assignment : S.Assignment)
    (sourceSupported : query.sourceTerm.SupportedAt model assignment) :
    ProbabilityTerm.EquivalentAt model query.sourceTerm term assignment :=
  (identifyConditionalKernelPublishedCertificate correct obsPositive query result).compile.denotational_soundAt
    graph.publishedSoundness model member assignment sourceSupported

/-- An identified public conditional run is semantically identifiable in the
selected positive class.  This is the success direction, not the missing
converse for arbitrary semantically identifiable conditional queries. -/
theorem identifyConditionalKernel_identified_identifiable
    {S : ObservedSignature.{0}} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyConditionalKernel graph query = .identified term) :
    C.conditionalIdentifiable query :=
  ConditionalIdentificationCertificate.identifiable graph.publishedSoundness
    (identifyConditionalKernelPublishedCertificate correct obsPositive query result).compile

end Causality
end Thesis
