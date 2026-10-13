import Thesis.CausalTransport.LocalKernelCompilation
import Thesis.CausalTransport.GuardedPrintedSupportCompletion

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}
variable {correct : DSeparationCorrectness G} {remaining externalAction : NodeSet S}

/-!
# Construct recursive kernel data from the actual printed expression

This is the constructor-level availability invariant needed by the uniform
guarded ID proof.  `PrintedAvailable` is constructive: support of a compiled
observational expression returns that compilation's actual primitive data,
not a propositional assertion that some unrelated data or derivation exists.

The observational initializer supplies unit data.  A defined strict marginal
supplies every listed input summand.  A defined guarded component or family
supplies only factors demanded by positive printed prefixes; quotient support
then exposes the exact positive denominator and finite inner input values.
The preceding input availability hypotheses construct those inner data.
Finally the completed-prefix bridge turns printed-only factor conditions into
the compiler's existing dual-guard data, without an assumed causal equality.

All formula alignments and marginal enumerations are the actual constructor
ones.  There is no global positivity or arbitrary value at a null quotient.
The availability invariant is not asserted for arbitrary user-defined
compilations: its hypotheses must be established for each preceding input.
The separate engine proof still has to propagate it through every actual
fuel branch and initial query wrapper, before final completeness is assembled.
-/

/-- Every defined printed value supplies this compilation's actual local
data in a structurally compatible model.  The result lives in `Type`, so its
data is constructed directly rather than chosen from a proposition. -/
def PublishedLocalKernelCompilation.PrintedAvailable
    (input : PublishedLocalKernelCompilation G correct remaining externalAction) : Type _ :=
  forall model : ExactModel S, HasProjectedGraph model G → forall reference : S.Assignment,
    input.reduction.formula.SupportedAt model reference → input.Data model reference

/-- Component factor data is initially requested only at printed positive
prefixes.  Its leaves contain the preceding input's data, not whole new trees. -/
def PrintedLocalComponentData
    (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (component : NodeSet S) (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node, component node = true →
    ProbabilityResult.PositiveSupportedValue ((guardedComponentPrefixTerm remaining input.reduction.formula component
      node.val (Nat.le_of_lt node.isLt)).denote model reference) → LocalComponentFactorData input model reference node

/-- Construct the old dual-guard component data from printed-only data.
For a causal request, build and interpret its strictly preceding prefix first.
The new factor's soundness is never assumed to establish its own guard. -/
noncomputable def LocalComponentData.ofPrinted
    {input : PublishedLocalKernelCompilation G correct remaining externalAction}
    {component : NodeSet S} (closed : G.KernelHostClosed remaining externalAction)
    (subset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (printed : PrintedLocalComponentData input component model reference) : LocalComponentData input component model reference := by
  intro node selected branch
  cases branch with
  | inr printedPositive => exact printed node selected printedPositive
  | inl sourcePositive =>
      let preceding := input.reduction.guardedComponentPrefix_supportedAt_of_printed_inputs correct component closed
        subset bidirectedClosed model projected reference
        (fun vertex included positive => (printed vertex included positive).toInputs) node.val (Nat.le_of_lt node.isLt)
      let equality :=
        ((input.reduction.guardedComponentPrefixDerivation component closed subset bidirectedClosed node.val
          (Nat.le_of_lt node.isLt)).compile correct).denotational_soundAt
          (model.projectedLocalPrimitiveSoundness projected correct) preceding
      exact printed node selected (ProbabilityResult.PositiveSupportedValue.transport equality sourcePositive)

/-- Read all component quotient inputs from a defined printed fold, using
only the preceding input's established availability.  Defined zero prefixes
do not request a factor, an input marginal or a denominator witness. -/
noncomputable def PrintedLocalComponentData.of_formula_supported
    {input : PublishedLocalKernelCompilation G correct remaining externalAction}
    (available : input.PrintedAvailable) (component : NodeSet S)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (supported : (guardedComponentTerm remaining input.reduction.formula component).SupportedAt model reference) :
    PrintedLocalComponentData input component model reference := by
  intro node selected positive
  let quotient := GuardedHostChain.factor_supportedAt_of_term_supported component
    (chainFactorFrom remaining input.reduction.formula) model reference node selected positive supported
  let numerator := ProbabilityTerm.divide_numerator_supportedAt quotient
  let denominator := ProbabilityTerm.divide_denominator_positiveAt quotient
  exact {
    projected := projected
    numeratorData := fun variant listed => available model projected variant
      (ProbabilityTerm.marginal_summand_supportedAt
        (NodeSet.diff remaining (NodeSet.union (NodeSet.singleton node) (chainCondition remaining node)))
        input.reduction.formula variant listed numerator)
    denominatorData := fun variant listed => available model projected variant
      (ProbabilityTerm.marginal_summand_supportedAt (NodeSet.diff remaining (chainCondition remaining node))
        input.reduction.formula variant listed denominator.toSupported)
    denominatorPositive := denominator
  }

/-- Printed family requests concern the actual independently compiled child
selected by the host lookup.  No causal host-prefix demand appears here. -/
def PrintedLocalFamilyData
    (family : PublishedLocalComponentFamily G correct remaining externalAction)
    (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node (selected : remaining node = true),
    ProbabilityResult.PositiveSupportedValue ((GuardedHostChain.prefixTerm remaining family.toFamily.factor node.val
      (Nat.le_of_lt node.isLt)).denote model reference) → LocalFamilyFactorData family model reference node selected

/-- The completed-prefix bridge also constructs the family's dual-guard data.
It preserves the exact lookup, component membership proof and factor syntax. -/
noncomputable def LocalFamilyData.ofPrinted
    {family : PublishedLocalComponentFamily G correct remaining externalAction}
    (closed : G.KernelHostClosed remaining externalAction)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (printed : PrintedLocalFamilyData family model reference) : LocalFamilyData family model reference := by
  intro node selected branch
  cases branch with
  | inr printedPositive => exact printed node selected printedPositive
  | inl sourcePositive =>
      let preceding := family.toFamily.guardedPrefix_supportedAt_of_printed_inputs correct closed model projected reference
        (fun vertex included positive => (printed vertex included positive).toInputs) node.val (Nat.le_of_lt node.isLt)
      let equality :=
        ((GuardedHostChain.prefixDerivation remaining externalAction closed.action_disjoint family.toFamily.factor
          (family.toFamily.factorDerivation closed) node.val (Nat.le_of_lt node.isLt)).compile correct).denotational_soundAt
            (model.projectedLocalPrimitiveSoundness projected correct) preceding
      exact printed node selected (ProbabilityResult.PositiveSupportedValue.transport equality sourcePositive)

/-- A defined printed host supplies its demanded child quotients.  Each
child's established availability supplies exactly the requested inner data;
the family formula equality is used before reading quotient operands. -/
noncomputable def PrintedLocalFamilyData.of_formula_supported
    {family : PublishedLocalComponentFamily G correct remaining externalAction}
    (available : forall component listed, (family.compilation component listed).PrintedAvailable)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (supported : (GuardedHostChain.term remaining family.toFamily.factor).SupportedAt model reference) :
    PrintedLocalFamilyData family model reference := by
  intro node selected positive
  let component := G.componentAt remaining node
  let computed := G.componentAt_spec remaining node selected
  let input := family.compilation component computed.1
  let displayed := GuardedHostChain.factor_supportedAt_of_term_supported remaining family.toFamily.factor
    model reference node selected positive supported
  let quotient : (chainFactorFrom component input.reduction.formula node).SupportedAt model reference :=
    ProbabilityTerm.SupportedAt.congr
      (congrArg (fun formula => chainFactorFrom component formula node) (family.formula_eq component computed.1)).symm displayed
  let numerator := ProbabilityTerm.divide_numerator_supportedAt quotient
  let denominator := ProbabilityTerm.divide_denominator_positiveAt quotient
  exact {
    projected := projected
    numeratorData := fun variant listed => available component computed.1 model projected variant
      (ProbabilityTerm.marginal_summand_supportedAt
        (NodeSet.diff component (NodeSet.union (NodeSet.singleton node) (chainCondition component node)))
        input.reduction.formula variant listed numerator)
    denominatorData := fun variant listed => available component computed.1 model projected variant
      (ProbabilityTerm.marginal_summand_supportedAt (NodeSet.diff component (chainCondition component node))
        input.reduction.formula variant listed denominator.toSupported)
    denominatorPositive := denominator
  }

namespace PublishedLocalKernelCompilation.PrintedAvailable

/-- Initial observational data is unit, including at zero observed atoms. -/
noncomputable def observational (G : ObservedGraph S) (correct : DSeparationCorrectness G) :
    (PublishedLocalKernelCompilation.observational G correct).PrintedAvailable :=
  fun _model _projected _reference _supported => ()

/-- Endpoint reindexing leaves the actual data unchanged; printed support
is transported by the literal target equality, not by a causal assumption. -/
noncomputable def reindex
    {input : PublishedLocalKernelCompilation G correct remaining externalAction} (available : input.PrintedAvailable)
    {newRemaining newAction : NodeSet S} (formula : ProbabilityTerm S)
    (sourceEq : ProbabilityTerm.kernel ⟨newRemaining, newAction, NodeSet.empty⟩ =
      .kernel ⟨remaining, externalAction, NodeSet.empty⟩)
    (formulaEq : formula = input.reduction.formula) :
    (input.reindex formula sourceEq formulaEq).PrintedAvailable :=
  fun model projected reference supported => available model projected reference
    (ProbabilityTerm.SupportedAt.congr formulaEq supported)

/-- Strict marginal evaluation supplies every listed preceding input value,
so preceding availability constructs all and only its required data. -/
noncomputable def marginal
    {input : PublishedLocalKernelCompilation G correct remaining externalAction} (available : input.PrintedAvailable)
    (kept : NodeSet S) (outside : NodeSet.Disjoint externalAction remaining) (subset : NodeSet.Subset kept remaining) :
    (input.marginal kept outside subset).PrintedAvailable :=
  fun model projected reference supported variant listed => available model projected variant
    (ProbabilityTerm.marginal_summand_supportedAt (NodeSet.diff remaining kept) input.reduction.formula variant listed supported)

/-- The complete component constructor preserves printed availability.
The causal/printed guard connection is proved by preceding-prefix induction,
not assumed as equality of complete guarded expressions. -/
noncomputable def component
    {input : PublishedLocalKernelCompilation G correct remaining externalAction} (available : input.PrintedAvailable)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (subset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true) :
    (input.component component closed subset bidirectedClosed).PrintedAvailable :=
  fun model projected reference supported => LocalComponentData.ofPrinted closed subset bidirectedClosed model projected reference
    (PrintedLocalComponentData.of_formula_supported available component model projected reference supported)

/-- Every computed actual component inherits the same availability theorem;
partition membership supplies its subset and bidirected-closure proofs. -/
noncomputable def ofComponent
    {input : PublishedLocalKernelCompilation G correct remaining externalAction} (available : input.PrintedAvailable)
    (closed : G.KernelHostClosed remaining externalAction) {component : NodeSet S}
    (listed : component ∈ G.cComponents remaining) : (input.ofComponent closed listed).PrintedAvailable :=
  available.component component closed (cComponents_subset G remaining listed) (G.cComponents_bidirected_closed remaining listed)

/-- Family assembly preserves availability without a host-joint oracle.
Only the actual listed children's availability hypotheses are used. -/
noncomputable def guardedReduction
    {family : PublishedLocalComponentFamily G correct remaining externalAction}
    (available : forall component listed, (family.compilation component listed).PrintedAvailable)
    (closed : G.KernelHostClosed remaining externalAction) : (family.guardedReduction closed).PrintedAvailable :=
  fun model projected reference supported => LocalFamilyData.ofPrinted closed model projected reference
    (PrintedLocalFamilyData.of_formula_supported available model projected reference supported)

end PublishedLocalKernelCompilation.PrintedAvailable

end Causality
end Thesis
