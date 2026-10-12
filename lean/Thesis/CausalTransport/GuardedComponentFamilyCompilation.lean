import Thesis.CausalTransport.GuardedHostChainCompilation
import Thesis.CausalTransport.SupportAwareComponentCompilation
import Thesis.CausalTransport.KernelPartition

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}
variable {remaining externalAction : NodeSet S}

/-!
# Whole-host assembly from independently compiled component inputs

Each actual c-component supplies its own current-kernel reduction under
actions on its host complement.  No reduction of the whole host is assumed:
the reverse graph bridge derives each needed host factor from that component
input, and the shared guarded host chain assembles the joint in topological
order.  Thus components may interleave, with no extra ordering premise.

The formula deliberately retains the component inputs' prefix quotients in
host order.  It is not the old strict product of their complete formulas.
Those two partial expressions can differ at zeros: a zero host prefix may
skip an undefined component input, while the strict product stays undefined.
There is consequently no unproved commutation, regrouping or cancellation
step disguised as formula alignment.

Local branch conditions supply only the current component's conditional
support, observable host-predecessor overlap, its two finite input-subtree
families and its displayed quotient denominator.  The complete host support
tree is constructed from them, including the genuinely skipped branches.
These are sufficient local conditions, not global observational positivity
or a zero-unrestricted engine-success equivalence.
-/

/-- Syntactic reductions for exactly the graph's actual component partition.
The total formula function supports the executable component lookup; values
outside the partition never need a reduction or semantic support witness. -/
structure PublishedComponentKernelReductionFamily (G : ObservedGraph S)
    (remaining externalAction : NodeSet S) where
  formula : NodeSet S → ProbabilityTerm S
  reduction : forall component, component ∈ G.cComponents remaining →
    PublishedCurrentKernelReduction G component
      (NodeSet.union externalAction (NodeSet.diff remaining component))
  formula_eq : forall component listed, (reduction component listed).formula = formula component

namespace PublishedComponentKernelReductionFamily

/-- Read the computed component's exact recursive-input quotient. -/
def factor (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (node : Fin S.count) : ProbabilityTerm S :=
  chainFactorFrom (G.componentAt remaining node) (family.formula (G.componentAt remaining node)) node

/-- Component uniqueness aligns every listed block with the computed lookup.
This is functional Boolean-set equality proved by the partition machinery,
not a classical equality decision for arbitrary functions. -/
theorem factor_eq_of_mem (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining)
    (node : Fin S.count) (inside : component node = true) :
    family.factor node = chainFactorFrom component (family.formula component) node := by
  unfold factor
  rw [G.componentAt_eq_of_mem remaining listed node inside]

theorem factor_actionFree (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (node : Fin S.count) (selected : remaining node = true) : (family.factor node).ActionFree := by
  let component := G.componentAt remaining node
  have computed := G.componentAt_spec remaining node selected
  have free := (family.reduction component computed.1).actionFree
  rw [family.formula_eq component computed.1] at free
  exact chainFactorFrom_actionFree component (family.formula component) node free

/-- The reverse bridge reduces a host conditional using only its computed
component input.  Source geometry and both graph rules come from actual
partition membership; the exact recursive target is reindexed visibly. -/
noncomputable def factorDerivation (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (closed : G.KernelHostClosed remaining externalAction)
    (node : Fin S.count) (selected : remaining node = true) :
    PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩) (family.factor node) := by
  let component := G.componentAt remaining node
  have computed := G.componentAt_spec remaining node selected
  let input := family.reduction component computed.1
  let inner := input.hostFactorOfComponentDerivation closed (cComponents_subset G remaining computed.1)
    (G.cComponents_bidirected_closed remaining computed.1) node computed.2
  have targetEq : family.factor node = chainFactorFrom component input.formula node :=
    congrArg (fun current => chainFactorFrom component current node) (family.formula_eq component computed.1).symm
  exact DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G) rfl targetEq inner

end PublishedComponentKernelReductionFamily

/-- Primitive local data for one needed component quotient.  The selected
proof is used only to access its actual listed reduction.  Support of an
entire host or of an unrelated component is not a field of this record. -/
structure ComponentFamilyFactorInputs
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (model : ExactModel S) (reference : S.Assignment)
    (node : Fin S.count) (selected : remaining node = true) where
  componentSupported : (ProbabilityTerm.kernel
    ⟨NodeSet.singleton node,
      NodeSet.union externalAction (NodeSet.diff remaining (G.componentAt remaining node)),
      chainCondition (G.componentAt remaining node) node⟩).SupportedAt model reference
  overlap : ObservationalCylinderPositiveAt model
    (NodeSet.union externalAction (chainCondition remaining node)) reference
  numeratorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff (G.componentAt remaining node)
        (NodeSet.union (NodeSet.singleton node) (chainCondition (G.componentAt remaining node) node))) reference →
      LocalDerivationSupport model variant
        ((family.reduction (G.componentAt remaining node)
          (G.componentAt_spec remaining node selected).1).derivation.compile correct)
  denominatorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff (G.componentAt remaining node) (chainCondition (G.componentAt remaining node) node)) reference →
      LocalDerivationSupport model variant
        ((family.reduction (G.componentAt remaining node)
          (G.componentAt_spec remaining node selected).1).derivation.compile correct)
  denominatorPositive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize
      (NodeSet.diff (G.componentAt remaining node) (chainCondition (G.componentAt remaining node) node))
      (family.reduction (G.componentAt remaining node)
        (G.componentAt_spec remaining node selected).1).formula).denote model reference)

namespace PublishedComponentKernelReductionFamily

/-- Build every reverse-rule and component-input subtree from the local
record, then preserve the formula-alignment wrapper's actual endpoints. -/
noncomputable def factor_supportedAt
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (closed : G.KernelHostClosed remaining externalAction)
    (node : Fin S.count) (selected : remaining node = true) (model : ExactModel S) (reference : S.Assignment)
    (data : ComponentFamilyFactorInputs family correct model reference node selected) :
    LocalDerivationSupport model reference ((family.factorDerivation closed node selected).compile correct) := by
  let component := G.componentAt remaining node
  have computed := G.componentAt_spec remaining node selected
  let input := family.reduction component computed.1
  let innerSupport := input.hostFactorOfComponent_supportedAt correct closed
    (cComponents_subset G remaining computed.1) (G.cComponents_bidirected_closed remaining computed.1)
    node computed.2 model reference data.componentSupported data.overlap
    data.numeratorInputSupport data.denominatorInputSupport data.denominatorPositive
  let targetSupported := ProbabilityTerm.SupportedAt.congr
    (congrArg (fun current => chainFactorFrom component current node) (family.formula_eq component computed.1))
    innerSupport.endpoints.2
  dsimp [factorDerivation, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨innerSupport.endpoints.1, ⟨targetSupported, innerSupport⟩⟩

/-- Assemble the whole host without assuming its reduction as an input.
The formula is a guarded topological fold of actual component quotients,
not a strict list product whose undefined factors could spoil a zero cell. -/
noncomputable def guardedReduction (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (closed : G.KernelHostClosed remaining externalAction) :
    PublishedCurrentKernelReduction G remaining externalAction :=
  GuardedHostChain.reduction remaining externalAction closed.action_disjoint family.factor
    family.factor_actionFree (family.factorDerivation closed)

theorem guardedReduction_formula (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (closed : G.KernelHostClosed remaining externalAction) :
    (family.guardedReduction closed).formula = GuardedHostChain.term remaining family.factor := rfl

end PublishedComponentKernelReductionFamily

/-- Needed quotient data are guarded by both actual host-prefix tests.
The source test drives recursive factor substitution; the displayed test
constructs the target weighted product.  Keeping them explicit avoids using
soundness to assume equality or manufacture prefix positivity. -/
def ComponentFamilySupportConditions
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node (selected : remaining node = true),
    Sum
      (ProbabilityResult.PositiveSupportedValue
        ((ProbabilityTerm.kernel ⟨chainPrefix remaining node.val, externalAction, NodeSet.empty⟩).denote model reference))
      (ProbabilityResult.PositiveSupportedValue
        ((GuardedHostChain.prefixTerm remaining family.factor node.val (Nat.le_of_lt node.isLt)).denote model reference)) →
    ComponentFamilyFactorInputs family correct model reference node selected

namespace PublishedComponentKernelReductionFamily

/-- Construct the complete whole-host tree from just its guarded quotient
inputs.  Null branches require neither the omitted factor's tree nor any
input marginal variant of that component.  Every demanded factor is built
by the reverse bridge, not supplied as a new assumed semantic law. -/
noncomputable def guardedReduction_supportedAt
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (closed : G.KernelHostClosed remaining externalAction)
    (model : ExactModel S) (reference : S.Assignment)
    (conditions : ComponentFamilySupportConditions family correct model reference) :
    LocalDerivationSupport model reference ((family.guardedReduction closed).derivation.compile correct) :=
  GuardedHostChain.reduction_supportedAt correct remaining externalAction closed.action_disjoint family.factor
    family.factor_actionFree (family.factorDerivation closed) model reference
    (fun node selected sourcePositive => family.factor_supportedAt correct closed node selected model reference
      (conditions node selected (.inl sourcePositive)))
    (fun node selected targetPositive =>
      (family.factor_supportedAt correct closed node selected model reference
        (conditions node selected (.inr targetPositive))).endpoints.2)

end PublishedComponentKernelReductionFamily
end Causality
end Thesis
