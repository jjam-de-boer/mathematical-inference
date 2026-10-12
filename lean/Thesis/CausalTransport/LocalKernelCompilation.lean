import Thesis.CausalTransport.GuardedComponentCompilation
import Thesis.CausalTransport.GuardedComponentFamilyCompilation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}
variable {correct : DSeparationCorrectness G} {remaining externalAction : NodeSet S}

/-!
# Compositional local data for recursive current-kernel compilation

The syntactic reduction and its local support constructor travel together.
`Data model reference` records the primitive conditions needed by this
particular compiled input; it is not an assumption that the whole derivation
is supported.  Each constructor below defines that data from its operands
and builds the ordinary support tree from it.

The observational initializer needs only `Unit`.  A marginal requests its
operand's data at precisely the finite enumerated variants.  Guarded
component extraction requests observable overlap, its actual displayed
denominator and recursively requested operand data only on positive prefix
branches.  Family assembly likewise requests each actual child compilation's
data, rather than requiring a host-joint tree as an input.

This is the input algebra for the uniform guarded-ID success compiler.  No
global observational positivity, denotational-equality leaf or soundness-
based inference of a positive denominator is introduced.  Graph parent
closure remains a separate recursion invariant: an arbitrary final marginal
need not itself be a parent-closed host in the original graph.
-/

/-- A source-aligned current expression and a constructor for its support
from the primitive data defined by the compilation that produced it. -/
structure PublishedLocalKernelCompilation (G : ObservedGraph S)
    (correct : DSeparationCorrectness G) (remaining externalAction : NodeSet S) where
  reduction : PublishedCurrentKernelReduction G remaining externalAction
  Data : ExactModel S → S.Assignment → Type
  supported : forall model reference, Data model reference →
    LocalDerivationSupport model reference (reduction.derivation.compile correct)

namespace PublishedLocalKernelCompilation

/-- The initial observed joint is supported even at zero cells.  There are
no regularity assumptions hidden in the initializer's unit data. -/
noncomputable def observational (G : ObservedGraph S) (correct : DSeparationCorrectness G) :
    PublishedLocalKernelCompilation G correct NodeSet.full NodeSet.empty where
  reduction := PublishedCurrentKernelReduction.observational G
  Data := fun _model _reference => Unit
  supported := fun model reference _data => PublishedCurrentKernelReduction.observational_supportedAt
    G correct model reference

/-- Keep an inspectable endpoint-equality wrapper while preserving the
operand's exact local data.  Only the new unconditional source value is
constructed here; the target value is transported by syntactic equality. -/
noncomputable def reindex (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    {newRemaining newAction : NodeSet S} (formula : ProbabilityTerm S)
    (sourceEq : ProbabilityTerm.kernel ⟨newRemaining, newAction, NodeSet.empty⟩ =
      .kernel ⟨remaining, externalAction, NodeSet.empty⟩)
    (formulaEq : formula = input.reduction.formula) :
    PublishedLocalKernelCompilation G correct newRemaining newAction where
  reduction := {
    formula := formula
    actionFree := by rw [formulaEq]; exact input.reduction.actionFree
    derivation := DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
      sourceEq formulaEq input.reduction.derivation
  }
  Data := input.Data
  supported := fun model reference data => by
    let inner := input.supported model reference data
    let source := Kernel.unconditional_supportedAt model newRemaining newAction reference
    let target := ProbabilityTerm.SupportedAt.congr formulaEq.symm inner.endpoints.2
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    exact ⟨source, ⟨target, inner⟩⟩

/-- A marginal consumes only the recursively defined operand data at its
finite summands.  Zero summands remain supported values, not positive ones. -/
noncomputable def marginal (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (kept : NodeSet S) (outside : NodeSet.Disjoint externalAction remaining)
    (subset : NodeSet.Subset kept remaining) : PublishedLocalKernelCompilation G correct kept externalAction where
  reduction := input.reduction.marginal kept outside subset
  Data := fun model reference => forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S (NodeSet.diff remaining kept) reference → input.Data model variant
  supported := fun model reference data => input.reduction.marginal_supportedAt correct kept outside subset
    model reference (fun variant listed => input.supported model variant (data variant listed))

theorem marginal_formula (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (kept : NodeSet S) (outside : NodeSet.Disjoint externalAction remaining) (subset : NodeSet.Subset kept remaining) :
    (input.marginal kept outside subset).reduction.formula =
      .marginalize (NodeSet.diff remaining kept) input.reduction.formula := rfl

end PublishedLocalKernelCompilation

/-- Primitive quotient data asks for the operand's own data, not its whole
support trees.  The constructor below recursively builds those trees. -/
structure LocalComponentFactorData
    (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (model : ExactModel S) (reference : S.Assignment) (node : Fin S.count) where
  overlap : ObservationalCylinderPositiveAt model
    (NodeSet.union externalAction (chainCondition remaining node)) reference
  numeratorData : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff remaining (NodeSet.union (NodeSet.singleton node) (chainCondition remaining node))) reference →
      input.Data model variant
  denominatorData : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff remaining (chainCondition remaining node)) reference → input.Data model variant
  denominatorPositive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize (NodeSet.diff remaining (chainCondition remaining node))
      input.reduction.formula).denote model reference)

/-- Convert primitive operand data into the exact two finite families of
support trees required by the established component-factor constructor. -/
noncomputable def LocalComponentFactorData.toInputs
    {input : PublishedLocalKernelCompilation G correct remaining externalAction}
    {model : ExactModel S} {reference : S.Assignment} {node : Fin S.count}
    (data : LocalComponentFactorData input model reference node) :
    GuardedComponentFactorInputs input.reduction correct model reference node where
  overlap := data.overlap
  numeratorInputSupport := fun variant listed => input.supported model variant (data.numeratorData variant listed)
  denominatorInputSupport := fun variant listed => input.supported model variant (data.denominatorData variant listed)
  denominatorPositive := data.denominatorPositive

/-- The new component's data is requested only on a positive causal or
displayed component prefix.  All inherited input conditions remain attached
to their actual marginal variants and are not reset to observational ones. -/
def LocalComponentData
    (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (component : NodeSet S) (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node, component node = true →
    Sum
      (ProbabilityResult.PositiveSupportedValue ((ProbabilityTerm.kernel
        ⟨chainPrefix component node.val, componentExternalAction remaining externalAction component, NodeSet.empty⟩).denote
          model reference))
      (ProbabilityResult.PositiveSupportedValue ((guardedComponentPrefixTerm remaining input.reduction.formula
        component node.val (Nat.le_of_lt node.isLt)).denote model reference)) →
    LocalComponentFactorData input model reference node

namespace PublishedLocalKernelCompilation

/-- Compile a whole component and define its genuinely recursive local
boundary.  Every requested input subtree is constructed by `input.supported`
from primitive data; no whole-component or whole-host tree is an assumption. -/
noncomputable def component
    (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (subset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true) :
    PublishedLocalKernelCompilation G correct component (componentExternalAction remaining externalAction component) where
  reduction := input.reduction.guardedComponent component closed subset bidirectedClosed
  Data := LocalComponentData input component
  supported := fun model reference data => input.reduction.guardedComponent_supportedAt correct component closed
    subset bidirectedClosed model reference (fun node selected branch => (data node selected branch).toInputs)

/-- The actual partition supplies subset and bidirected closure, without
asking the caller for an extra graph-separation condition or Boolean. -/
noncomputable def ofComponent
    (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (closed : G.KernelHostClosed remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining) :
    PublishedLocalKernelCompilation G correct component (componentExternalAction remaining externalAction component) :=
  input.component component closed (cComponents_subset G remaining listed) (G.cComponents_bidirected_closed remaining listed)

theorem component_formula (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (subset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true) :
    (input.component component closed subset bidirectedClosed).reduction.formula =
      guardedComponentTerm remaining input.reduction.formula component := rfl

end PublishedLocalKernelCompilation

/-! ## Independently compiled children supply data, not assumed host trees -/

structure PublishedLocalComponentFamily (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (remaining externalAction : NodeSet S) where
  formula : NodeSet S → ProbabilityTerm S
  compilation : forall component, component ∈ G.cComponents remaining →
    PublishedLocalKernelCompilation G correct component (componentExternalAction remaining externalAction component)
  formula_eq : forall component listed, (compilation component listed).reduction.formula = formula component

def PublishedLocalComponentFamily.toFamily
    (family : PublishedLocalComponentFamily G correct remaining externalAction) :
    PublishedComponentKernelReductionFamily G remaining externalAction where
  formula := family.formula
  reduction := fun component listed => (family.compilation component listed).reduction
  formula_eq := family.formula_eq

/-- One demanded child quotient's primitive boundary.  Its inherited data
are indexed by exactly that child's two finite marginal enumerations. -/
structure LocalFamilyFactorData
    (family : PublishedLocalComponentFamily G correct remaining externalAction)
    (model : ExactModel S) (reference : S.Assignment) (node : Fin S.count) (selected : remaining node = true) where
  componentSupported : (ProbabilityTerm.kernel ⟨NodeSet.singleton node,
    componentExternalAction remaining externalAction (G.componentAt remaining node),
    chainCondition (G.componentAt remaining node) node⟩).SupportedAt model reference
  overlap : ObservationalCylinderPositiveAt model (NodeSet.union externalAction (chainCondition remaining node)) reference
  numeratorData : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S (NodeSet.diff (G.componentAt remaining node)
      (NodeSet.union (NodeSet.singleton node) (chainCondition (G.componentAt remaining node) node))) reference →
      (family.compilation (G.componentAt remaining node) (G.componentAt_spec remaining node selected).1).Data model variant
  denominatorData : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S (NodeSet.diff (G.componentAt remaining node)
      (chainCondition (G.componentAt remaining node) node)) reference →
      (family.compilation (G.componentAt remaining node) (G.componentAt_spec remaining node selected).1).Data model variant
  denominatorPositive : ProbabilityResult.PositiveSupportedValue ((ProbabilityTerm.marginalize
    (NodeSet.diff (G.componentAt remaining node) (chainCondition (G.componentAt remaining node) node))
    (family.compilation (G.componentAt remaining node) (G.componentAt_spec remaining node selected).1).reduction.formula).denote
      model reference)

noncomputable def LocalFamilyFactorData.toInputs
    {family : PublishedLocalComponentFamily G correct remaining externalAction}
    {model : ExactModel S} {reference : S.Assignment} {node : Fin S.count} {selected : remaining node = true}
    (data : LocalFamilyFactorData family model reference node selected) :
    ComponentFamilyFactorInputs family.toFamily correct model reference node selected where
  componentSupported := data.componentSupported
  overlap := data.overlap
  numeratorInputSupport := fun variant listed =>
    (family.compilation _ _).supported model variant (data.numeratorData variant listed)
  denominatorInputSupport := fun variant listed =>
    (family.compilation _ _).supported model variant (data.denominatorData variant listed)
  denominatorPositive := data.denominatorPositive

def LocalFamilyData (family : PublishedLocalComponentFamily G correct remaining externalAction)
    (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node (selected : remaining node = true),
    Sum
      (ProbabilityResult.PositiveSupportedValue ((ProbabilityTerm.kernel
        ⟨chainPrefix remaining node.val, externalAction, NodeSet.empty⟩).denote model reference))
      (ProbabilityResult.PositiveSupportedValue ((GuardedHostChain.prefixTerm remaining family.toFamily.factor
        node.val (Nat.le_of_lt node.isLt)).denote model reference)) →
    LocalFamilyFactorData family model reference node selected

/-- Whole-host assembly recursively constructs every demanded child tree
before invoking the proved guarded family fold.  Zero branches request no
child data at all.  The resulting boundary is compositional and finite. -/
noncomputable def PublishedLocalComponentFamily.guardedReduction
    (family : PublishedLocalComponentFamily G correct remaining externalAction)
    (closed : G.KernelHostClosed remaining externalAction) :
    PublishedLocalKernelCompilation G correct remaining externalAction where
  reduction := family.toFamily.guardedReduction closed
  Data := LocalFamilyData family
  supported := fun model reference data => family.toFamily.guardedReduction_supportedAt correct closed model reference
    (fun node selected branch => (data node selected branch).toInputs)

end Causality
end Thesis
