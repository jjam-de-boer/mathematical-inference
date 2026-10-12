import Thesis.CausalTransport.SupportAwareComponentCompilation
import Thesis.CausalTransport.GuardedHostChainCompilation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}
variable {remaining externalAction : NodeSet S}

/-!
# Whole component extraction with prefix-first guarded products

The selected component is folded in observed topological order.  Its already
compiled prefix is the weight of the next *host-input* quotient; the factor
still reads the two marginals of the original current expression.  An absent
host position changes neither prefix nor formula.  This is different syntax
from the later-first strict product emitted by the positive ID engine.

The derivation uses the ordinary guarded chain identity and the proved
component-factor graph bridge.  There is no commutation, regrouping or
replacement by the original observational marginal.  External actions keep
all discarded host coordinates fixed.

The support construction below separates the causal prefix's positive
branches from the displayed formula prefix's positive branches.  Its local
conditions supply only observable overlap, actual input subtrees and the
displayed quotient denominator, not a semantic equivalence or a whole-product
support tree.  This avoids using soundness to manufacture positivity.
-/

/-- Previously fixed actions and the component's discarded host coordinates. -/
def componentExternalAction (remaining externalAction component : NodeSet S) : NodeSet S :=
  NodeSet.union externalAction (NodeSet.diff remaining component)

/-- Prefix-first selected-factor fold.  Every factor retains the full host
and actual current input, while the weight selects only component vertices. -/
def guardedComponentPrefixTerm (remaining : NodeSet S) (current : ProbabilityTerm S)
    (component : NodeSet S) : (n : Nat) → n ≤ S.count → ProbabilityTerm S :=
  GuardedHostChain.prefixTerm component (chainFactorFrom remaining current)

def guardedComponentTerm (remaining : NodeSet S) (current : ProbabilityTerm S)
    (component : NodeSet S) : ProbabilityTerm S :=
  guardedComponentPrefixTerm remaining current component S.count (Nat.le_refl _)

/-- Guarding changes support and product order, not the action-free status
of a current input's prefix quotients. -/
theorem guardedComponentPrefixTerm_actionFree (remaining : NodeSet S)
    (current : ProbabilityTerm S) (component : NodeSet S) (free : current.ActionFree)
    (n : Nat) (bound : n ≤ S.count) :
    (guardedComponentPrefixTerm remaining current component n bound).ActionFree :=
  GuardedHostChain.prefixTerm_actionFree component (chainFactorFrom remaining current)
    (fun node _selected => chainFactorFrom_actionFree remaining current node free) n bound

theorem guardedComponentTerm_actionFree (remaining : NodeSet S)
    (current : ProbabilityTerm S) (component : NodeSet S) (free : current.ActionFree) :
    (guardedComponentTerm remaining current component).ActionFree :=
  guardedComponentPrefixTerm_actionFree remaining current component free S.count (Nat.le_refl _)

/-- Data for one actually needed host-input quotient.  Overlap and the
displayed denominator are reference-local; input support is requested only
at the quotient's two finite marginal enumerations.  No component source
support or whole guarded-product support is assumed in these fields. -/
structure GuardedComponentFactorInputs
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G) (model : ExactModel S)
    (reference : S.Assignment) (node : Fin S.count) where
  overlap : ObservationalCylinderPositiveAt model
    (NodeSet.union externalAction (chainCondition remaining node)) reference
  numeratorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff remaining (NodeSet.union (NodeSet.singleton node) (chainCondition remaining node))) reference →
      LocalDerivationSupport model variant (input.derivation.compile correct)
  denominatorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff remaining (chainCondition remaining node)) reference →
      LocalDerivationSupport model variant (input.derivation.compile correct)
  denominatorPositive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize (NodeSet.diff remaining (chainCondition remaining node))
      input.formula).denote model reference)

/-- Build the ordinary host-factor tree from the displayed local data.
Observable overlap supplies its causal source conditioner directly by
consistency; neither the outcome nor the complete joint must be positive. -/
noncomputable def GuardedComponentFactorInputs.host_supportedAt
    {input : PublishedCurrentKernelReduction G remaining externalAction}
    {correct : DSeparationCorrectness G} {model : ExactModel S}
    {reference : S.Assignment} {node : Fin S.count}
    (data : GuardedComponentFactorInputs input correct model reference node)
    (outside : NodeSet.Disjoint externalAction remaining) (selected : remaining node = true) :
    LocalDerivationSupport model reference ((input.factorDerivation outside node selected).compile correct) :=
  input.factor_supportedAt correct outside node selected model reference
    (Kernel.supportedAt_of_observational_overlap model
      ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩ reference data.overlap)
    data.numeratorInputSupport data.denominatorInputSupport data.denominatorPositive

/-- Local factor inputs are demanded only on a positive prefix branch.
Both guards are explicit: the first is the intrinsic causal component prefix,
the second is its displayed compiled prefix.  Keeping the two tests separate
lets the support constructor avoid assuming their equality or calling a
soundness theorem to manufacture target positivity.  When both are zero,
the factor's undefined quotient and all its subtrees are genuinely skipped. -/
def GuardedComponentSupportConditions
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G) (component : NodeSet S)
    (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node, component node = true →
    Sum
      (ProbabilityResult.PositiveSupportedValue
        ((ProbabilityTerm.kernel ⟨chainPrefix component node.val,
          componentExternalAction remaining externalAction component, NodeSet.empty⟩).denote model reference))
      (ProbabilityResult.PositiveSupportedValue
        ((guardedComponentPrefixTerm remaining input.formula component node.val
          (Nat.le_of_lt node.isLt)).denote model reference)) →
    GuardedComponentFactorInputs input correct model reference node

namespace PublishedCurrentKernelReduction

/-- Assemble the inspectable guarded derivation at arbitrary prefix depth.
The graph closure invariants are independent of model regularity and are
reused for each actual selected vertex.  There is no recursion-depth case
list or global positivity premise. -/
noncomputable def guardedComponentPrefixDerivation
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true) :
    (n : Nat) → (bound : n ≤ S.count) →
      PathDoCalculusDerivation G
        (.kernel ⟨chainPrefix component n, componentExternalAction remaining externalAction component,
          NodeSet.empty⟩)
        (guardedComponentPrefixTerm remaining input.formula component n bound) :=
  GuardedHostChain.prefixDerivation component (componentExternalAction remaining externalAction component)
    (NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint componentSubset)
      (NodeSet.disjoint_diff_right remaining component))
    (chainFactorFrom remaining input.formula)
    (fun node selected => input.componentFactorDerivation component closed componentSubset bidirectedClosed node selected)

/-- The whole guarded component is an actual new current-kernel reduction.
Its source fixes the discarded coordinates and its displayed expression
retains every original host-input quotient.  Support is supplied separately
by the local constructor, not asserted by this syntactic record. -/
noncomputable def guardedComponent
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true) :
    PublishedCurrentKernelReduction G component (componentExternalAction remaining externalAction component) where
  formula := guardedComponentTerm remaining input.formula component
  actionFree := guardedComponentTerm_actionFree remaining input.formula component input.actionFree
  derivation := DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
    (by rw [chainPrefix_count]) rfl
    (input.guardedComponentPrefixDerivation component closed componentSubset bidirectedClosed
      S.count (Nat.le_refl _))

/-- Construct the full prefix support tree by the same bounded induction as
the derivation.  Conditional factor trees are built only when the source
prefix is positive; target-factor support is built only when the displayed
prefix is positive.  The primitive guarded-chain intermediate is supported
by its intrinsic finite-record identity, including at null prefix cells. -/
noncomputable def guardedComponentPrefix_supportedAt
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true)
    (model : ExactModel S) (reference : S.Assignment)
    (conditions : GuardedComponentSupportConditions input correct component model reference) :
    (n : Nat) → (bound : n ≤ S.count) →
      LocalDerivationSupport model reference
        ((input.guardedComponentPrefixDerivation component closed componentSubset bidirectedClosed n bound).compile
          correct) :=
  GuardedHostChain.prefix_supportedAt correct component
    (componentExternalAction remaining externalAction component)
    (NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint componentSubset)
      (NodeSet.disjoint_diff_right remaining component))
    (chainFactorFrom remaining input.formula)
    (fun node selected => input.componentFactorDerivation component closed componentSubset bidirectedClosed node selected)
    model reference
    (fun node selected sourcePositive => by
      let data := conditions node selected (.inl sourcePositive)
      let componentSupported := Kernel.supportedAt_of_positive_unconditional_conditioner model (NodeSet.singleton node)
        (componentExternalAction remaining externalAction component) (chainCondition component node) reference
        (by simpa only [chainCondition_eq_prefix] using sourcePositive)
      let middle := componentFactor_middle_supportedAt_of_overlap model component componentSubset node reference data.overlap
      exact input.componentFactor_supportedAt correct component closed componentSubset bidirectedClosed node selected
        model reference componentSupported middle (data.host_supportedAt closed.action_disjoint (componentSubset node selected)))
    (fun node selected targetPositive =>
      ((conditions node selected (.inr targetPositive)).host_supportedAt closed.action_disjoint
        (componentSubset node selected)).endpoints.2)

/-- The assembled whole-component reduction has a genuine ordinary support
tree under its explicit local branch conditions.  This is not a global
positivity certificate or an assumption that the resulting product is
supported: the constructor has built every required prefix and factor node. -/
noncomputable def guardedComponent_supportedAt
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true)
    (model : ExactModel S) (reference : S.Assignment)
    (conditions : GuardedComponentSupportConditions input correct component model reference) :
    LocalDerivationSupport model reference
      ((input.guardedComponent component closed componentSubset bidirectedClosed).derivation.compile correct) := by
  let prefixSupport := input.guardedComponentPrefix_supportedAt correct component closed componentSubset
    bidirectedClosed model reference conditions S.count (Nat.le_refl _)
  let sourceSupported := Kernel.unconditional_supportedAt model component
    (componentExternalAction remaining externalAction component) reference
  dsimp [guardedComponent, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨sourceSupported, ⟨prefixSupport.endpoints.2, prefixSupport⟩⟩

end PublishedCurrentKernelReduction
end Causality
end Thesis
