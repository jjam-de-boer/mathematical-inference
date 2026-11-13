import Thesis.CausalTransport.KernelRecursionCompilation
import Thesis.CausalTransport.KernelPartition
import Thesis.CausalTransport.ProductCompilation

namespace Thesis
namespace Causality

open Probability

/-!
# Supported compilation of the recursive c-component product

Each component is identified recursively under interventions on its host
complement.  The product branch must combine those reductions into the joint
free kernel before marginalizing its unwanted outcomes.  Assuming an input
certificate for that free joint would be circular: it is the result being
constructed here.

Instead, every host conditional factor is reduced to the corresponding
factor of its own identified component.  The shared topological chain fold
assembles those factors into the free joint.  The exact partition permutation
then groups them by component, and a supported comparison replaces each
component's chain expansion by its recursive expression.

All graph side conditions come from parent closure and actual partition
membership.  All support and positivity invariants come from observational
positivity and finite probability algebra.  Neither soundness nor an assumed
completeness theorem is imported, and components may interleave arbitrarily.
-/

/-! ## The independently compiled component family -/

/-- Formula-aligned recursive reductions of every actual host component.

The formula function is total so indexed products have an ordinary list
map.  Its values outside the partition are irrelevant: certificates and
positive-support data are required only for listed components.  No decision
procedure for equality of functional node sets is needed. -/
structure PublishedComponentKernelFamily
    {G : ObservedGraph S} (C : GraphModelClass G) (correct : DSeparationCorrectness G)
    (remaining externalAction : NodeSet S) where
  formula : NodeSet S -> ProbabilityTerm S
  certificate : forall component, component ∈ G.cComponents remaining ->
    PublishedIdentificationCertificate C correct
      (.kernel ⟨component, NodeSet.union externalAction (NodeSet.diff remaining component), NodeSet.empty⟩)
  formula_eq : forall component listed, (certificate component listed).formula = formula component
  positive : forall component, component ∈ G.cComponents remaining ->
    forall (model : ExactModel S), C.Mem model -> forall reference,
      ProbabilityResult.PositiveSupportedValue ((formula component).denote model reference)

/-- Listed component formulas inherit action-freeness from their certificates. -/
theorem PublishedComponentKernelFamily.formula_actionFree
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining) :
    (family.formula component).ActionFree := by
  rw [← family.formula_eq component listed]
  exact (family.certificate component listed).actionFree

/-- A global vertex factor reads its computed component's recursive formula.
For unselected vertices the search fallback is harmless; the chain fold and
the partition enumerate only selected vertices. -/
def PublishedComponentKernelFamily.factor
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    (node : Fin S.count) : ProbabilityTerm S :=
  chainFactorFrom (G.componentAt remaining node)
    (family.formula (G.componentAt remaining node)) node

/-- Uniqueness of the computed component aligns the global factor function
with every listed component's own current-input quotient. -/
theorem PublishedComponentKernelFamily.factor_eq_of_mem
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining)
    (node : Fin S.count) (inside : component node = true) :
    family.factor node = chainFactorFrom component (family.formula component) node := by
  unfold factor
  rw [G.componentAt_eq_of_mem remaining listed node inside]

/-- Only selected global factors are needed, and each is action-free. -/
theorem PublishedComponentKernelFamily.factor_actionFree
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    (node : Fin S.count) (selected : remaining node = true) :
    (family.factor node).ActionFree :=
  chainFactorFrom_actionFree _ _ node
    (family.formula_actionFree (G.componentAt_spec remaining node selected).1)

/-! ## From each identified component back to the host conditional factors -/

/-- Compile a host factor using its computed component reduction.

The factor compiler first extracts a quotient of the component's recursive
expression.  The reverse graph bridge then adds outside-component actions
and exchanges observations as required by the full host conditioner.  No
certificate for the host joint is passed to this construction. -/
noncomputable def PublishedComponentKernelFamily.factorCertificate
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (closed : G.KernelHostClosed remaining externalAction)
    (node : Fin S.count) (selected : remaining node = true) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩) := by
  let component := G.componentAt remaining node
  have computed := G.componentAt_spec remaining node selected
  have subset := cComponents_subset G remaining computed.1
  have outside : NodeSet.Disjoint
      (NodeSet.union externalAction (NodeSet.diff remaining component)) component :=
    NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint subset)
      (NodeSet.disjoint_diff_right remaining component)
  let input := (family.certificate component computed.1).reindex rfl
    (family.formula_eq component computed.1).symm
  let factor := currentKernelFactorPublishedCertificate correct obsPositive component
    (NodeSet.union externalAction (NodeSet.diff remaining component)) outside
    node computed.2 input (family.positive component computed.1)
  exact (currentKernelHostFactorOfComponentPublishedCertificate obsPositive
    remaining externalAction component closed subset
    (fun sourceInside targetRemaining edge =>
      G.cComponents_bidirected_closed remaining computed.1 sourceInside targetRemaining edge)
    node computed.2 factor).reindex rfl rfl

/-- The graph bridge preserves the exact quotient of the recursive formula. -/
theorem PublishedComponentKernelFamily.factorCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (closed : G.KernelHostClosed remaining externalAction)
    (node : Fin S.count) (selected : remaining node = true) :
    (family.factorCertificate obsPositive closed node selected).formula = family.factor node := rfl

/-! ## Replace grouped component chains by their recursive expressions -/

/-- Listed components contain a selected root, so their reverse vertex
enumerations are nonempty.  This supplies the product regrouping fold's
block condition, not an additional premise on a graph or query. -/
private theorem listed_component_members_nonempty
    (G : ObservedGraph S) (remaining : NodeSet S) {component : NodeSet S}
    (listed : component ∈ G.cComponents remaining) : (NodeSet.members component).reverse ≠ [] := by
  rcases cComponents_mem G remaining listed with ⟨root, selected, rfl⟩
  have member := List.mem_reverse.mpr ((NodeSet.mem_members_iff _ root).mpr
    (cComponentOf_root_mem G remaining selected))
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

/-- A grouped global factor block is literally the listed component's
current-input chain product; uniqueness aligns each factor separately. -/
theorem PublishedComponentKernelFamily.componentProduct_eq
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining) :
    topologicalProductTerm component family.factor =
      chainProductFrom component (family.formula component) component := by
  unfold topologicalProductTerm chainProductFrom
  apply congrArg productTerms
  apply List.map_congr_left
  intro node member
  exact family.factor_eq_of_mem listed node
    ((NodeSet.mem_members_iff component node).mp (List.mem_reverse.mp member))

/-- Replace one component's expanded chain by its recursive expression.

Both expressions reduce the same component kernel.  The support-sensitive
comparison reverses the chain certificate and follows the original recursive
certificate, retaining the common positive source kernel as an intermediate.
It neither cancels quotients syntactically nor appeals to semantic soundness. -/
noncomputable def PublishedComponentKernelFamily.componentProductCertificate
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (closed : G.KernelHostClosed remaining externalAction)
    (component : NodeSet S) (listed : component ∈ G.cComponents remaining) :
    PublishedIdentificationCertificate C correct (topologicalProductTerm component family.factor) := by
  let input := (family.certificate component listed).reindex rfl (family.formula_eq component listed).symm
  let action := NodeSet.union externalAction (NodeSet.diff remaining component)
  have outside : NodeSet.Disjoint action component := NodeSet.disjoint_union_left_of
    (NodeSet.disjoint_of_subset_right closed.action_disjoint (cComponents_subset G remaining listed))
    (NodeSet.disjoint_diff_right remaining component)
  let expanded := PublishedCurrentKernelChainCompilation.ofPositive correct obsPositive
    component action outside input (family.positive component listed)
  let compared := PublishedIdentificationCertificate.compareWithSupport expanded.certificate input
    (fun _model member reference => (obsPositive member).kernelPositiveSupportedValue
      ⟨component, action, NodeSet.empty⟩ reference |>.toSupported)
  exact compared.reindex
    (show topologicalProductTerm component family.factor = expanded.certificate.formula by
      rw [expanded.formula_eq]
      exact family.componentProduct_eq listed)
    (show family.formula component = compared.formula from rfl)

/-- The component comparison's target is the exact recursive expression. -/
theorem PublishedComponentKernelFamily.componentProductCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (closed : G.KernelHostClosed remaining externalAction)
    (component : NodeSet S) (listed : component ∈ G.cComponents remaining) :
    (family.componentProductCertificate obsPositive closed component listed).formula =
      family.formula component := rfl

/-! ## The full component product identifies its host joint -/

/-- Compile the product of every independently identified c-component.

This general result includes empty and singleton partitions as well as the
multi-component branch.  Interleaving components are handled by the actual
partition permutation, and the exact target is a product of recursive
formulas, not a product of fresh observational chain factors. -/
noncomputable def PublishedComponentKernelFamily.productCompilation
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (family : PublishedComponentKernelFamily C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (closed : G.KernelHostClosed remaining externalAction) :
    PublishedPositiveIdentificationCompilation C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩)
      (productTerms ((G.cComponents remaining).map family.formula)) := by
  let vertexChain := topologicalProductPublishedCertificate correct obsPositive
    remaining externalAction closed.action_disjoint family.factor
    (family.factorCertificate obsPositive closed)
    (family.factorCertificate_formula obsPositive closed)
  let blocks := (G.cComponents remaining).map (fun component => (NodeSet.members component).reverse)
  let regrouped := productTermsRegroupingCompilation (C := C) (correct := correct)
    (NodeSet.members remaining).reverse blocks (G.cComponents_members_permutation remaining)
    (by
      intro block member
      rcases List.mem_map.mp member with ⟨component, listed, rfl⟩
      exact listed_component_members_nonempty G remaining listed)
    family.factor (fun node member => family.factor_actionFree node
      ((NodeSet.mem_members_iff remaining node).mp (List.mem_reverse.mp member)))
  let grouped := regrouped.alignedCertificate.reindex rfl
    (show productTerms ((G.cComponents remaining).map
        (fun component => topologicalProductTerm component family.factor)) =
        regrouped.alignedCertificate.formula by
      change _ = productTerms (blocks.map (fun block => productTerms (block.map family.factor)))
      simp only [blocks, List.map_map, topologicalProductTerm]
      rfl)
  let reduced := productTermsMapPublishedCompilation (G.cComponents remaining)
    (fun component => topologicalProductTerm component family.factor) family.formula
    (family.componentProductCertificate obsPositive closed)
    (family.componentProductCertificate_formula obsPositive closed)
  let certificate := (vertexChain.trans grouped).trans reduced.alignedCertificate
  exact {
    certificate := certificate
    formula_eq := rfl
    positive := fun model member reference => productTerms_map_positiveSupportedValue
      model (obsPositive member) (G.cComponents remaining) family.formula reference
      (fun component listed => family.positive component listed model member reference)
  }

/-! ## The engine's product branch retains the original host actions -/

/-- A free-host component's outside actions include the original local
action already.  Consequently adding that action and the free complement
is exactly the original host complement of the component. -/
private theorem componentAction_from_free_eq
    (remaining action component : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (componentSubset : NodeSet.Subset component (NodeSet.diff remaining action)) :
    NodeSet.union action (NodeSet.diff (NodeSet.diff remaining action) component) =
      NodeSet.diff remaining component := by
  funext node
  have actionInside : action node = true -> remaining node = true := actionSubset node
  have componentInside : component node = true ->
      (remaining node && !action node) = true := componentSubset node
  cases hostSelected : remaining node <;> cases actionSelected : action node <;>
    cases componentSelected : component node <;>
    simp_all [NodeSet.union, NodeSet.diff]

/-- The final complementary marginal is exactly the engine's host-level
selection.  This equality is Boolean algebra, not a semantic marginal swap. -/
private theorem free_outcome_complement_eq (remaining action outcome : NodeSet S) :
    NodeSet.diff (NodeSet.diff remaining action) outcome =
      NodeSet.diff remaining (NodeSet.union outcome action) := by
  funext node
  change ((remaining node && Bool.not (action node)) && Bool.not (outcome node)) =
    (remaining node && Bool.not (outcome node || action node))
  cases remaining node <;> cases action node <;> cases outcome node <;> rfl

/-- Compile the complete multi-component product branch from arbitrary
nested component reductions.

The nested sources are exactly the engine's recursive queries: each fixes
`externalAction ∪ (remaining \ component)` in the original host.  The
assembled source fixes only the parent action, and its formula is precisely
the engine's displayed complementary marginal of the ordered component
formula list.  Positivity is retained for the actual output expression.

No whole-free-kernel input certificate is assumed, no fixed component count
is imposed, and no topological noninterleaving condition is required.  The
recursive input is used only for its already established parent closure;
its current expression is never reset to an observational marginal. -/
noncomputable def currentKernelSplitCompilation
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (formulas : NodeSet S -> ProbabilityTerm S)
    (nested : forall component, component ∈ G.cComponents (NodeSet.diff remaining action) ->
      PublishedIdentificationCertificate C correct
        (.kernel ⟨component, NodeSet.union externalAction (NodeSet.diff remaining component), NodeSet.empty⟩))
    (aligned : forall component listed, (nested component listed).formula = formulas component)
    (positive : forall component, component ∈ G.cComponents (NodeSet.diff remaining action) ->
      forall (model : ExactModel S), C.Mem model -> forall reference,
        ProbabilityResult.PositiveSupportedValue ((formulas component).denote model reference)) :
    PublishedPositiveIdentificationCompilation C correct
      (.kernel ⟨outcome, NodeSet.union externalAction action, NodeSet.empty⟩)
      (.marginalize (NodeSet.diff remaining (NodeSet.union outcome action))
        (productTerms ((G.cComponents (NodeSet.diff remaining action)).map formulas))) := by
  let free := NodeSet.diff remaining action
  let baseAction := NodeSet.union externalAction action
  have discarded : NodeSet.diff remaining free = action := by
    change NodeSet.diff remaining (NodeSet.diff remaining action) = action
    rw [NodeSet.diff_diff, NodeSet.inter_eq_of_subset actionSubset]
  have closed : G.KernelHostClosed free baseAction := by
    have restricted := input.closed.restrict free (NodeSet.diff_subset_left remaining action)
    rw [discarded] at restricted
    exact restricted
  have outcomeFree : NodeSet.Subset outcome free := by
    intro node selected
    simp only [free, NodeSet.diff, outcomeSubset node selected, disjoint.symm node selected,
      Bool.not_false, Bool.and_self]
  let family : PublishedComponentKernelFamily C correct free baseAction := {
    formula := formulas
    certificate := fun component listed => (nested component listed).reindex
      (show ProbabilityTerm.kernel ⟨component,
          NodeSet.union baseAction (NodeSet.diff free component), NodeSet.empty⟩ =
          .kernel ⟨component, NodeSet.union externalAction (NodeSet.diff remaining component), NodeSet.empty⟩ by
        change ProbabilityTerm.kernel ⟨component,
          NodeSet.union (NodeSet.union externalAction action)
            (NodeSet.diff (NodeSet.diff remaining action) component), NodeSet.empty⟩ = _
        rw [NodeSet.union_assoc, componentAction_from_free_eq remaining action component
          actionSubset (cComponents_subset G free listed)]) rfl
    formula_eq := fun component listed => aligned component listed
    positive := positive
  }
  let product := family.productCompilation obsPositive closed
  let productCertificate := product.certificate.reindex rfl product.formula_eq.symm
  let marginal := currentKernelMarginalPublishedCertificate correct obsPositive free baseAction outcome
    closed.action_disjoint outcomeFree productCertificate
  let certificate := marginal.reindex rfl
    (show ProbabilityTerm.marginalize (NodeSet.diff remaining (NodeSet.union outcome action))
        (productTerms ((G.cComponents free).map formulas)) = marginal.formula by
      change ProbabilityTerm.marginalize (NodeSet.diff remaining (NodeSet.union outcome action))
          (productTerms ((G.cComponents free).map formulas)) =
        ProbabilityTerm.marginalize (NodeSet.diff free outcome)
        (productTerms ((G.cComponents free).map formulas))
      change ProbabilityTerm.marginalize (NodeSet.diff remaining (NodeSet.union outcome action))
          (productTerms ((G.cComponents free).map formulas)) =
        ProbabilityTerm.marginalize (NodeSet.diff (NodeSet.diff remaining action) outcome)
          (productTerms ((G.cComponents free).map formulas))
      rw [free_outcome_complement_eq])
  exact {
    certificate := certificate
    formula_eq := rfl
    positive := fun model member reference => ProbabilityTerm.marginalizePositiveSupportedValue
      model (NodeSet.diff remaining (NodeSet.union outcome action))
      (productTerms ((G.cComponents free).map formulas)) reference
      (product.positive model member)
  }

end Causality
end Thesis
