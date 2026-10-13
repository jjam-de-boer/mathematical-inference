import Thesis.CausalTransport.CurrentKernelFamilySupportCompletion
import Thesis.CausalTransport.GuardedEvaluationSupport

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}

/-!
# Construct guarded prefix support from printed-only factor obligations

The previous support constructors ask for factor data under either a causal
or a printed positive prefix.  That is a sufficient boundary, but its causal
guard is not itself observable.  This module replaces the two independent
demand sets by a well-founded prefix construction.

At each selected vertex, the preceding prefix tree has already been built.
Only that completed tree is interpreted.  Its actual causal and printed
values agree, so a positive causal weight supplies a positive printed weight.
The next factor's primitive data can therefore be requested solely on its
printed positive branch.  Soundness of the next factor or the complete fold
is not assumed to establish the preceding prefix equality.

The probability expression and derivation stay literal: this is support of
the existing `GuardedHostChain.prefixDerivation`, not a replacement expression
or a new semantic rule.  Zero weights still skip undefined factors.  The
generic builder takes a primitive semantics record; its component and family
adapters below construct that record from the already proved projected-graph
theorem, including noncanonical multi-child root models.

Printed factor inputs still include the recursively preceding marginal
trees and displayed denominators.  Reading and constructing those inputs
uniformly from the actual successful program's admissible observation domain
remains separate; it is not assumed completed by the prefix bridge.
-/

namespace GuardedHostChain

/-- Build each prefix before interpreting it.  The source callback receives
both positive-prefix witnesses, while the target callback needs only the
printed one.  No callback is demanded at a zero weight. -/
noncomputable def prefix_supportedAt_of_printed_factors
    (correct : DSeparationCorrectness G)
    (remaining action : NodeSet S) (outside : NodeSet.Disjoint action remaining)
    (factor : Fin S.count → ProbabilityTerm S)
    (factorDerivation : forall node, remaining node = true → PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, action, chainCondition remaining node⟩) (factor node))
    (model : ExactModel S) (reference : S.Assignment) (semantics : LocalPrimitiveSoundness G model)
    (sourceFactorSupport : forall node (selected : remaining node = true),
      ProbabilityResult.PositiveSupportedValue
        ((ProbabilityTerm.kernel ⟨chainPrefix remaining node.val, action, NodeSet.empty⟩).denote model reference) →
      ProbabilityResult.PositiveSupportedValue
        ((prefixTerm remaining factor node.val (Nat.le_of_lt node.isLt)).denote model reference) →
      LocalDerivationSupport model reference ((factorDerivation node selected).compile correct))
    (targetFactorSupport : forall node, remaining node = true →
      ProbabilityResult.PositiveSupportedValue
        ((prefixTerm remaining factor node.val (Nat.le_of_lt node.isLt)).denote model reference) →
      (factor node).SupportedAt model reference) :
    (n : Nat) → (bound : n ≤ S.count) → LocalDerivationSupport model reference
      ((prefixDerivation remaining action outside factor factorDerivation n bound).compile correct)
  | 0, _ => by
      let sourceSupported := Kernel.unconditional_supportedAt model NodeSet.empty action reference
      let initialSupported := Kernel.unconditional_supportedAt model (chainPrefix remaining 0) action reference
      let targetSupported := Kernel.unconditional_supportedAt model NodeSet.empty NodeSet.empty reference
      let query : JointKernelQuery S := ⟨NodeSet.empty, action, NodeSet.disjoint_empty_right _⟩
      let ruleSupported := ProbabilityTerm.SupportedAt.congr
        (JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw query) sourceSupported
      dsimp [prefixDerivation, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        deleteActionRule3Derivation]
      exact ⟨initialSupported, ⟨targetSupported,
        ⟨sourceSupported, ⟨targetSupported, ⟨ruleSupported, ⟨targetSupported, ()⟩⟩⟩⟩⟩⟩
  | n + 1, bound => by
      let node : Fin S.count := ⟨n, Nat.lt_of_succ_le bound⟩
      let previousBound : n ≤ S.count := Nat.le_trans (Nat.le_succ n) bound
      let previousSupport := prefix_supportedAt_of_printed_factors correct remaining action outside factor factorDerivation
        model reference semantics sourceFactorSupport targetFactorSupport n previousBound
      cases selected : remaining node with
      | false =>
          have notSelected : ¬ remaining node = true := by
            rw [selected]
            exact Bool.false_ne_true
          let sourceSupported := Kernel.unconditional_supportedAt model (chainPrefix remaining (n + 1)) action reference
          have targetSupported : (prefixTerm remaining factor (n + 1) bound).SupportedAt model reference := by
            simpa only [prefixTerm, node, selected, Bool.false_eq_true, if_false] using previousSupport.endpoints.2
          dsimp [prefixDerivation, node]
          simp only [node] at notSelected
          simp only [notSelected]
          dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
          exact ⟨sourceSupported, ⟨targetSupported, previousSupport⟩⟩
      | true =>
          let previousNodes := chainPrefix remaining n
          let previousEquality :=
            ((prefixDerivation remaining action outside factor factorDerivation n previousBound).compile correct)
              .denotational_soundAt semantics previousSupport
          let sourceSupported := Kernel.unconditional_supportedAt model (chainPrefix remaining (n + 1)) action reference
          let jointSupported := Kernel.unconditional_supportedAt model
            (NodeSet.union (NodeSet.singleton node) previousNodes) action reference
          let splitSupported := ProbabilityTerm.SupportedAt.of_equivalent
            (ProbabilityTerm.weightedChain_soundAt model action (NodeSet.singleton node) previousNodes NodeSet.empty reference)
            jointSupported
          have intermediate : (ProbabilityTerm.weightedMultiply
              (.kernel ⟨previousNodes, action, NodeSet.empty⟩)
              (.kernel ⟨NodeSet.singleton node, action, chainCondition remaining node⟩)).SupportedAt model reference := by
            simpa only [NodeSet.union_empty_right, chainCondition_eq_prefix, node] using splitSupported
          let factorTree := fun sourcePositive => sourceFactorSupport node selected sourcePositive
            (ProbabilityResult.PositiveSupportedValue.transport previousEquality sourcePositive)
          let targetSupported := ProbabilityResult.weightedMultiply_supported previousSupport.endpoints.2
            (targetFactorSupport node selected)
          have displayedSupported : (prefixTerm remaining factor (n + 1) bound).SupportedAt model reference := by
            simpa only [prefixTerm, node, selected, if_true] using targetSupported
          dsimp [prefixDerivation, node]
          simp only [node] at selected
          simp only [selected, dif_pos]
          dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
          exact ⟨sourceSupported, ⟨displayedSupported,
            ⟨jointSupported, ⟨targetSupported,
              ⟨⟨jointSupported, ⟨intermediate, ⟨jointSupported, ⟨splitSupported, ()⟩⟩⟩⟩,
                ⟨intermediate, ⟨targetSupported, ⟨previousSupport, factorTree⟩⟩⟩⟩⟩⟩⟩⟩

end GuardedHostChain

variable {remaining externalAction : NodeSet S}

/-- Only positive printed component prefixes request quotient inputs.
There is no causal-prefix premise in the caller's factor-data callback. -/
def PrintedCurrentKernelComponentConditions
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G) (component : NodeSet S)
    (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node, component node = true →
    ProbabilityResult.PositiveSupportedValue
      ((guardedComponentPrefixTerm remaining input.formula component node.val
        (Nat.le_of_lt node.isLt)).denote model reference) →
    CurrentKernelFactorInputs input correct model reference node

namespace PublishedCurrentKernelReduction

/-- Interpret only completed preceding prefixes to construct the original
component tree from printed-branch quotient inputs.  The arbitrary bound is
needed by the data adapter at each factor vertex, not just at the full host. -/
noncomputable def guardedComponentPrefix_supportedAt_of_printed_inputs
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (conditions : PrintedCurrentKernelComponentConditions input correct component model reference) :
    (n : Nat) → (bound : n ≤ S.count) → LocalDerivationSupport model reference
      ((input.guardedComponentPrefixDerivation component closed componentSubset bidirectedClosed n bound).compile correct) :=
  GuardedHostChain.prefix_supportedAt_of_printed_factors correct component
    (componentExternalAction remaining externalAction component)
    (NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint componentSubset)
      (NodeSet.disjoint_diff_right remaining component))
    (chainFactorFrom remaining input.formula)
    (fun node selected => input.componentFactorDerivation component closed componentSubset bidirectedClosed node selected)
    model reference (model.projectedLocalPrimitiveSoundness projected correct)
    (fun node selected _sourcePositive printedPositive => input.componentFactor_supportedAt correct component closed
      componentSubset bidirectedClosed node selected model reference
      ((conditions node selected printedPositive).host_supportedAt closed.action_disjoint (componentSubset node selected)))
    (fun node selected printedPositive =>
      ((conditions node selected printedPositive).host_supportedAt closed.action_disjoint
        (componentSubset node selected)).endpoints.2)

end PublishedCurrentKernelReduction

/-- The family fold likewise requests child quotient data only on a printed
positive prefix.  Source support is constructed internally from the matched
actual host-prefix value when its graph-rule tree is needed. -/
def PrintedCurrentKernelFamilyConditions
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node (selected : remaining node = true),
    ProbabilityResult.PositiveSupportedValue
      ((GuardedHostChain.prefixTerm remaining family.factor node.val (Nat.le_of_lt node.isLt)).denote model reference) →
    CurrentKernelFamilyFactorInputs family correct model reference node selected

/-- Family-prefix support at every bound, preserving the exact factor
lookup and graph-rule derivations of the actual assembled host. -/
noncomputable def PublishedComponentKernelReductionFamily.guardedPrefix_supportedAt_of_printed_inputs
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (closed : G.KernelHostClosed remaining externalAction)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (conditions : PrintedCurrentKernelFamilyConditions family correct model reference) :
    (n : Nat) → (bound : n ≤ S.count) → LocalDerivationSupport model reference
      ((GuardedHostChain.prefixDerivation remaining externalAction closed.action_disjoint family.factor
        (family.factorDerivation closed) n bound).compile correct) :=
  GuardedHostChain.prefix_supportedAt_of_printed_factors correct remaining externalAction closed.action_disjoint
    family.factor (family.factorDerivation closed) model reference (model.projectedLocalPrimitiveSoundness projected correct)
    (fun node selected sourcePositive printedPositive => (conditions node selected printedPositive).factor_supportedAt closed
      (Kernel.supportedAt_of_positive_unconditional_conditioner model (NodeSet.singleton node) externalAction
        (chainCondition remaining node) reference (by simpa only [chainCondition_eq_prefix] using sourcePositive)))
    (fun node selected printedPositive => (conditions node selected printedPositive).target_supportedAt)

end Causality
end Thesis
