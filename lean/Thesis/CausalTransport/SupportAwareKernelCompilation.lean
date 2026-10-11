import Thesis.CausalTransport.KernelCompilation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}

/-!
# Current-kernel reductions with assignment-local support

The old recursive input bundles a derivation with everywhere-positive target
values.  Those values are useful for the positive theorem, but are not needed
to construct the derivation itself.  Here the current-expression invariant
retains its actual action-free syntax and its inspectable path derivation;
support is supplied separately at the finitely enumerated references used
by a marginal or at the displayed denominator of a prefix quotient.

This is not a new semantic-equality leaf.  Every constructor below assembles
ordinary marginalization, conditioning and congruence derivation nodes.
The support constructors return the established `LocalDerivationSupport`
tree, so the existing published soundness theorem interprets the result.
They do not change the meaning of a missing conditional or a zero outcome.

An initial observational reduction is constructed without regularity.  The
marginal constructor preserves gaps, external intervention parameters and
the exact current input.  A factor's support is needed only at its actual
reference and marginal variants, and only its displayed denominator must
be positive.  This supplies the input algebra for the continuing zero-aware
component and recursive-ID compiler; it does not yet claim that compiler
or a zero-unrestricted engine-success iff theorem is complete.
-/

/-- Syntactic current-host reduction, with no model-class regularity premise.
Local semantic support remains explicit rather than being asserted globally.
The source keeps previously fixed external intervention coordinates. -/
structure PublishedCurrentKernelReduction (G : ObservedGraph S)
    (remaining externalAction : NodeSet S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G
    (.kernel ⟨remaining, externalAction, NodeSet.empty⟩) formula

namespace PublishedCurrentKernelReduction

variable {remaining externalAction : NodeSet S}

/-- The initial full observational input is a genuine reflexive reduction,
including at null observed cells.  Its support does not require positivity. -/
def observational (G : ObservedGraph S) :
    PublishedCurrentKernelReduction G NodeSet.full NodeSet.empty where
  formula := observationalJointTerm S
  actionFree := observationalJointTerm_actionFree S
  derivation := DoCalculusDerivation.refl (G := G) (separation := pathRuleSeparation G) _

/-- Retain the actual syntax of an existing published input, without
calling its class-indexed support field or strengthening its model class. -/
def ofCertificate {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    (certificate : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩)) :
    PublishedCurrentKernelReduction G remaining externalAction where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation

/-- Marginalize the same current expression.  This construction concerns
only finite host geometry and syntax; it assumes neither support nor a
positive model, and does not reset the expression to an observational law. -/
def marginal (input : PublishedCurrentKernelReduction G remaining externalAction)
    (kept : NodeSet S) (outside : NodeSet.Disjoint externalAction remaining)
    (keptSubset : NodeSet.Subset kept remaining) :
    PublishedCurrentKernelReduction G kept externalAction := by
  let removed := NodeSet.diff remaining kept
  have sourceEq : ProbabilityTerm.kernel
      ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩ =
      .kernel ⟨remaining, externalAction, NodeSet.empty⟩ := by
    rw [NodeSet.union_diff_eq keptSubset]
  let covered : PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩) input.formula :=
    DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
      sourceEq rfl input.derivation
  let split : PathDoCalculusDerivation G
      (.kernel ⟨kept, externalAction, NodeSet.empty⟩)
      (.marginalize removed
        (.kernel ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩)) :=
    DoCalculusDerivation.marginalization (G := G) (separation := pathRuleSeparation G)
      externalAction kept removed NodeSet.empty
      (FourWayDisjoint.of_empty_w externalAction kept removed
        (NodeSet.disjoint_of_subset_right outside keptSubset)
        (NodeSet.disjoint_of_subset_right outside (NodeSet.diff_subset_left remaining kept))
        (NodeSet.disjoint_diff remaining kept))
  exact {
    formula := .marginalize removed input.formula
    actionFree := input.actionFree
    derivation := DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G)
      split (DoCalculusDerivation.marginalizeCongr (G := G)
        (separation := pathRuleSeparation G) removed covered)
  }

theorem marginal_formula (input : PublishedCurrentKernelReduction G remaining externalAction)
    (kept : NodeSet S) (outside : NodeSet.Disjoint externalAction remaining)
    (keptSubset : NodeSet.Subset kept remaining) :
    (input.marginal kept outside keptSubset).formula =
      .marginalize (NodeSet.diff remaining kept) input.formula := rfl

/-- Construct the marginal's ordinary recursive support tree from the input
trees at precisely its enumerated variants.  Every unconditional source
summand is intrinsically supported, including a zero summand. -/
noncomputable def marginal_supportedAt
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G)
    (kept : NodeSet S) (outside : NodeSet.Disjoint externalAction remaining)
    (keptSubset : NodeSet.Subset kept remaining)
    (model : ExactModel S) (reference : S.Assignment)
    (inputSupport : forall variant,
      variant ∈ ProbabilityTerm.marginalAssignments S (NodeSet.diff remaining kept) reference →
        LocalDerivationSupport model variant (input.derivation.compile correct)) :
    LocalDerivationSupport model reference
      ((input.marginal kept outside keptSubset).derivation.compile correct) := by
  let removed := NodeSet.diff remaining kept
  let sourceSupported := Kernel.unconditional_supportedAt model kept externalAction reference
  let intermediate := ProbabilityTerm.marginalize_supportedAt_of_mem model removed
    (.kernel ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩) reference
    (fun variant _listed => Kernel.unconditional_supportedAt model
      (NodeSet.union kept removed) externalAction variant)
  let targetSupported := ProbabilityTerm.marginalize_supportedAt_of_mem model removed
    input.formula reference (fun variant listed => (inputSupport variant listed).endpoints.2)
  dsimp [marginal, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨sourceSupported, ⟨targetSupported,
    ⟨⟨sourceSupported, ⟨intermediate, ()⟩⟩,
      ⟨intermediate, ⟨targetSupported, fun variant listed =>
        ⟨Kernel.unconditional_supportedAt model (NodeSet.union kept removed) externalAction variant,
          ⟨(inputSupport variant listed).endpoints.2, inputSupport variant listed⟩⟩⟩⟩⟩⟩⟩

/-- The exact replacement-engine prefix quotient, compiled by conditioning
and two marginals of the same input.  No support or positivity is consumed
while constructing the inspectable derivation. -/
def factorDerivation (input : PublishedCurrentKernelReduction G remaining externalAction)
    (outside : NodeSet.Disjoint externalAction remaining)
    (node : Fin S.count) (selected : remaining node = true) :
    PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩)
      (chainFactorFrom remaining input.formula node) := by
  let earlier := chainCondition remaining node
  have earlierSubset : NodeSet.Subset earlier remaining := by
    intro vertex member
    exact (Bool.and_eq_true_iff.mp member).1
  have prefixSubset : NodeSet.Subset (NodeSet.union (NodeSet.singleton node) earlier) remaining :=
    NodeSet.union_subset (NodeSet.singleton_subset_of_mem selected) earlierSubset
  let numerator := input.marginal (NodeSet.union (NodeSet.singleton node) earlier) outside prefixSubset
  let denominator := input.marginal earlier outside earlierSubset
  let split : PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, externalAction, NodeSet.union earlier NodeSet.empty⟩)
      (.divide
        (.kernel ⟨NodeSet.union (NodeSet.singleton node) earlier, externalAction, NodeSet.empty⟩)
        (.kernel ⟨earlier, externalAction, NodeSet.empty⟩)) :=
    DoCalculusDerivation.conditioning (G := G) (separation := pathRuleSeparation G)
      externalAction (NodeSet.singleton node) earlier NodeSet.empty
      (FourWayDisjoint.of_empty_w externalAction (NodeSet.singleton node) earlier
        (NodeSet.disjoint_of_subset_right outside (NodeSet.singleton_subset_of_mem selected))
        (NodeSet.disjoint_of_subset_right outside earlierSubset)
        (disjoint_singleton_chainCondition remaining node))
  exact DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
    (by rw [NodeSet.union_empty_right]) rfl
    (DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G)
      split (DoCalculusDerivation.divideCongr (G := G) (separation := pathRuleSeparation G)
        numerator.derivation denominator.derivation))

/-- Prefix quotients remain action-free even if some references have null
denominators.  Action-freeness is syntax, not a claim of global support. -/
theorem factor_actionFree (input : PublishedCurrentKernelReduction G remaining externalAction)
    (node : Fin S.count) : (chainFactorFrom remaining input.formula node).ActionFree :=
  chainFactorFrom_actionFree remaining input.formula node input.actionFree

/-- The factor's recursive support is assignment-local.  Only its actual
denominator marginal must be positive; its numerator may be a supported zero.
Input support is supplied at the two finite marginal enumerations, not at
every assignment in the signature.  Intrinsic quotient normalization supplies
the conditioning intermediate, without applying identification soundness. -/
noncomputable def factor_supportedAt
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G)
    (outside : NodeSet.Disjoint externalAction remaining)
    (node : Fin S.count) (selected : remaining node = true)
    (model : ExactModel S) (reference : S.Assignment)
    (sourceSupported : (ProbabilityTerm.kernel
      ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩).SupportedAt model reference)
    (numeratorInputSupport : forall variant,
      variant ∈ ProbabilityTerm.marginalAssignments S
        (NodeSet.diff remaining (NodeSet.union (NodeSet.singleton node)
          (chainCondition remaining node))) reference →
        LocalDerivationSupport model variant (input.derivation.compile correct))
    (denominatorInputSupport : forall variant,
      variant ∈ ProbabilityTerm.marginalAssignments S
        (NodeSet.diff remaining (chainCondition remaining node)) reference →
        LocalDerivationSupport model variant (input.derivation.compile correct))
    (denominatorPositive : ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.marginalize (NodeSet.diff remaining (chainCondition remaining node))
        input.formula).denote model reference)) :
    LocalDerivationSupport model reference
      ((input.factorDerivation outside node selected).compile correct) := by
  let earlier := chainCondition remaining node
  have earlierSubset : NodeSet.Subset earlier remaining := by
    intro vertex member
    exact (Bool.and_eq_true_iff.mp member).1
  have prefixSubset : NodeSet.Subset (NodeSet.union (NodeSet.singleton node) earlier) remaining :=
    NodeSet.union_subset (NodeSet.singleton_subset_of_mem selected) earlierSubset
  let numeratorSupport := input.marginal_supportedAt correct
    (NodeSet.union (NodeSet.singleton node) earlier) outside prefixSubset model reference
    numeratorInputSupport
  let denominatorSupport := input.marginal_supportedAt correct earlier outside earlierSubset
    model reference denominatorInputSupport
  let targetSupported := ProbabilityResult.divide_supported_of_positive_denominator
    numeratorSupport.endpoints.2 denominatorPositive
  let intermediate := ProbabilityTerm.SupportedAt.of_equivalent
    (Kernel.unconditionalQuotient_equivalentAt model
      ⟨NodeSet.singleton node, externalAction, earlier⟩ reference) sourceSupported
  have splitSourceSupported : (ProbabilityTerm.kernel
      ⟨NodeSet.singleton node, externalAction, NodeSet.union earlier NodeSet.empty⟩).SupportedAt
      model reference := by
    simpa only [NodeSet.union_empty_right] using sourceSupported
  dsimp [factorDerivation, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨sourceSupported, ⟨targetSupported,
    ⟨splitSourceSupported, ⟨targetSupported,
      ⟨⟨splitSourceSupported, ⟨intermediate, ()⟩⟩,
        ⟨intermediate, ⟨targetSupported, ⟨numeratorSupport, denominatorSupport⟩⟩⟩⟩⟩⟩⟩⟩

end PublishedCurrentKernelReduction
end Causality
end Thesis
