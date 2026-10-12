import Thesis.CausalTransport.LocalKernelCompilation
import Thesis.CausalTransport.KernelRecursionCompilation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S} {correct : DSeparationCorrectness G}

/-!
# Joint-query transformations preserve recursive local data

Pruning and action augmentation change the query, not the recursively
compiled target expression.  Both rule-3 endpoints are unconditional joint
kernels, so their actual support is constructed directly from the finite
records, including at zero outcome cells.  No observed action overlap or
global positivity is needed solely for these joint-query transformations.

The nested compilation's primitive `Data` is retained unchanged.  The
constructors add the real rule/equality nodes and their endpoint support to
the existing support tree; they do not assume a new semantic equation.
Containing-component recursion changes only the external/local action split
and therefore needs the proved Boolean source equality, not another rule.
-/

namespace PublishedLocalKernelCompilation

/-- Prepend one actual rule-3 action deletion.  Every new source/intermediate
support value is an intrinsic unconditional cylinder in the same model. -/
noncomputable def prependDeleteActions (x y z : NodeSet S)
    (application : PathDoRuleApplication G (rule3Left x y z NodeSet.empty) (rule3Right x y z NodeSet.empty))
    (nested : PublishedLocalKernelCompilation G correct y x) :
    PublishedLocalKernelCompilation G correct y (NodeSet.union x z) where
  reduction := {
    formula := nested.reduction.formula
    actionFree := nested.reduction.actionFree
    derivation := DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.doRule (G := G) (separation := pathRuleSeparation G) application) nested.reduction.derivation
  }
  Data := nested.Data
  supported := fun model reference data => by
    let inner := nested.supported model reference data
    let source := Kernel.unconditional_supportedAt model y (NodeSet.union x z) reference
    let middle := Kernel.unconditional_supportedAt model y x reference
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    exact ⟨source, ⟨inner.endpoints.2, ⟨⟨source, ⟨middle, ()⟩⟩, inner⟩⟩⟩

/-- Reverse the same actual rule-3 application to add actions before using
the nested result.  The reversed leaf retains its forward support tree. -/
noncomputable def prependAddActions (x y z : NodeSet S)
    (application : PathDoRuleApplication G (rule3Left x y z NodeSet.empty) (rule3Right x y z NodeSet.empty))
    (nested : PublishedLocalKernelCompilation G correct y (NodeSet.union x z)) :
    PublishedLocalKernelCompilation G correct y x where
  reduction := {
    formula := nested.reduction.formula
    actionFree := nested.reduction.actionFree
    derivation := DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.symm (G := G) (separation := pathRuleSeparation G)
        (DoCalculusDerivation.doRule (G := G) (separation := pathRuleSeparation G) application)) nested.reduction.derivation
  }
  Data := nested.Data
  supported := fun model reference data => by
    let inner := nested.supported model reference data
    let source := Kernel.unconditional_supportedAt model y x reference
    let middle := Kernel.unconditional_supportedAt model y (NodeSet.union x z) reference
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    exact ⟨source, ⟨inner.endpoints.2, ⟨⟨source, ⟨middle, ⟨middle, ⟨source, ()⟩⟩⟩⟩, inner⟩⟩⟩

end PublishedLocalKernelCompilation

/-- Remove the local actions outside uncut outcome ancestry.  Parent
closure supplies the actual path-side condition; the nested target and
its recursively defined local data remain unchanged. -/
noncomputable def localKernelPruneCompilation
    {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S) (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining) (disjoint : NodeSet.Disjoint action outcome)
    (nested : PublishedLocalKernelCompilation G correct outcome
      (NodeSet.union externalAction (NodeSet.inter action (G.ancestralSet remaining (.none S) outcome)))) :
    PublishedLocalKernelCompilation G correct outcome (NodeSet.union externalAction action) := by
  let kept := G.ancestralSet remaining (.none S) outcome
  let keptAction := NodeSet.inter action kept
  let removed := NodeSet.diff action kept
  let baseAction := NodeSet.union externalAction keptAction
  have keptSubset : NodeSet.Subset keptAction action := NodeSet.inter_subset_left _ _
  have removedSubset := (NodeSet.diff_subset_left action kept).trans actionSubset
  have four : FourWayDisjoint baseAction outcome removed NodeSet.empty := FourWayDisjoint.of_empty_w _ _ _
    (NodeSet.disjoint_union_left_of (NodeSet.disjoint_of_subset_right closed.action_disjoint outcomeSubset)
      (NodeSet.Disjoint.of_subset_left disjoint keptSubset))
    (NodeSet.disjoint_union_left_of (NodeSet.disjoint_of_subset_right closed.action_disjoint removedSubset)
      (NodeSet.disjoint_inter_diff action kept))
    (NodeSet.disjoint_of_subset_right disjoint.symm (NodeSet.diff_subset_left action kept))
  let application := DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G)
    baseAction outcome removed NodeSet.empty four
    (G.pathDSeparated_rule3_prune_actions remaining externalAction action outcome closed actionSubset outcomeSubset)
  let deleted := PublishedLocalKernelCompilation.prependDeleteActions baseAction outcome removed application nested
  exact deleted.reindex nested.reduction.formula
    (by simp only [baseAction, keptAction, removed, NodeSet.union_assoc, NodeSet.union_inter_diff]) rfl

/-- Reverse rule 3 for exactly the incoming-cut additional-action block.
No marginalization is introduced and no current-input expression is reset. -/
noncomputable def localKernelAdditionalActionCompilation
    {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction) (action outcome : NodeSet S)
    (disjoint : NodeSet.Disjoint (NodeSet.inter action remaining) (NodeSet.inter outcome remaining))
    (nested : PublishedLocalKernelCompilation G correct (NodeSet.inter outcome remaining)
      (NodeSet.union externalAction (NodeSet.union (NodeSet.inter action remaining)
        (identificationAdditionalAction G remaining outcome action)))) :
    PublishedLocalKernelCompilation G correct (NodeSet.inter outcome remaining)
      (NodeSet.union externalAction (NodeSet.inter action remaining)) := by
  let localAction := NodeSet.inter action remaining
  let localOutcome := NodeSet.inter outcome remaining
  let additional := identificationAdditionalAction G remaining outcome action
  let baseAction := NodeSet.union externalAction localAction
  have four : FourWayDisjoint baseAction localOutcome additional NodeSet.empty := FourWayDisjoint.of_empty_w _ _ _
    (NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint (NodeSet.inter_subset_right _ _)) disjoint)
    (NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint
        (identificationAdditionalAction_subset_remaining G remaining outcome action))
      (identificationAdditionalAction_disjoint_action G remaining outcome action).symm)
    (identificationAdditionalAction_disjoint_outcome G remaining outcome action).symm
  let reindexed := nested.reindex nested.reduction.formula
    (by simp only [baseAction, NodeSet.union_assoc]) rfl
  exact PublishedLocalKernelCompilation.prependAddActions baseAction localOutcome additional
    (DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G) baseAction localOutcome additional NodeSet.empty four
      (G.pathDSeparated_rule3_additional_action remaining externalAction action outcome closed)) reindexed

/-- A containing component discards only already fixed action vertices.
The actual source is therefore reindexed, with no semantic algebra step. -/
noncomputable def localKernelRestrictionCompilation
    (remaining kept externalAction action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (discarded : NodeSet.Subset (NodeSet.diff remaining kept) action)
    (nested : PublishedLocalKernelCompilation G correct outcome
      (NodeSet.union (NodeSet.union externalAction (NodeSet.diff remaining kept)) (NodeSet.inter action kept))) :
    PublishedLocalKernelCompilation G correct outcome (NodeSet.union externalAction action) :=
  nested.reindex nested.reduction.formula
    (by rw [NodeSet.union_assoc,
      currentKernelRestrictionAction_eq remaining kept action actionSubset discarded]) rfl

end Causality
end Thesis
