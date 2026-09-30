import Thesis.CausalTransport.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentKernelFailureExtraction

/-!
# Regression checks for structural current-kernel failure extraction

The fixtures below exercise each recursive failure transport with an actual
engine equation.  They do not provide a nested hedge or a hand-built forest:
the general fuel induction constructs both forests and restores the original
query.  Exact failure coordinates check that pruning and restriction retain
their smaller host rather than incorrectly claiming the full original host.

The immediate example also separates ordinary host ancestry from incoming-cut
host ancestry.  The latter is not the whole host, although the corrected
program legitimately fails.  This prevents reuse of the legacy failure proof
with an invariant that the replacement algorithm does not establish.

All finite branch checks use ordinary kernel reduction or constructive Boolean
node-set tests.  There is no model-specific semantic assumption or classical
function-equality decision in these regressions.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Exact failure equations use finite set equality, not function decisions -/

/-- Read the computed failure record.  A successful or unfinished result has
an inert fallback; the failure equation below proves that fallback is not
used in any of these fixtures. -/
private def computedFailure {S : ObservedSignature} (result : IdentificationOutcome S) :
    IdentificationFail S :=
  match result with
  | .failed fail => fail
  | _ => ⟨NodeSet.empty, NodeSet.empty⟩

/-- Align the computed Boolean node sets with a human-readable failure
record.  Function-valued node selections are compared by their finite
Boolean equality test, not by a classical `DecidableEq` instance. -/
private theorem failedWithCoordinates {S : ObservedSignature}
    (result : IdentificationOutcome S) (remaining free : NodeSet S)
    (failed : result = .failed (computedFailure result))
    (large : NodeSet.equal (computedFailure result).remaining remaining = true)
    (small : NodeSet.equal (computedFailure result).free free = true) :
    result = .failed ⟨remaining, free⟩ := by
  have largeEqual := (NodeSet.equal_eq_true_iff _ _).mp large
  have smallEqual := (NodeSet.equal_eq_true_iff _ _).mp small
  have aligned : computedFailure result = ⟨remaining, free⟩ := by
    cases record : computedFailure result with
    | mk host component =>
        rw [record] at largeEqual smallEqual
        cases largeEqual
        cases smallEqual
        rfl
  exact failed.trans (congrArg IdentificationOutcome.failed aligned)

/-! ## Small ordered signatures and explicit bidirected partitions -/

/-- Directed edges follow the consecutive topological chain.  An optional
last vertex can be made isolated for the ancestral-pruning fixture. -/
def chainSignature (count : Nat) (lastIsolated : Bool := false) : ObservedSignature where
  count := count
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (child.val = parent.val + 1) &&
    !(lastIsolated && decide (child.val + 1 = count))
  directed_earlier := by
    intro parent child edge
    have next : child.val = parent.val + 1 := of_decide_eq_true (Bool.and_eq_true_iff.mp edge).1
    omega

/-- Vertices with the same Boolean label form a bidirected clique.
Different labels give separate components; the diagonal is always absent. -/
def partitionGraph (S : ObservedSignature) (label : Fin S.count -> Bool) : ObservedGraph S where
  bidirected := fun left right => decide (left ≠ right) && decide (label left = label right)
  bidirected_symmetric := by
    intro left right edge
    simpa only [ne_comm, eq_comm] using edge
  bidirected_irreflexive := by intro node; simp

/-! ## Immediate failure does not require whole-host incoming-cut ancestry -/

def immediateSignature := chainSignature 3
def immediateGraph := partitionGraph immediateSignature (fun _ => false)
def immediateAction : NodeSet immediateSignature := fun node => decide (node.val < 2)
def immediateOutcome : NodeSet immediateSignature := NodeSet.singleton ⟨2, by decide⟩
def immediateQuery : JointKernelQuery immediateSignature where
  outcome := immediateOutcome
  action := immediateAction
  action_outcome_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

/-- Uncut ancestry retains both consecutive action vertices. -/
theorem immediate_uncut_ancestry_full : NodeSet.equal
    (immediateGraph.ancestralSet NodeSet.full (GraphMutilation.none immediateSignature) immediateOutcome)
    NodeSet.full = true := by decide +kernel

/-- Cutting incoming arrows at the middle action deletes the first vertex's
route.  This is exactly the whole-host premise the legacy argument cannot
require of an immediate failure in the corrected program. -/
theorem immediate_cut_ancestry_not_full : NodeSet.equal
    (immediateGraph.ancestralSet NodeSet.full (GraphMutilation.bar immediateAction) immediateOutcome)
    NodeSet.full = false := by decide +kernel

theorem immediate_failed : identifyJointKernel immediateGraph immediateQuery =
    .failed ⟨NodeSet.full, immediateOutcome⟩ := by
  apply failedWithCoordinates
  · rfl
  · decide +kernel
  · decide +kernel

noncomputable def immediateExtraction := identifyJointKernelFailedHedge immediateQuery immediate_failed

theorem immediate_large : immediateExtraction.witness.large = NodeSet.full := immediateExtraction.large_eq
theorem immediate_small : immediateExtraction.witness.small = immediateOutcome := immediateExtraction.small_eq

/-! ## Pruning an unrelated vertex still witnesses the original query -/

def pruningSignature := chainSignature 4 true
def pruningGraph := partitionGraph pruningSignature (fun node => decide (node.val = 3))
def pruningHost : NodeSet pruningSignature := fun node => decide (node.val < 3)
def pruningOutcome : NodeSet pruningSignature := NodeSet.singleton ⟨2, by decide⟩
def pruningQuery : JointKernelQuery pruningSignature where
  outcome := pruningOutcome
  action := fun node => decide (node.val < 2)
  action_outcome_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

/-- The actual initial branch discards the isolated fourth vertex. -/
theorem pruning_ancestry_proper : NodeSet.equal
    (pruningGraph.ancestralSet NodeSet.full (GraphMutilation.none pruningSignature) pruningOutcome)
    NodeSet.full = false := by decide +kernel

theorem pruning_failed : identifyJointKernel pruningGraph pruningQuery =
    .failed ⟨pruningHost, pruningOutcome⟩ := by
  apply failedWithCoordinates
  · rfl
  · decide +kernel
  · decide +kernel

noncomputable def pruningExtraction := identifyJointKernelFailedHedge pruningQuery pruning_failed

/-- The returned hedge is indexed by the original four-node query, but its
large forest is the terminal three-node ancestral host. -/
theorem pruning_large : pruningExtraction.witness.large = pruningHost := pruningExtraction.large_eq

/-! ## Nonempty action augmentation cannot create a spurious parent hedge -/

def augmentationQuery : JointKernelQuery immediateSignature where
  outcome := immediateOutcome
  action := NodeSet.singleton ⟨1, by decide⟩
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

/-- The first action blocks the zero vertex's route through the middle
vertex, so the program adds exactly that zero vertex to the intervention. -/
theorem augmentation_added_zero : NodeSet.equal
    (identificationAdditionalAction immediateGraph NodeSet.full augmentationQuery.outcome augmentationQuery.action)
    (NodeSet.singleton ⟨0, by decide⟩) = true := by decide +kernel

theorem augmentation_failed : identifyJointKernel immediateGraph augmentationQuery =
    .failed ⟨NodeSet.full, immediateOutcome⟩ := by
  apply failedWithCoordinates
  · rfl
  · decide +kernel
  · decide +kernel

noncomputable def augmentationExtraction := identifyJointKernelFailedHedge augmentationQuery augmentation_failed

/-- Contact is with the original middle-vertex action, not merely the added
zero vertex.  The structural extractor proves this without a supplied seed. -/
theorem augmentation_original_action : NodeSet.meetsBool augmentationExtraction.witness.large
    augmentationQuery.action = true :=
  (NodeSet.meetsBool_eq_true_iff _ _).mpr augmentationExtraction.witness.large_meets_intervention

/-! ## Containing-component restriction retains the external action split -/

def restrictionSignature := chainSignature 4
def restrictionGraph := partitionGraph restrictionSignature (fun node => decide (node.val = 0))
def restrictionHost : NodeSet restrictionSignature := fun node => decide (0 < node.val)
def restrictionFree : NodeSet restrictionSignature := fun node => decide (1 < node.val)
def restrictionOutcome : NodeSet restrictionSignature := NodeSet.singleton ⟨3, by decide⟩
def restrictionAction : NodeSet restrictionSignature := fun node => decide (node.val < 2)
def restrictionQuery : JointKernelQuery restrictionSignature where
  outcome := restrictionOutcome
  action := restrictionAction
  action_outcome_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

/-- The sole free component is properly contained in `{1,2,3}`, not already
a complete component of the full host.  Restriction is therefore recursive. -/
theorem restriction_containing : restrictionGraph.containingCComponent NodeSet.full restrictionFree =
    some restrictionHost := by
  apply congrArg some
  apply (NodeSet.equal_eq_true_iff _ _).mp
  decide +kernel

theorem restriction_failed : identifyJointKernel restrictionGraph restrictionQuery =
    .failed ⟨restrictionHost, restrictionFree⟩ := by
  apply failedWithCoordinates
  · rfl
  · decide +kernel
  · decide +kernel

noncomputable def restrictionExtraction := identifyJointKernelFailedHedge restrictionQuery restriction_failed

theorem restriction_large : restrictionExtraction.witness.large = restrictionHost := restrictionExtraction.large_eq
theorem restriction_small : restrictionExtraction.witness.small = restrictionFree := restrictionExtraction.small_eq

/-! ## A failed product factor is lifted beyond its own outcome component -/

def productGraph := partitionGraph immediateSignature (fun node => decide (node.val = 2))
def productOutcome : NodeSet immediateSignature := fun node => decide (0 < node.val)
def productHost : NodeSet immediateSignature := fun node => decide (node.val < 2)
def productFree : NodeSet immediateSignature := NodeSet.singleton ⟨1, by decide⟩
def productQuery : JointKernelQuery immediateSignature where
  outcome := productOutcome
  action := NodeSet.singleton ⟨0, by decide⟩
  action_outcome_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

/-- Both free vertices are separate components, so this really enters the
collector rather than testing a single-component failure in disguise. -/
theorem product_two_factors : (productGraph.cComponents (NodeSet.diff NodeSet.full productQuery.action)).length = 2 := by rfl

theorem product_failed : identifyJointKernel productGraph productQuery =
    .failed ⟨productHost, productFree⟩ := by
  apply failedWithCoordinates
  · rfl
  · decide +kernel
  · decide +kernel

noncomputable def productExtraction := identifyJointKernelFailedHedge productQuery product_failed

/-- The factor is pruned before failing.  Both nested transports preserve
the actual smaller forest while returning a hedge for the two-outcome query. -/
theorem product_large : productExtraction.witness.large = productHost := productExtraction.large_eq
theorem product_small : productExtraction.witness.small = productFree := productExtraction.small_eq

/-! ## Recursive failure does not require a certified or positive input term -/

/-- A host with a missing initial vertex has a nonempty external action.
The general recursive interface accepts even a zero current expression:
failure extraction is graph-only, independently of the success invariant. -/
noncomputable def recursiveExtraction :=
  identifyKernelFuelFailedHedge (kernelIdentificationFuel restrictionSignature)
    ((ObservedGraph.KernelHostClosed.full restrictionGraph).restrict restrictionHost (fun _ _ => rfl))
    (NodeSet.singleton ⟨1, by decide⟩) restrictionOutcome .zero
    (NodeSet.singleton_subset_of_mem (by decide : restrictionHost ⟨1, by decide⟩ = true))
    (NodeSet.singleton_subset_of_mem (by decide : restrictionHost ⟨3, by decide⟩ = true))
    (NodeSet.disjoint_singletons_of_ne (by decide))
    (show identifyKernelFuel (kernelIdentificationFuel restrictionSignature) restrictionGraph restrictionHost
      restrictionOutcome (NodeSet.singleton ⟨1, by decide⟩) .zero =
      .failed ⟨restrictionHost, restrictionFree⟩ by
      apply failedWithCoordinates
      · rfl
      · decide +kernel
      · decide +kernel)

theorem recursive_large : recursiveExtraction.witness.large = restrictionHost := recursiveExtraction.large_eq

/-! ## Graph-only extraction is not restricted to value universe zero -/

/-- Finite node selections always live in `Type`, even when observed values
live higher.  The product collector's lifted input representation must not
silently specialize the general failure theorem to the lowest universe. -/
noncomputable def higherUniverseExtraction
    {S : ObservedSignature.{1}} {G : ObservedGraph S}
    (query : JointKernelQuery S) {fail : IdentificationFail S}
    (result : identifyJointKernel G query = .failed fail) : HedgeWitness G query :=
  (identifyJointKernelFailedHedge query result).witness

end CurrentKernelFailureExtraction
end Examples
end Causality
end Thesis
