import Thesis.CausalTransport.HedgeCompensatedConservation
import Thesis.Examples.HedgeCompensatedReadout
import Thesis.Examples.HedgeInterventionalProbability

namespace Thesis
namespace Causality
namespace Examples

open Probability

/-!
# General compensated conservation at responding and action-cut vertices

The first regression applies the general large-flow theorem to the existing
three-value re-entry chain.  Its conclusion agrees with the independently
expanded row-by-row calculation in `HedgeCompensatedReadout`; the public
theorem now supplies it without assuming that particular graph shape.

The second regression checks a kept forest on the actual extracted node
sets for the confounded chain `A → B → Y` and composite action `{A,B}`.  It
does not normalize the proof-bearing extractor to recover its particular
child map, nor assert equality with that map.  Here `A` is an
intervened non-sink of the kept map.  Both action labels can be the third
observed value.  A further intervention fixes only `A`, leaving the protected
outer-only row `B` free to respond to its parent.  Its complete value, not
merely its `second` bit, is preserved by the compensated plan.

All identities quantify over every old latent unit and fresh-bit family.
They do not enumerate the carrier prior or silently assume that independent
noise integration follows from a pointwise signal identity.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace HedgeCompensatedReentry

open HedgeCarrierReentryReplay (signature rich witness query outcomeNode noise)

/-- General conservation recovers the manually expanded re-entry signal
law, including the responding kept child at the queried outcome. -/
theorem large_outcome_carries_root_signal_of_conservation
    (unit : (witness.largeCarrierDefectParityModel rich).latent.Assignment)
    (bits : Fin signature.count -> Bool) :
    updatedBits unit bits outcomeNode = Bool.xor
      (hedgeRootParityEvent rich witness.roots
        ((witness.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich query.action) unit))
      (hedgeNodeXor witness.smallOutcomeFlowNodes bits) := by
  have allowed : forall node, witness.rootReadoutNodes node = true ->
      witness.small node = true ∨ witness.large node = false := by decide +kernel
  have sinksMembers : NodeSet.members (keptSinks witness.rootReadoutNodes witness.rootReadoutSuccessor) =
      [outcomeNode] := by decide +kernel
  simpa only [hedgeNodeXor, sinksMembers, List.foldl_cons, List.foldl_nil, Bool.false_xor] using
    witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_doSecond rich
      (fun _node => noise) allowed bits unit

end HedgeCompensatedReentry

namespace HedgeCompensatedCompositeAction

open HedgeWeightedTernaryIntervention (signature rich graph query extraction balance outcome intervention)

def middle : Fin signature.count := ⟨1, by decide⟩

def child : ForestChild signature := closedForestChild NodeSet.full query.outcome
def roots : NodeSet signature := keptSinks NodeSet.full child

private theorem large_forest : CForest graph NodeSet.full roots child :=
  cForest_of_child graph NodeSet.full child (by decide +kernel) (by decide +kernel)

private theorem small_forest : CForest graph query.outcome roots (restrictChild query.outcome child) := by
  have sameRoots : keptSinks query.outcome (restrictChild query.outcome child) = roots :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  rw [← sameRoots]
  exact cForest_of_child graph query.outcome (restrictChild query.outcome child) (by decide +kernel) (by decide +kernel)

private theorem roots_selected : NodeSet.Subset roots query.outcome := by
  change forall node : Fin signature.count, roots node = true -> query.outcome node = true
  decide +kernel

noncomputable def witness : HedgeWitness graph query :=
  HedgeWitness.ofForests query NodeSet.full query.outcome roots child large_forest small_forest
    (fun _node _selected => rfl) (by decide +kernel)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel))
    (fun root selected => ⟨root, roots_selected root selected, DirectedReachableBy.refl root⟩)

/-- The checked semantic hedge keeps the actual failure's two node sets;
it makes no assertion about the extractor's chosen child map. -/
theorem witness_matches_failure : witness.large = extraction.witness.large ∧ witness.small = extraction.witness.small :=
  ⟨extraction.large_eq.symm, extraction.small_eq.symm⟩

noncomputable def plan := witness.carrierFlowReadoutPlan rich
  (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide))

noncomputable def model := (witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich plan

private theorem allowed : forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false := by decide +kernel

/-- The first action coordinate really has a retained outgoing child.
Thus the composite-action regression is not a disguised sink-only case. -/
theorem action_has_non_sink : query.action balance = true ∧ witness.child balance = some middle :=
  by decide +kernel

/-- The original action uses the third label at both vertices; conservation
retains the effective sources of these cut equations at their full labels. -/
theorem composite_third_label_signal
    (unit : (witness.largeCarrierDefectParityModel rich).latent.Assignment)
    (bits : Fin signature.count -> Bool) :
    hedgeNodeXor (keptSinks witness.rootReadoutNodes witness.rootReadoutSuccessor)
        (fun node => hedgeIsSecond rich node (model.evalUnder intervention
          ((witness.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits plan unit) node)) =
      Bool.xor (hedgeRootParityEvent rich witness.roots
        ((witness.largeCarrierDefectParityModel rich).evalUnder intervention unit))
        (hedgeNodeXor witness.smallOutcomeFlowNodes bits) := by
  apply witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_evalUnder rich
    (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) allowed bits unit
  exact (by decide +kernel : forall node, witness.smallOutcomeFlowNodes node = true -> intervention node = none)

/-- Fix only the first vertex to the nonbinary label.  The next outer-only
row stays free, so its preservation must account for its responding equation. -/
def first_only_third (node : Fin signature.count) : Option (signature.Value node) :=
  if node = balance then some ⟨2, by decide⟩ else none

theorem middle_is_free_and_protected : first_only_third middle = none ∧
    witness.large middle = true ∧ witness.small middle = false := by decide +kernel

/-- Every full value of the free protected row is unchanged, even with a
nonbinary upstream intervention.  There is no Boolean-alphabet restriction. -/
theorem responding_middle_full_value_unchanged
    (unit : (witness.largeCarrierDefectParityModel rich).latent.Assignment)
    (bits : Fin signature.count -> Bool) :
    model.evalUnder first_only_third
        ((witness.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits plan unit) middle =
      (witness.largeCarrierDefectParityModel rich).evalUnder first_only_third unit middle :=
  witness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_eq_of_outer rich
    (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) allowed bits unit first_only_third middle
    middle_is_free_and_protected.2.1 middle_is_free_and_protected.2.2

end HedgeCompensatedCompositeAction
end Examples
end Causality
end Thesis
