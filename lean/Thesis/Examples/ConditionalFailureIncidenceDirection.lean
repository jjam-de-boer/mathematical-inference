import Thesis.CausalTransport.ConditionalFailureIncidenceDirection
import Thesis.Examples.ConditionalFailureForkApproach
import Thesis.Examples.ConditionalFailurePathIncidence

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureIncidenceDirection

open Probability FiniteBooleanInteraction PathSpecification
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureSmallPrefixDirection

/-!
# The actual finite incidence constructor on an outside-Small failure

The genuine five-vertex query has Small `U,R`, evidence `P` outside Small,
and actual normalized path `P <- Y`.  The starting outcome column is read
at `P`.  The mandatory approach retains the actual edge `R -> P`, whose
free observed coordinate has exactly the two selected incidences `R,P`.

Thus the actual finite incidence graph connects `P` to Small in one step.
The new general constructor, rather than a manually proposed correction,
computes its row, original realizing coordinate and Small target.  It proves
support, outcome oddness and every outside-Small background row even, then
constructs positive original-alphabet countermodels for the unchanged query.

The opaque normalization is never executed.  Its previously proved actual
window and graph-local column identities supply the finite edge test.  This
regression exercises the entire connection-to-countermodel adapter, but
does not prove that every terminal's actual incidence graph reaches Small.
-/

private theorem root_in_small : witness.small commonRoot = true := by decide +kernel

private theorem root_retained : normal.forkApproachNodes boundary pivot forest commonRoot = true :=
  boundary.small_subset_absorbingNodes _ _ commonRoot root_in_small

private theorem root_selected : normal.forkAbsorbedInteractionRows boundary pivot forest commonRoot = true :=
  NodeSet.subset_union_right _ _ commonRoot root_retained

private theorem pivot_selected : normal.forkAbsorbedInteractionRows boundary pivot forest pivotNode = true := by
  apply NodeSet.subset_union_left _ _
  rw [actual_core]
  exact (NodeSet.singleton_eq_true_iff pivotNode pivotNode).mpr rfl

private theorem root_noncontact : normal.forkAbsorptionTargets pivot forest commonRoot = false := by
  rw [CurrentConditionalFailureForkApproach.actual_targets]
  decide +kernel

private theorem root_successor : normal.forkAbsorptionSuccessor boundary pivot forest commonRoot = some pivotNode := by
  rw [normal.forkAbsorptionSuccessor_noncontact boundary pivot forest commonRoot root_retained root_noncontact]
  decide +kernel

/-- The finite starting-row scan returns the actual outside-Small pivot.
This follows from the proved whole singleton column, without evaluating the
opaque normalizer or supplying its outgoing endpoint orientation. -/
theorem actual_starting_row : normal.forkOutcomeIncidenceRow boundary pivot forest = pivotNode := by
  have column := normal.forkOutcomeIncidence_basis_single boundary pivot forest pivotNode
  change (if _ then _ else false) = _ at column
  rw [CurrentConditionalFailurePathIncidence.actual_outcome_basis_pivot pivotNode, decide_eq_true rfl] at column
  exact (of_decide_eq_true column.symm).symm

/-- The actual original `R` coordinate passes the complete guarded pair
test.  Fixed evidence `P` itself is never used as a correction coordinate. -/
theorem actual_pivot_root_edge : normal.forkPairIncidence boundary pivot forest pivotNode commonRoot = true := by
  apply LinearSignal.pairIncidence_of_column _ _ _ _ pivotNode commonRoot
    (Fin.natAdd (pairRootCount graph.binary) commonRoot) pivot_selected root_selected
    (by decide +kernel)
  · change FiniteProduct.BooleanBlocks.rightBlock _ _
      (cubeMask graph (NodeSet.union query.action query.condition)) commonRoot = false
    rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
    decide +kernel
  · change FiniteProduct.BooleanBlocks.rightBlock _ _
      (cubeMask graph (NodeSet.singleton normal.outcome)) commonRoot = false
    rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
    have same := (NodeSet.singleton_eq_true_iff outcome normal.outcome).mp normal.outcome_selected
    rw [same]
    decide +kernel
  · intro row
    have actual := normal.forkAbsorbedInteraction_noncontact_basis_pair boundary pivot forest root_noncontact root_successor row
    unfold LinearSignal.selectedRowValue
    rw [actual]
    cases chosen : normal.forkAbsorbedInteractionRows boundary pivot forest row with
    | true => simp only [if_true]; exact Bool.xor_comm _ _
    | false =>
        have notPivot : row ≠ pivotNode := by
          intro same
          subst row
          exact Bool.false_ne_true (chosen.symm.trans pivot_selected)
        have notRoot : row ≠ commonRoot := by
          intro same
          subst row
          exact Bool.false_ne_true (chosen.symm.trans root_selected)
        simp only [Bool.false_eq_true, if_false, decide_eq_false notPivot, decide_eq_false notRoot]
        rfl

/-- One actual tested column reaches an original Small row.  The finite
search theorem is used only in Prop; the general direction constructor
still computes its own route and coordinate by the successful scans. -/
theorem actual_connection : normal.forkOutcomeReachesSmallTest boundary pivot forest 1 = true := by
  apply List.any_eq_true.mpr
  refine ⟨commonRoot, (NodeSet.mem_members_iff witness.small commonRoot).mpr root_in_small, ?_⟩
  rw [actual_starting_row]
  apply (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated signature)
    (normal.forkPairIncidence boundary pivot forest) finBeq_eq_true_iff (NodeSet.mem_enumerated signature)
    1 pivotNode commonRoot).mpr
  exact ⟨1, Nat.le_refl 1, ⟨.step actual_pivot_root_edge (.refl commonRoot)⟩⟩

/-- This is the general scan/transport output, not the companion's
manually instantiated proper-prefix direction. -/
def readout := normal.forkIncidenceReadout boundary pivot forest 1 actual_connection

theorem readout_supported : readout.direction ∈
    FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) := readout.supported

theorem readout_outcome_odd : (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value readout.direction = true :=
  readout.outcome_odd

/-- The general actual-row theorem checks every original background row,
including the outside-Small pivot whose initial outcome incidence was odd. -/
theorem readout_background_even (row : Fin signature.count)
    (chosen : normal.forkAbsorbedInteractionBackgroundRows boundary pivot forest row = true) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value readout.direction = false :=
  normal.forkIncidenceReadout_background_even boundary pivot forest 1 actual_connection row chosen

/-- Original three-valued positive models from the full finite connection
adapter, not a separately supplied probability gap or parity certificate. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfForkIncidenceReachability witness rich boundary pivot normal forest 1 actual_connection

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end CurrentConditionalFailureIncidenceDirection
end Examples
end Causality
end Thesis
