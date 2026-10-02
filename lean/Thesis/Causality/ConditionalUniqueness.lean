import Thesis.Causality.SelectedAssignment
import Thesis.Causality.IdentificationSearch
import Thesis.Probability.ConditionalUniqueness

namespace Thesis
namespace Causality

open Probability

/-!
# Recovering an interventional joint law from both conditional directions

The finite two-way normalization theorem is applied here to actual causal
kernel evaluations.  For a positive model, the outcome and conditioner form
a strictly positive joint table at each fixed intervention.  If two models
agree on both `P(Y | do(X), W)` and `P(W | do(X), Y)`, they agree on the full
joint numerator `P(Y, W | do(X))`.

The intervention values remain fixed while the outcome and conditioning
values are enumerated.  Selected assignments use canonical defaults off
their coordinate sets, so rows are not counted repeatedly and no section of
a quotient is chosen.  Positivity comes from the intrinsic finite-SCM
consistency theorem, not from graph compatibility or do-calculus soundness.

This implication does not assume equal conditioning marginals.  Its
contrapositive is therefore useful when a joint countermodel has a common
reverse conditional but different denominators.  Proving that common reverse
conditional for a particular countermodel remains a separate obligation;
this module does not assert the general conditional completeness theorem.
-/

namespace ConditionalKernelQuery

variable {S : ObservedSignature}

/-- Exchange outcome and conditioner, keeping the intervention unchanged.
This is a new query, not an asserted do-calculus equivalence. -/
def reverse (query : ConditionalKernelQuery S) : ConditionalKernelQuery S where
  outcome := query.condition
  action := query.action
  condition := query.outcome
  action_outcome_disjoint := query.action_condition_disjoint
  action_condition_disjoint := query.action_outcome_disjoint
  outcome_condition_disjoint := query.outcome_condition_disjoint.symm

/-- Reversing both conditional directions returns the original query.
Only the disjointness proof fields are reconstructed, and proof irrelevance
identifies those fields without selecting any new mathematical data. -/
@[simp] theorem reverse_reverse (query : ConditionalKernelQuery S) : query.reverse.reverse = query := by
  cases query
  rfl

/-- Assemble an arbitrary table cell while retaining the supplied action
values.  Disjointness of all three sets makes these instructions consistent. -/
private def cellAssignment (query : ConditionalKernelQuery S)
    (reference : S.Assignment)
    (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) : S.Assignment :=
  fun node => if query.outcome node then row.val node
    else if query.condition node then column.val node else reference node

private theorem cellAssignment_outcome (query : ConditionalKernelQuery S)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) (node : Fin S.count)
    (selected : query.outcome node = true) :
    cellAssignment query reference row column node = row.val node := by
  simp only [cellAssignment, selected, if_true]

private theorem cellAssignment_condition (query : ConditionalKernelQuery S)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) (node : Fin S.count)
    (selected : query.condition node = true) :
    cellAssignment query reference row column node = column.val node := by
  simp only [cellAssignment, query.outcome_condition_disjoint.symm node selected,
    selected, Bool.false_eq_true, if_false, if_true]

private theorem cellAssignment_action (query : ConditionalKernelQuery S)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) (node : Fin S.count)
    (selected : query.action node = true) :
    cellAssignment query reference row column node = reference node := by
  simp only [cellAssignment, query.action_outcome_disjoint node selected,
    query.action_condition_disjoint node selected, Bool.false_eq_true, if_false]

/-- Subtype equality of canonical selected assignments is exactly the
ordinary full-value cylinder on those coordinates. -/
private theorem selected_eq_cylinder (nodes : NodeSet S)
    (target : S.SelectedAssignment nodes) (sample : S.Assignment) :
    decide (S.selectAssignment nodes sample = target) =
      Kernel.agreesOn nodes target.val sample := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, Kernel.agreesOn_iff_project_eq, target.property]
  constructor
  · intro same
    exact congrArg Subtype.val same
  · intro same
    exact Subtype.ext same

/-- The genuine interventional joint table.  Relabelling preserves the
record's atoms, weights, and normalization; it changes only their labels. -/
private def jointTable (query : ConditionalKernelQuery S) (model : ExactModel S)
    (reference : S.Assignment) :
    FiniteProbRecord (S.SelectedAssignment query.outcome × S.SelectedAssignment query.condition) :=
  (query.operationKernel.distribution model reference).map
    (fun sample => (S.selectAssignment query.outcome sample,
      S.selectAssignment query.condition sample))

private theorem cell_distribution (query : ConditionalKernelQuery S) (model : ExactModel S)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) :
    query.operationKernel.distribution model (cellAssignment query reference row column) =
      query.operationKernel.distribution model reference :=
  Kernel.distribution_eq_of_action_reference model query.outcome query.outcome
    query.action query.condition query.condition _ _
    (cellAssignment_action query reference row column)

private theorem jointTable_rowMass (query : ConditionalKernelQuery S) (model : ExactModel S)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome) :
    FiniteProbRecord.eventMass (jointTable query model reference).atoms
        (ConditionalUniqueness.rowEvent row) =
      FiniteProbRecord.eventMass (query.operationKernel.distribution model reference).atoms
        (Kernel.agreesOn query.outcome row.val) := by
  apply Eq.trans (FiniteProbRecord.eventMass_map_labels
    (query.operationKernel.distribution model reference).atoms
    (fun sample => (S.selectAssignment query.outcome sample, S.selectAssignment query.condition sample))
    (ConditionalUniqueness.rowEvent row))
  apply FiniteProbRecord.eventMass_congr
  intro sample
  exact selected_eq_cylinder query.outcome row sample

private theorem jointTable_columnMass (query : ConditionalKernelQuery S) (model : ExactModel S)
    (reference : S.Assignment) (column : S.SelectedAssignment query.condition) :
    FiniteProbRecord.eventMass (jointTable query model reference).atoms
        (ConditionalUniqueness.columnEvent column) =
      FiniteProbRecord.eventMass (query.operationKernel.distribution model reference).atoms
        (Kernel.agreesOn query.condition column.val) := by
  apply Eq.trans (FiniteProbRecord.eventMass_map_labels
    (query.operationKernel.distribution model reference).atoms
    (fun sample => (S.selectAssignment query.outcome sample, S.selectAssignment query.condition sample))
    (ConditionalUniqueness.columnEvent column))
  apply FiniteProbRecord.eventMass_congr
  intro sample
  exact selected_eq_cylinder query.condition column sample

private theorem jointTable_cellMass (query : ConditionalKernelQuery S) (model : ExactModel S)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) :
    FiniteProbRecord.eventMass (jointTable query model reference).atoms
        (ConditionalUniqueness.cellEvent row column) =
      FiniteProbRecord.eventMass
        (query.operationKernel.distribution model (cellAssignment query reference row column)).atoms
        (query.operationKernel.numeratorEvent (cellAssignment query reference row column)) := by
  rw [cell_distribution]
  apply Eq.trans (FiniteProbRecord.eventMass_map_labels
    (query.operationKernel.distribution model reference).atoms
    (fun sample => (S.selectAssignment query.outcome sample, S.selectAssignment query.condition sample))
    (ConditionalUniqueness.cellEvent row column))
  apply FiniteProbRecord.eventMass_congr
  intro sample
  change (decide (S.selectAssignment query.outcome sample = row) &&
    decide (S.selectAssignment query.condition sample = column)) =
      (Kernel.agreesOn query.outcome (cellAssignment query reference row column) sample &&
        Kernel.agreesOn query.condition (cellAssignment query reference row column) sample)
  rw [selected_eq_cylinder, selected_eq_cylinder]
  rw [Kernel.agreesOn_reference_congr query.outcome _ row.val sample
    (cellAssignment_outcome query reference row column)]
  rw [Kernel.agreesOn_reference_congr query.condition _ column.val sample
    (cellAssignment_condition query reference row column)]

private theorem jointTable_conditionMass (query : ConditionalKernelQuery S) (model : ExactModel S)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) :
    FiniteProbRecord.eventMass (jointTable query model reference).atoms
        (ConditionalUniqueness.columnEvent column) =
      FiniteProbRecord.eventMass
        (query.operationKernel.distribution model (cellAssignment query reference row column)).atoms
        (query.operationKernel.conditionEvent (cellAssignment query reference row column)) := by
  rw [jointTable_columnMass, cell_distribution]
  apply FiniteProbRecord.eventMass_congr
  intro sample
  exact (Kernel.agreesOn_reference_congr query.condition _ column.val sample
    (cellAssignment_condition query reference row column)).symm

private theorem jointTable_reverseConditionMass (query : ConditionalKernelQuery S) (model : ExactModel S)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) :
    FiniteProbRecord.eventMass (jointTable query model reference).atoms
        (ConditionalUniqueness.rowEvent row) =
      FiniteProbRecord.eventMass
        (query.reverse.operationKernel.distribution model (cellAssignment query reference row column)).atoms
        (query.reverse.operationKernel.conditionEvent (cellAssignment query reference row column)) := by
  rw [jointTable_rowMass]
  change FiniteProbRecord.eventMass (query.operationKernel.distribution model reference).atoms
      (Kernel.agreesOn query.outcome row.val) =
    FiniteProbRecord.eventMass (query.operationKernel.distribution model (cellAssignment query reference row column)).atoms
      (Kernel.agreesOn query.outcome (cellAssignment query reference row column))
  rw [cell_distribution]
  apply FiniteProbRecord.eventMass_congr
  intro sample
  exact (Kernel.agreesOn_reference_congr query.outcome _ row.val sample
    (cellAssignment_outcome query reference row column)).symm

/-- All cells of the selected table are positive.  The corresponding full
reference agrees with the action, so intrinsic intervention consistency
applies even when the cell is not the original reference cell. -/
private theorem jointTable_cell_positive (query : ConditionalKernelQuery S) (model : ExactModel S)
    (positive : ObservationallyPositive model) (reference : S.Assignment)
    (row : S.SelectedAssignment query.outcome) (column : S.SelectedAssignment query.condition) :
    (jointTable query model reference).EventPositive (ConditionalUniqueness.cellEvent row column) := by
  unfold FiniteProbRecord.EventPositive
  rw [jointTable_cellMass]
  have cylinder : query.operationKernel.numeratorEvent (cellAssignment query reference row column) =
      Kernel.agreesOn (NodeSet.union query.outcome query.condition) (cellAssignment query reference row column) := by
    funext sample
    exact (Kernel.agreesOn_union _ _ _ sample).symm
  rw [cylinder]
  exact positive.kernel_cylinder_positive query.operationKernel _ _

/-- Remove the displayed rational denominators from an equality of supported
conditional results.  Each record contributes its own positive denominator;
neither denominator is assumed to equal the other. -/
private theorem conditional_mass_cross {Ω : Type u}
    (left right : FiniteProbRecord Ω) (event evidence : Event Ω)
    (leftPositive : left.EventPositive evidence) (rightPositive : right.EventPositive evidence)
    (equal : ProbabilityResult.Equivalent
      (ProbabilityResult.divide (some (left.probVal (fun sample => event sample && evidence sample)))
        (some (left.probVal evidence)))
      (ProbabilityResult.divide (some (right.probVal (fun sample => event sample && evidence sample)))
        (some (right.probVal evidence)))) :
    FiniteProbRecord.eventMass left.atoms (fun sample => event sample && evidence sample) *
        FiniteProbRecord.eventMass right.atoms evidence =
      FiniteProbRecord.eventMass right.atoms (fun sample => event sample && evidence sample) *
        FiniteProbRecord.eventMass left.atoms evidence := by
  have leftDenPositive : 0 < (left.probVal evidence).num := leftPositive
  have rightDenPositive : 0 < (right.probVal evidence).num := rightPositive
  simp only [ProbabilityResult.divide, dif_pos leftDenPositive, dif_pos rightDenPositive] at equal
  cases equal with
  | value compared =>
    change (FiniteProbRecord.eventMass left.atoms (fun sample => event sample && evidence sample) * left.den) *
        (right.den * FiniteProbRecord.eventMass right.atoms evidence) =
      (FiniteProbRecord.eventMass right.atoms (fun sample => event sample && evidence sample) * right.den) *
        (left.den * FiniteProbRecord.eventMass left.atoms evidence) at compared
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos left.den_pos right.den_pos)
    calc
      _ = _ := by ac_rfl
      _ = _ := compared
      _ = _ := by ac_rfl

/-- Forward comparison supplies column-normalized mass equalities in the
actual table.  Common-support equivalence is enough, since positivity
constructs both support witnesses at the assembled cell assignment. -/
private theorem jointTable_forward_cross (query : ConditionalKernelQuery S)
    (left right : ExactModel S) (leftPositive : ObservationallyPositive left)
    (rightPositive : ObservationallyPositive right) (equal : query.ValueEquivalent left right)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) :
    FiniteProbRecord.eventMass (jointTable query left reference).atoms (ConditionalUniqueness.cellEvent row column) *
        FiniteProbRecord.eventMass (jointTable query right reference).atoms (ConditionalUniqueness.columnEvent column) =
      FiniteProbRecord.eventMass (jointTable query right reference).atoms (ConditionalUniqueness.cellEvent row column) *
        FiniteProbRecord.eventMass (jointTable query left reference).atoms (ConditionalUniqueness.columnEvent column) := by
  let assignment := cellAssignment query reference row column
  rcases equal assignment
    (leftPositive.kernelPositiveSupportedValue query.operationKernel assignment).toSupported
    (rightPositive.kernelPositiveSupportedValue query.operationKernel assignment).toSupported with ⟨compared⟩
  rw [jointTable_cellMass, jointTable_cellMass,
    jointTable_conditionMass query right reference row column,
    jointTable_conditionMass query left reference row column]
  exact conditional_mass_cross
    (query.operationKernel.distribution left assignment) (query.operationKernel.distribution right assignment)
    (Kernel.agreesOn query.outcome assignment) (Kernel.agreesOn query.condition assignment)
    (leftPositive.kernel_cylinder_positive query.operationKernel query.condition assignment)
    (rightPositive.kernel_cylinder_positive query.operationKernel query.condition assignment) compared

/-- Reverse comparison supplies row-normalized equalities for the same
table.  Only the order of the two cylinder factors changes; the action and
the underlying distribution do not. -/
private theorem jointTable_reverse_cross (query : ConditionalKernelQuery S)
    (left right : ExactModel S) (leftPositive : ObservationallyPositive left)
    (rightPositive : ObservationallyPositive right) (equal : query.reverse.ValueEquivalent left right)
    (reference : S.Assignment) (row : S.SelectedAssignment query.outcome)
    (column : S.SelectedAssignment query.condition) :
    FiniteProbRecord.eventMass (jointTable query left reference).atoms (ConditionalUniqueness.cellEvent row column) *
        FiniteProbRecord.eventMass (jointTable query right reference).atoms (ConditionalUniqueness.rowEvent row) =
      FiniteProbRecord.eventMass (jointTable query right reference).atoms (ConditionalUniqueness.cellEvent row column) *
        FiniteProbRecord.eventMass (jointTable query left reference).atoms (ConditionalUniqueness.rowEvent row) := by
  let assignment := cellAssignment query reference row column
  rcases equal assignment
    (leftPositive.kernelPositiveSupportedValue query.reverse.operationKernel assignment).toSupported
    (rightPositive.kernelPositiveSupportedValue query.reverse.operationKernel assignment).toSupported with ⟨compared⟩
  have cross := conditional_mass_cross
    (query.reverse.operationKernel.distribution left assignment) (query.reverse.operationKernel.distribution right assignment)
    (Kernel.agreesOn query.condition assignment) (Kernel.agreesOn query.outcome assignment)
    (leftPositive.kernel_cylinder_positive query.reverse.operationKernel query.outcome assignment)
    (rightPositive.kernel_cylinder_positive query.reverse.operationKernel query.outcome assignment) compared
  have commute : (fun sample => Kernel.agreesOn query.condition assignment sample &&
      Kernel.agreesOn query.outcome assignment sample) = query.operationKernel.numeratorEvent assignment := by
    funext sample
    exact Bool.and_comm _ _
  rw [commute] at cross
  rw [jointTable_cellMass, jointTable_cellMass,
    jointTable_reverseConditionMass query right reference row column,
    jointTable_reverseConditionMass query left reference row column]
  exact cross

/-- The reference row and column give precisely the original joint
numerator cylinder.  Projection defaults disappear on selected nodes. -/
private theorem jointTable_reference_probVal (query : ConditionalKernelQuery S) (model : ExactModel S)
    (reference : S.Assignment) :
    (jointTable query model reference).probVal
        (ConditionalUniqueness.cellEvent (S.selectAssignment query.outcome reference)
          (S.selectAssignment query.condition reference)) =
      (query.jointNumerator.operationKernel.distribution model reference).probVal
        (Kernel.agreesOn query.jointNumerator.outcome reference) := by
  apply congrArg (fun mass => (⟨mass, (query.operationKernel.distribution model reference).den,
    (query.operationKernel.distribution model reference).den_pos⟩ : QProb))
  apply Eq.trans (FiniteProbRecord.eventMass_map_labels
    (query.operationKernel.distribution model reference).atoms
    (fun sample => (S.selectAssignment query.outcome sample, S.selectAssignment query.condition sample))
    (ConditionalUniqueness.cellEvent (S.selectAssignment query.outcome reference)
      (S.selectAssignment query.condition reference)))
  apply FiniteProbRecord.eventMass_congr
  intro sample
  change (decide (S.selectAssignment query.outcome sample = S.selectAssignment query.outcome reference) &&
    decide (S.selectAssignment query.condition sample = S.selectAssignment query.condition reference)) = _
  rw [selected_eq_cylinder, selected_eq_cylinder]
  rw [Kernel.agreesOn_reference_congr query.outcome _ reference sample
    (fun node selected => by simp only [ObservedSignature.selectAssignment, ObservedSignature.project, selected, if_true])]
  rw [Kernel.agreesOn_reference_congr query.condition _ reference sample
    (fun node selected => by simp only [ObservedSignature.selectAssignment, ObservedSignature.project, selected, if_true])]
  exact (Kernel.agreesOn_union _ _ _ _).symm

/-- Positive causal models agreeing in both conditional directions agree
on the full joint numerator.  No equality or identifiability assumption is
made for `query.jointDenominator`.  Every value comparison refers to the
same intervention, and all support evidence is supplied intrinsically. -/
theorem jointNumerator_valueEquivalent_of_twoWayConditionals
    (query : ConditionalKernelQuery S) (left right : ExactModel S)
    (leftPositive : ObservationallyPositive left) (rightPositive : ObservationallyPositive right)
    (forward : query.ValueEquivalent left right) (backward : query.reverse.ValueEquivalent left right) :
    query.jointNumerator.ValueEquivalent left right := by
  intro reference
  let column := S.selectAssignment query.condition reference
  have cells := jointTable_cell_positive query right rightPositive reference
  have columnPositive : (jointTable query right reference).EventPositive (ConditionalUniqueness.columnEvent column) :=
    Nat.lt_of_lt_of_le (cells (S.selectAssignment query.outcome reference) column)
      (FiniteProbRecord.eventMass_mono _ _ _ (fun _ selected => (Bool.and_eq_true_iff.mp selected).2))
  have cellEqual := FiniteProbRecord.cell_probVal_equiv_of_twoWayConditionalMasses
    (jointTable query left reference) (jointTable query right reference)
    (S.selectedAssignmentEnumeration query.outcome)
    (S.selectedAssignmentEnumeration_nodup query.outcome)
    (S.selectedAssignmentEnumeration_complete query.outcome) column columnPositive
    (fun row => cells row column)
    (fun row => jointTable_forward_cross query left right leftPositive rightPositive forward reference row column)
    (jointTable_reverse_cross query left right leftPositive rightPositive backward reference)
    (S.selectAssignment query.outcome reference) column
  change QProb.Equiv
    ((jointTable query left reference).probVal (ConditionalUniqueness.cellEvent
      (S.selectAssignment query.outcome reference) (S.selectAssignment query.condition reference)))
    ((jointTable query right reference).probVal (ConditionalUniqueness.cellEvent
      (S.selectAssignment query.outcome reference) (S.selectAssignment query.condition reference))) at cellEqual
  rw [jointTable_reference_probVal, jointTable_reference_probVal] at cellEqual
  exact ⟨ProbabilityResult.trans
    (Kernel.unconditionalDenote left query.jointNumerator.outcome query.action reference)
    (ProbabilityResult.trans (.value cellEqual)
      (ProbabilityResult.symm (Kernel.unconditionalDenote right query.jointNumerator.outcome query.action reference)))⟩

end ConditionalKernelQuery

end Causality
end Thesis
