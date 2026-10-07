import Thesis.Examples.HedgeObstructionModel

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeObstructionCounterexample

open Probability
open HedgeObstructionLikelihood HedgeObstructionModel

/-!
# Positive original-query countermodels for the outer-reentry obstruction

The structural realization and its full observed law live in
`HedgeObstructionModel`.  This module verifies the intervention against those
same models, then applies the general private label refinement to the
original three-valued signature.  The final query remains `P(Y | do(A,B))`:
neither the graph, the supplied observed alphabets, nor the action/outcome
sets are replaced by a surrogate root-parity problem.

The exact causal gap comes from deleting precisely the `A` and `B` rows.
All other responses, including the outside relay and outer re-entry, are
retained.  This is a countermodel for a graph outside the old compensated
carrier coverage family.  It is not a proof of universal completeness.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def intervention (node : Fin signature.count) : Option Bool :=
  if node.val = 0 ∨ node.val = 4 then some false else none

def outcomeEvent : Event signature.Assignment := fun sample => sample y

private def consistent (sample : Observation) : Bool := !sample.a && !sample.b

private def freeRowWeight (perturbed : Bool) (sample : Observation) (unit : Hidden) : Nat :=
  outputWeight 1024 (rTrueWeight perturbed unit) sample.r *
    outputWeight 6 (if sample.r then 5 else 1) sample.u *
    outputWeight 6 (vTrueWeight sample unit) sample.v *
    outputWeight 6 (qTrueWeight sample unit) sample.q *
    outputWeight 6 (yTrueWeight sample) sample.y

private def interventionSlice (perturbed : Bool) (sample : Observation) (unit : Hidden) : QProb :=
  FiniteProduct.qProduct (tables perturbed).extension.count
    ((tables perturbed).sliceFactors intervention (hiddenAssignment unit) (observationAssignment sample))

private def interventionWeight (perturbed : Bool) (sample : Observation) (unit : Hidden) : QProb :=
  ⟨if consistent sample then freeRowWeight perturbed sample unit else 0,
    interventionDenominator, by decide⟩

/-- Forced-node consistency gives zero for an assignment with a nonzero
action bit, and otherwise gives the five remaining likelihood factors.
The check uses actual SCM slice factors, not a guessed truncation rule. -/
private theorem intervention_slice_checks (perturbed : Bool) (sample : Observation) :
    hiddenAssignments.all (fun unit => decide
      (QProb.Equiv (interventionSlice perturbed sample unit) (interventionWeight perturbed sample unit))) = true := by
  rcases sample with ⟨sa, sr, su, sv, sb, sq, sy⟩
  cases perturbed <;> cases sa <;> cases sr <;> cases su <;>
    cases sv <;> cases sb <;> cases sq <;> cases sy <;> decide +kernel

private theorem interventionSlice_equiv (perturbed : Bool) (sample : Observation) (unit : Hidden) :
    QProb.Equiv (interventionSlice perturbed sample unit) (interventionWeight perturbed sample unit) := by
  exact of_decide_eq_true (List.all_eq_true.mp (intervention_slice_checks perturbed sample)
    unit (hiddenAssignments_complete unit))

private def assignmentNumerator (perturbed : Bool) (sample : Observation) : Nat :=
  if consistent sample then (hiddenAssignments.map (freeRowWeight perturbed sample)).sum else 0

private theorem sum_constant_zero {α : Type} (values : List α) :
    (values.map (fun _ => (0 : Nat))).sum = 0 := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simpa only [List.map_cons, List.sum_cons, Nat.zero_add] using inductionHypothesis

private theorem assignmentNumerator_eq_sum (perturbed : Bool) (sample : Observation) :
    (hiddenAssignments.map (fun unit => if consistent sample then freeRowWeight perturbed sample unit else 0)).sum =
      assignmentNumerator perturbed sample := by
  cases selected : consistent sample
  · simp only [selected, Bool.false_eq_true, if_false, assignmentNumerator]
    exact sum_constant_zero hiddenAssignments
  · simp only [selected, if_true, assignmentNumerator]

private theorem interventionLikelihood_equiv (perturbed : Bool) (sample : Observation) :
    QProb.Equiv ((tables perturbed).likelihoodWith hiddenEnumeration intervention (observationAssignment sample))
      ⟨assignmentNumerator perturbed sample, interventionDenominator, by decide⟩ := by
  rw [likelihoodWith_hiddenEnumeration]
  refine QProb.equiv_trans
    (QProb.listSum_map_congr hiddenAssignments _ _ (interventionSlice_equiv perturbed sample)) ?_
  have summed := QProb.listSum_mk_same_den interventionDenominator (by decide)
    (hiddenAssignments.map fun unit => if consistent sample then freeRowWeight perturbed sample unit else 0)
  rw [List.map_map, assignmentNumerator_eq_sum] at summed
  exact summed

/-- A Boolean filter can instead be represented by zero contributions.
This elementary induction is kept explicit to avoid choosing or classically
selecting supported observations from a probability record. -/
private theorem sum_selected {α : Type} (values : List α) (selected : α → Bool) (weight : α → Nat) :
    (values.map (fun value => if selected value then weight value else 0)).sum =
      ((values.filter selected).map weight).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      cases atValue : selected value <;>
        simp only [List.map_cons, List.sum_cons, List.filter_cons, atValue,
          Bool.false_eq_true, if_false, if_true, Nat.zero_add, inductionHypothesis]

private theorem assignmentNumerator_sum (perturbed : Bool) :
    ((observations.filter fun sample => sample.y).map (assignmentNumerator perturbed)).sum =
      interventionNumerator perturbed := by
  unfold assignmentNumerator
  rw [sum_selected]
  simp only [List.filter_filter]
  have predicates : (fun sample : Observation => consistent sample && sample.y) =
      (fun sample => !sample.a && !sample.b && sample.y) := by
    funext sample
    simp only [consistent, Bool.and_comm]
  rw [predicates]
  rfl

/-- The exact interventional event probability belongs to the realized SCM
with all four pair sources and all non-intervened structural equations. -/
theorem model_intervention_probability (perturbed : Bool) :
    QProb.Equiv ((model perturbed).interventionalValue intervention outcomeEvent)
      (interventionProbability perturbed) := by
  have semantics := (tables perturbed).toSCM_interventionalValue_likelihoodWith
    hiddenEnumeration hiddenEnumeration_nodup hiddenEnumeration_complete
    sampleEnumeration sampleEnumeration_nodup sampleEnumeration_complete intervention outcomeEvent
  refine QProb.equiv_trans semantics ?_
  have pointwise (sample : signature.Assignment) :
      QProb.Equiv ((tables perturbed).likelihoodWith hiddenEnumeration intervention sample)
        ⟨assignmentNumerator perturbed (observationOfAssignment sample), interventionDenominator, by decide⟩ := by
    have likelihood := interventionLikelihood_equiv perturbed (observationOfAssignment sample)
    rw [observationAssignment_ofAssignment] at likelihood
    exact likelihood
  refine QProb.equiv_trans (QProb.listSum_map_congr (sampleEnumeration.filter outcomeEvent) _ _ pointwise) ?_
  have mapped :
      ((sampleEnumeration.filter outcomeEvent).map (fun sample =>
        (⟨assignmentNumerator perturbed (observationOfAssignment sample), interventionDenominator, by decide⟩ : QProb))) =
      ((observations.filter fun sample => sample.y).map (fun sample =>
        (⟨assignmentNumerator perturbed sample, interventionDenominator, by decide⟩ : QProb))) := by
    simp only [sampleEnumeration, List.filter_map, List.map_map, Function.comp_def,
      observationOfAssignment_assignment]
    rfl
  rw [mapped]
  have summed := QProb.listSum_mk_same_den interventionDenominator (by decide)
    ((observations.filter fun sample => sample.y).map (assignmentNumerator perturbed))
  rw [List.map_map, assignmentNumerator_sum] at summed
  exact summed

/-- The algebraic half-probability is the actual causal value of the
unperturbed structural model, not just of its truncated-table expression. -/
theorem model_intervention_unperturbed :
    QProb.Equiv ((model false).interventionalValue intervention outcomeEvent) ⟨1, 2, by decide⟩ :=
  QProb.equiv_trans (model_intervention_probability false) interventionProbability_unperturbed

/-- The same semantic bridge retains the small but exact perturbation gap. -/
theorem model_intervention_perturbed :
    QProb.Equiv ((model true).interventionalValue intervention outcomeEvent) ⟨31103, 62208, by decide⟩ :=
  QProb.equiv_trans (model_intervention_probability true) interventionProbability_perturbed

/-- Observational equality does not extend to this original causal event. -/
theorem model_intervention_separated : Not (QProb.Equiv
    ((model false).interventionalValue intervention outcomeEvent)
    ((model true).interventionalValue intervention outcomeEvent)) := by
  intro equal
  exact interventionProbability_separated (QProb.equiv_trans
    (QProb.equiv_symm (model_intervention_probability false))
    (QProb.equiv_trans equal (model_intervention_probability true)))

/-! ## Return to the original supplied three-valued signature -/

def rich : ObservedSignature.ValueRich originalSignature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

/-- The event reads the original outcome's distinguished bit.  Additional
labels are filled by private refinement, not by changing the query. -/
def query : InterventionalQuery originalSignature where
  intervention := ⟨fun node => if HedgeCarrierRouteObstruction.action node then some (rich.first node) else none⟩
  outcomeNodes := HedgeCarrierRouteObstruction.query.outcome
  action_outcome_disjoint := by
    intro node selected
    have targets : (if HedgeCarrierRouteObstruction.action node then some (rich.first node) else none).isSome =
        HedgeCarrierRouteObstruction.action node := by
      cases HedgeCarrierRouteObstruction.action node <;> rfl
    change (if HedgeCarrierRouteObstruction.action node then some (rich.first node) else none).isSome = true at selected
    exact HedgeCarrierRouteObstruction.query.action_outcome_disjoint node (targets.symm.trans selected)
  event := fun sample => ObservedValueRefinement.bit rich y (sample y)
  event_local := by
    intro first second agree
    exact congrArg (ObservedValueRefinement.bit rich y)
      (agree y (by change NodeSet.singleton y y = true; exact (NodeSet.singleton_eq_true_iff y y).mpr rfl))

private theorem jointQuery_ext {S : ObservedSignature} (first second : JointKernelQuery S)
    (outcome : first.outcome = second.outcome) (action : first.action = second.action) : first = second := by
  cases first
  cases second
  cases outcome
  cases action
  rfl

theorem query_kernel_original : query.kernelQuery = HedgeCarrierRouteObstruction.query := by
  have targets : query.intervention.targets = HedgeCarrierRouteObstruction.action := by
    funext node
    change (if HedgeCarrierRouteObstruction.action node then some (rich.first node) else none).isSome =
      HedgeCarrierRouteObstruction.action node
    cases HedgeCarrierRouteObstruction.action node <;> rfl
  exact jointQuery_ext _ _ rfl targets

private theorem query_factors (sample : originalSignature.Assignment) :
    query.event sample = outcomeEvent (ObservedValueRefinement.bits (S := originalSignature) rich sample) := rfl

private theorem decoded_intervention :
    (ObservedValueRefinement.binaryQuery rich query outcomeEvent query_factors).intervention.value = intervention := by
  funext node
  change (if HedgeCarrierRouteObstruction.action node then some (rich.first node) else none).map
    (ObservedValueRefinement.bit rich node) = intervention node
  by_cases active : node.val = 0 ∨ node.val = 4
  · have selected : HedgeCarrierRouteObstruction.action node = true := decide_eq_true active
    simp only [selected, if_true, Option.map_some, intervention, active]
    exact congrArg some (decide_eq_false (rich.different node))
  · have excluded : HedgeCarrierRouteObstruction.action node = false := decide_eq_false active
    simp only [excluded, Bool.false_eq_true, if_false, Option.map_none, intervention, active]

private theorem binary_query_value (base : ExactModel signature) :
    (ObservedValueRefinement.binaryQuery rich query outcomeEvent query_factors).value base =
      base.interventionalValue intervention outcomeEvent := by
  have active : finAny signature.count
      (ObservedValueRefinement.binaryQuery rich query outcomeEvent query_factors).intervention.targets = true :=
    (finAny_eq_true_iff _).mpr ⟨a, by
      change ((ObservedValueRefinement.binaryQuery rich query outcomeEvent query_factors).intervention.value a).isSome = true
      rw [decoded_intervention]
      rfl⟩
  unfold InterventionalQuery.value InterventionalQuery.distribution
  rw [active]
  simp only [if_true]
  change base.interventionalValue
    (ObservedValueRefinement.binaryQuery rich query outcomeEvent query_factors).intervention.value outcomeEvent =
      base.interventionalValue intervention outcomeEvent
  exact congrArg (fun target => base.interventionalValue target outcomeEvent) decoded_intervention

/-- The final pair is positive on every original three-valued observed
assignment, graph-compatible, and observationally indistinguishable.  Its
original `Y` kernel differs under the original action set `{A,B}`.

The general binary-to-rich-label theorem supplies actual encoded and
privately refined models.  It preserves all node indices and alphabets;
no positivity or observational equivalence is assumed for a surrogate law. -/
noncomputable def counterexample :
    CounterexampleIn (GraphModelClass.positive HedgeCarrierRouteObstruction.graph)
      HedgeCarrierRouteObstruction.query := by
  rw [← query_kernel_original]
  exact ObservedValueRefinement.positiveCounterexampleOfBinaryEvent rich query (model false) (model true)
    (model_compatible false) (model_compatible true) (model_positive false) (model_positive true)
    models_observationally_equivalent outcomeEvent query_factors (by
      intro equal
      exact model_intervention_separated (Eq.mp
        ((congrArg (fun left => QProb.Equiv left
            ((ObservedValueRefinement.binaryQuery rich query outcomeEvent query_factors).value (model true)))
          (binary_query_value (model false))).trans
          (congrArg (QProb.Equiv ((model false).interventionalValue intervention outcomeEvent))
            (binary_query_value (model true)))) equal))

/-- This ID-failure regression is genuinely non-identifiable in the positive
model class, even though no compensated route-ready hedge can cover it. -/
theorem original_query_not_identifiable :
    Not ((GraphModelClass.positive HedgeCarrierRouteObstruction.graph).identifiable
      HedgeCarrierRouteObstruction.query) := counterexample.not_identifiable

end HedgeObstructionCounterexample
end Examples
end Causality
end Thesis
