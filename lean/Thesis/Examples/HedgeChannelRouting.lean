import Thesis.CausalTransport.HedgeChannelRouting
import Thesis.CausalTransport.HedgeChannelInterventional
import Thesis.CausalTransport.HedgeChannelCounterexample
import Thesis.CausalTransport.HedgeChannelConditionalCounterexample

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelRouting

open Probability

/-!
# An original outcome beyond the small forest

The graph is `A -> R -> Y`, `A <-> R`; the hedge's large forest is `{A,R}`
and its small forest is `{R}`, but the original query is `P(Y | do(A))`.
Thus a gap at a full `R` assignment would not answer the query.  The existing
outcome flow sends `R` to `Y`, and the distinguished background is exactly
the unconsumed `Y` row.

The small character alone cancels when the unqueried `R` bit is summed out.
The small-plus-background character is instead the `Y` bit, so both allowed
`R` values contribute positively to the unchanged original outcome event.
Full cells conflicting with the forced `A` value still contribute zero.

Only this three-node fixture and its sixty-four actual pair-root vectors
are evaluated.  The symbolic phase and full-term theorems below do not
evaluate a general latent support or assert universal completeness.
-/

private def signature : ObservedSignature where
  count := 3
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := fun _ => by decide
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 1) ∨ (parent.val = 1 ∧ child.val = 2))
  directed_earlier := by
    intro parent child selected
    have edge := of_decide_eq_true selected
    omega

private def graph : ObservedGraph signature where
  bidirected := fun left right => decide
    ((left.val = 0 ∧ right.val = 1) ∨ (left.val = 1 ∧ right.val = 0))
  bidirected_symmetric := by
    intro left right selected
    apply decide_eq_true
    rcases of_decide_eq_true selected with ⟨first, second⟩ | ⟨first, second⟩
    · exact Or.inr ⟨second, first⟩
    · exact Or.inl ⟨second, first⟩
  bidirected_irreflexive := by
    intro node
    apply decide_eq_false
    intro edge
    omega

private def action : Fin signature.count := ⟨0, by decide⟩
private def root : Fin signature.count := ⟨1, by decide⟩
private def outcome : Fin signature.count := ⟨2, by decide⟩
private def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.singleton action
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
private def selection : HedgeSelection signature where
  large := NodeSet.union (NodeSet.singleton action) (NodeSet.singleton root)
  small := NodeSet.singleton root
  child := fun parent => if parent = action then some root else none
private def witness : HedgeWitness graph query := hedgeWitness_of_sets graph query selection (by decide +kernel)
private def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := fun _ => by change false ∈ [false, true]; decide
  second_enumerated := fun _ => by change true ∈ [false, true]; decide
  different := fun _ => Bool.false_ne_true

private def signal := Causality.HedgeChannelInstallation.routingParentSignal witness.smallOutcomeFlowSuccessor
private def mask := Causality.HedgeChannelInstallation.outcomeFlowBackground witness
private def target : Fin signature.count -> Option Bool := fun child => if child = action then some false else none
private def originalEvent := FiniteProduct.falseCylinder signature.count query.outcome
private def choice (background : NodeSet signature) :=
  Causality.HedgeChannelInstallation.fullChoice witness witness.small
    (Causality.HedgeChannelInstallation.smallChannel witness) background
private def projectedTerm (background : NodeSet signature) : Int :=
  ((signature.binary.assignmentEnumeration.filter originalEvent).map
    (fun sample => Causality.HedgeChannelInstallation.rightTermIntegralUnder witness signal signal target sample
      (choice background))).sum

/-- The distinguished background is the actual query outcome, while the
small forest is the unqueried intermediate row.  The flow sends that row
along the genuine directed arrow to the outcome. -/
theorem actual_flow_and_mask :
    mask = NodeSet.singleton outcome ∧
    witness.smallOutcomeFlowSuccessor root = some outcome ∧
    query.outcome root = false ∧ witness.small root = true := by decide +kernel

/-- The general conservation theorem makes the distinguished character
even at every selected original-event sample, including forced conflicts.
Their zero contribution is retained separately in the actual coefficient. -/
theorem original_outcome_phase_even (sample : signature.binary.Assignment)
    (selected : originalEvent sample = true) :
    Bool.xor (Causality.HedgeChannelInstallation.signalPhase witness.small signal sample)
      (Causality.HedgeChannelInstallation.signalPhase mask signal sample) = false :=
  Causality.HedgeChannelInstallation.outcomeFlow_phase_false_of_outcome witness sample selected

/-- Arbitrary routed row selections have nonnegative complete character
projection on the original action/outcome false cylinder.  This is a use of
the symbolic theorem on the signature's own assignment enumeration. -/
theorem original_cylinder_character_nonnegative (nodes : NodeSet signature) :
    0 <= ((signature.binary.assignmentEnumeration.filter
      (FiniteProduct.falseCylinder signature.count (NodeSet.union query.action query.outcome))).map
      (fun sample => FiniteProbRecord.characterSign
        (Causality.HedgeChannelInstallation.signalPhase nodes signal sample))).sum :=
  Causality.HedgeChannelInstallation.routingPhase_characterSum_nonneg
    witness.smallOutcomeFlowNodes nodes witness.smallOutcomeFlowSuccessor
    witness.smallOutcomeFlowSuccessor_wellFormed (NodeSet.union query.action query.outcome)

/-- The exact actual full-small integral retains the forced indicators,
the entire shared-prior mass and the routed original-outcome character. -/
theorem actual_full_term_formula (sample : signature.binary.Assignment) :
    Causality.HedgeChannelInstallation.rightTermIntegralUnder witness signal signal target sample (choice mask) =
      ((PairRootChannels.prior graph.binary 6).den : Int) *
        HedgeChannelTable.choiceCoefficient (Causality.HedgeChannelInstallation.rightTables witness)
          target sample (choice mask) *
        FiniteProbRecord.characterSign
          (Bool.xor (Causality.HedgeChannelInstallation.signalPhase witness.small signal sample)
            (Causality.HedgeChannelInstallation.signalPhase mask signal sample)) :=
  Causality.HedgeChannelInstallation.right_fullTermIntegral_under witness signal signal target sample mask
    (Causality.HedgeChannelInstallation.outcomeFlowBackground_subset_outside witness)

/-- The unqueried small row really is summed out: its bare character
cancels, but the distinguished original-outcome term survives positively. -/
theorem actual_projected_term_values :
    projectedTerm NodeSet.empty = 0 ∧ projectedTerm mask = 4194304 := by decide +kernel

private theorem sum_two (samples : List signature.binary.Assignment)
    (left right : signature.binary.Assignment -> Int) :
    (samples.map (fun sample => left sample + right sample)).sum =
      (samples.map left).sum + (samples.map right).sum := by
  induction samples with
  | nil => rfl
  | cons sample rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, inductionHypothesis]
      ac_rfl

/-- The complete actual original-outcome numerators have the predicted
gap.  The general expansion theorem evaluates the likelihood symbolically;
only the two remaining full-small terms are computed, avoiding a large
kernel reduction of all concrete model probabilities. -/
theorem actual_original_event_difference :
    (HedgeChannelTable.eventNumerator graph 6 (Causality.HedgeChannelInstallation.rightTables witness)
      (Causality.HedgeChannelInstallation.rightSignals witness signal signal) target originalEvent : Int) =
    (HedgeChannelTable.eventNumerator graph 6 (Causality.HedgeChannelInstallation.leftTables witness)
      (Causality.HedgeChannelInstallation.leftSignals witness rich signal signal) target originalEvent : Int) +
      4194304 := by
  letI : DecidableEq (Fin signature.count -> Option (Fin 6)) :=
    FiniteProduct.assignmentDecidableEq signature.count (fun _ => Option (Fin 6)) (fun _ => inferInstance)
  have choices : Causality.HedgeChannelInstallation.rightFullChoicesUnder witness target =
      [choice NodeSet.empty, choice mask] := by decide +kernel
  have difference := Causality.HedgeChannelInstallation.eventNumerators_difference_of_action
    witness rich signal signal target false (by decide +kernel) originalEvent
  rw [choices] at difference
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero] at difference
  rw [sum_two] at difference
  change _ = _ + (projectedTerm NodeSet.empty + projectedTerm mask) at difference
  rw [actual_projected_term_values.1, actual_projected_term_values.2, Int.zero_add] at difference
  exact difference

/-- The general construction separates the original `Y` query in the full
positive model class, despite the hedge's small forest containing only `R`.
No concrete full-model enumeration is needed: this regression instantiates
the unrestricted theorem and its existing original-query kernel adapter. -/
noncomputable def original_positive_counterexample :
    CounterexampleIn (GraphModelClass.positive graph) query :=
  Causality.HedgeChannelInstallation.counterexample witness rich

/-- The same original outcome kernel, not the intermediate root kernel,
is non-identifiable among observationally positive compatible models. -/
theorem original_query_not_identifiable :
    ¬ (GraphModelClass.positive graph).identifiable query :=
  original_positive_counterexample.not_identifiable

/-! ## A declared child conditioner with an omitted small-flow sink -/

private def conditionalQuery : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton root
  action := NodeSet.singleton action
  condition := NodeSet.singleton outcome
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

private def conditionalWitness : HedgeWitness graph conditionalQuery.jointNumerator :=
  hedgeWitness_of_sets graph conditionalQuery.jointNumerator selection (by decide +kernel)

/-- The original `R | do(A), Y` query retains the declared `R -> Y` arrow.
Its numerator flow stops at the queried `R`, and the conditioner omits that
small-flow sink.  These are finite graph facts, not probabilities computed
by enumerating the new refined model's latent prior. -/
theorem conditional_balance_site :
    signature.directed root outcome = true ∧
    conditionalWitness.small root = true ∧
    conditionalWitness.smallOutcomeFlowSuccessor root = none ∧
    conditionalQuery.condition root = false := by decide +kernel

/-- The actual unrestricted channel construction proves the conditioning
marginal equality and separates the original conditional kernel.  A declared
child of the balancing sink is allowed, and no old route-permission premise
or assumed semantic denominator agreement is supplied. -/
noncomputable def conditional_positive_counterexample :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) conditionalQuery :=
  Causality.HedgeChannelInstallation.conditionalCounterexampleOfSmallFlowSink
    conditionalQuery conditionalWitness rich root conditional_balance_site.2.1
    conditional_balance_site.2.2.1 conditional_balance_site.2.2.2

/-- The same full original conditional kernel is non-identifiable in the
positive graph-indexed class, by the two models actually constructed above. -/
theorem conditional_query_not_identifiable :
    ¬ (GraphModelClass.positive graph).conditionalIdentifiable conditionalQuery :=
  conditional_positive_counterexample.not_identifiable

/-- The corrected conditional engine really fails on this original query.
An identified result would contradict its general soundness theorem and the
actual positive counterexample; exhaustion excludes an unfinished result.
We therefore inspect only the abstract result constructors rather than
evaluating the complete exchange search or the installed models.  This
regression asserts failure, not an exact failure forest or a no-exchange
policy for the original query. -/
theorem conditional_engine_failed :
    (match identifyConditionalKernel graph conditionalQuery with
      | .failed _ => true
      | _ => false) = true := by
  cases result : identifyConditionalKernel graph conditionalQuery with
  | failed fail => rfl
  | identified term =>
      exact False.elim (conditional_query_not_identifiable
        (identifyConditionalKernel_identified_identifiable
          (C := GraphModelClass.positive graph) graph.dSeparationCorrectness
          (fun member => member.2) conditionalQuery result))
  | unfinished =>
      exact False.elim (identifyConditionalKernel_ne_unfinished graph conditionalQuery result)

end HedgeChannelRouting
end Examples
end Causality
end Thesis
