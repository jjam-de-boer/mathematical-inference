import Thesis.Probability.Distros.ReinforcedUpdates
namespace Thesis.Probability.Distros

/-- Observe the complete ordered prefix. -/
def reinforcedPrefixEvent (history : List Nat) : Event (List Nat) :=
  fun word => decide (word.take history.length = history)

def reinforcedHistorySupported (alphas : List Nat) (increment : Nat) (history : List Nat) : Prop :=
  0 < FiniteProbRecord.eventMass (reinforcedUrnAtoms history.length alphas increment)
    (FiniteProbRecord.singletonEvent history)

instance (alphas : List Nat) (increment : Nat) (history : List Nat) :
    Decidable (reinforcedHistorySupported alphas increment history) := by
  unfold reinforcedHistorySupported
  infer_instance

/-- Factor the exact ordered prefix from every future event. -/
theorem reinforcedPrefixEvent_mass (history : List Nat) (n : Nat) (alphas : List Nat) (increment : Nat)
    (event : Event (List Nat)) :
    FiniteProbRecord.eventMass (reinforcedUrnAtoms (history.length + n) alphas increment)
      (fun word => reinforcedPrefixEvent history word && event (word.drop history.length)) =
      FiniteProbRecord.eventMass (reinforcedUrnAtoms history.length alphas increment)
        (FiniteProbRecord.singletonEvent history) *
      FiniteProbRecord.eventMass (reinforcedUrnAtoms n (reinforcedUpdate alphas increment history) increment) event := by
  rw [reinforcedUrnAtoms_append, eventMass_flatMap]
  have rows : ((reinforcedUrnAtoms history.length alphas increment).map (fun front =>
      FiniteProbRecord.eventMass
        ((reinforcedUrnAtoms n (reinforcedUpdate alphas increment front.1) increment).map
          (fun back => (front.1 ++ back.1, front.2 * back.2)))
        (fun word => reinforcedPrefixEvent history word && event (word.drop history.length)))) =
      (reinforcedUrnAtoms history.length alphas increment).map (fun front =>
        if FiniteProbRecord.singletonEvent history front.1 then front.2 *
          FiniteProbRecord.eventMass (reinforcedUrnAtoms n (reinforcedUpdate alphas increment history) increment) event else 0) := by
    apply List.map_congr_left
    intro front member
    rw [FiniteProbRecord.eventMass_map_weight]
    have length := (reinforcedUrn_word_support history.length alphas increment front member).1
    have ev : (fun back => reinforcedPrefixEvent history (front.1 ++ back) &&
        event ((front.1 ++ back).drop history.length)) =
        (fun back => decide (front.1 = history) && event back) := by
      funext back
      simp only [reinforcedPrefixEvent, ← length, List.take_left, List.drop_left]
    rw [ev]
    by_cases same : front.1 = history
    · simp only [same, decide_true, Bool.true_and, FiniteProbRecord.singletonEvent, if_true]
    · simp only [FiniteProbRecord.singletonEvent, same, decide_false, Bool.false_and, Bool.false_eq_true,
        if_false, FiniteProbRecord.eventMass_false, Nat.mul_zero]
  rw [rows]
  exact eventMass_factor_sum _ (FiniteProbRecord.singletonEvent history) _

theorem reinforcedPrefixEvent_positive (history : List Nat) (n : Nat) (alphas : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (supported : reinforcedHistorySupported alphas increment history) :
    (reinforcedUrnDistro (history.length + n) alphas increment positive).record.EventPositive (reinforcedPrefixEvent history) := by
  have factor := reinforcedPrefixEvent_mass history n alphas increment topEvent
  have ev : (fun word => reinforcedPrefixEvent history word && topEvent (word.drop history.length)) =
      reinforcedPrefixEvent history := by funext word; exact Bool.and_true _
  rw [ev, FiniteProbRecord.eventMass_top, totalMass_reinforcedUrnAtoms] at factor
  change 0 < FiniteProbRecord.eventMass (reinforcedUrnAtoms (history.length + n) alphas increment) _
  rw [factor]
  exact Nat.mul_pos supported (stepRising_pos _ _ _ (reinforcedUpdate_positive alphas increment history positive))

/-- The actual conditional suffix after an ordered observed prefix. -/
def reinforcedPrefixContinuation (history : List Nat) (n : Nat) (alphas : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (supported : reinforcedHistorySupported alphas increment history) : Distro (List Nat) :=
  ⟨((reinforcedUrnDistro (history.length + n) alphas increment positive).record.conditionOn
    (reinforcedPrefixEvent history) (reinforcedPrefixEvent_positive history n alphas increment positive supported)).map
      (List.drop history.length)⟩

theorem reinforcedPrefixContinuation_updated (history : List Nat) (n : Nat) (alphas : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (supported : reinforcedHistorySupported alphas increment history) :
    (reinforcedPrefixContinuation history n alphas increment positive supported).SameLaw
      (reinforcedUrnDistro n (reinforcedState increment alphas (colourCounts alphas.length history)) increment
        (by rw [← reinforcedUpdate_counts]; exact reinforcedUpdate_positive alphas increment history positive)) := by
  intro event
  refine QProb.equiv_trans (FiniteProbRecord.map_probVal _ _ event) ?_
  refine QProb.equiv_trans (FiniteProbRecord.conditionOn_probVal _ _ _
    (reinforcedPrefixEvent_positive history n alphas increment positive supported)) ?_
  have top := reinforcedPrefixEvent_mass history n alphas increment topEvent
  have ev : (fun word => reinforcedPrefixEvent history word && topEvent (word.drop history.length)) =
      reinforcedPrefixEvent history := by funext word; exact Bool.and_true _
  rw [ev, FiniteProbRecord.eventMass_top, totalMass_reinforcedUrnAtoms] at top
  simp only [FiniteProbRecord.probVal, QProb.Equiv, QProb.div, reinforcedUrnDistro, ofWeightedAtoms]
  rw [reinforcedPrefixEvent_mass, top]
  simp only [totalMass_reinforcedUrnAtoms, reinforcedUpdate_counts]
  ac_rfl

theorem reinforcedHistorySupported_valid (alphas : List Nat) (increment : Nat) (history : List Nat)
    (supported : reinforcedHistorySupported alphas increment history) :
    ∀ colour ∈ history, colour < alphas.length := by
  rcases eventMass_positive_witness (reinforcedUrnAtoms history.length alphas increment)
    (FiniteProbRecord.singletonEvent history) supported with ⟨atom, member, selected, _⟩
  have same : atom.1 = history := of_decide_eq_true selected
  rw [← same]
  exact (reinforcedUrn_word_support history.length alphas increment atom member).2

theorem reinforced_next_after_prefix (history : List Nat) (alphas : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (supported : reinforcedHistorySupported alphas increment history)
    (i : Nat) (within : i < alphas.length) :
    QProb.Equiv ((reinforcedPrefixContinuation history 1 alphas increment positive supported).pmf [i])
      ⟨alphas.getD i 0 + increment * (colourCounts alphas.length history).getD i 0,
        alphas.sum + increment * history.length, by omega⟩ := by
  have dimension := colourCounts_length alphas.length history
  have total := colourCounts_sum alphas.length history (reinforcedHistorySupported_valid alphas increment history supported)
  refine QProb.equiv_trans (reinforcedPrefixContinuation_updated history 1 alphas increment positive supported
    (FiniteProbRecord.singletonEvent [i])) ?_
  have next := reinforcedUrn_one_colour (reinforcedState increment alphas (colourCounts alphas.length history)) increment
    (by rw [reinforcedState_sum _ _ _ dimension]; omega) i (by rw [reinforcedState_length]; exact within)
  simpa only [reinforcedState_getD _ _ _ dimension i within, reinforcedState_sum _ _ _ dimension, total] using next

theorem reinforcedHistorySupported_counts (alphas : List Nat) (increment : Nat) (history : List Nat)
    (supported : reinforcedHistorySupported alphas increment history) :
    reinforcedCountsSupported history.length alphas increment (colourCounts alphas.length history) := by
  have monotone := FiniteProbRecord.eventMass_mono (reinforcedUrnAtoms history.length alphas increment)
    (FiniteProbRecord.singletonEvent history) (fun word => decide (colourCounts alphas.length word = colourCounts alphas.length history))
    (by intro word selected; have same : word = history := of_decide_eq_true selected; rw [same]; exact decide_eq_true rfl)
  exact Nat.lt_of_lt_of_le supported monotone

/-- Retaining the order of an observed prefix gives exactly the same
future law as retaining only its counts. -/
theorem reinforcedPrefix_counts_sufficient (history : List Nat) (n : Nat) (alphas : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (supported : reinforcedHistorySupported alphas increment history) :
    (reinforcedPrefixContinuation history n alphas increment positive supported).SameLaw
      (reinforcedCountsContinuation history.length n alphas (colourCounts alphas.length history) increment positive
        (colourCounts_length _ _) (reinforcedHistorySupported_counts alphas increment history supported)) := by
  exact (reinforcedPrefixContinuation_updated history n alphas increment positive supported).trans
    (reinforcedCountsContinuation_updated history.length n alphas (colourCounts alphas.length history) increment positive
      (colourCounts_length _ _) (reinforcedHistorySupported_counts alphas increment history supported)).symm

end Thesis.Probability.Distros
