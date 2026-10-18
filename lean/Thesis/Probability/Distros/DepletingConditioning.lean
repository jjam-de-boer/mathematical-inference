import Thesis.Probability.Distros.DepletingWord

namespace Thesis.Probability.Distros

/-- Observed colour counts in the first m actual draws. -/
def depletingCountsEvent (m colours : Nat) (counts : List Nat) : Event (List Nat) :=
  fun word => decide (colourCounts colours (word.take m) = counts)

def depletingCountsSupported (m : Nat) (stocks counts : List Nat) : Prop :=
  0 < FiniteProbRecord.eventMass (multicolourDepletingAtoms m stocks)
    (fun word => decide (colourCounts stocks.length word = counts))

instance (m : Nat) (stocks counts : List Nat) : Decidable (depletingCountsSupported m stocks counts) := by
  unfold depletingCountsSupported
  infer_instance

/-- Actual positive evidence supplies dimension, total draws, and every
coordinate stock bound. No impossible observation is conditioned on. -/
theorem depletingCountsSupported_data (m : Nat) (stocks counts : List Nat)
    (supported : depletingCountsSupported m stocks counts) :
    counts.length = stocks.length ∧ counts.sum = m ∧ depletingCountsWithin counts stocks := by
  rcases eventMass_positive_witness (multicolourDepletingAtoms m stocks)
    (fun word => decide (colourCounts stocks.length word = counts)) supported with ⟨atom, member, selected, weight⟩
  have same : colourCounts stocks.length atom.1 = counts := of_decide_eq_true selected
  have shape := multicolourDepletingAtoms_support m stocks atom member
  have bounded := jointFalling_positive_within _ stocks (multicolourDepletingAtoms_kernel_positive m stocks atom member weight)
  rw [← same]
  exact ⟨colourCounts_length _ _, (colourCounts_sum _ _ shape.2).trans shape.1, bounded⟩

theorem depletingCounts_remaining (m n : Nat) (stocks counts : List Nat)
    (within : m + n ≤ stocks.sum) (supported : depletingCountsSupported m stocks counts) :
    n ≤ (depletingState stocks counts).sum := by
  have data := depletingCountsSupported_data m stocks counts supported
  have conserved := depletingState_sum stocks counts data.2.2
  rw [data.2.1] at conserved
  omega

theorem depletingCountsEvent_mass (m n : Nat) (stocks counts : List Nat)
    (event : Event (List Nat)) :
    FiniteProbRecord.eventMass (multicolourDepletingAtoms (m + n) stocks)
      (fun word => depletingCountsEvent m stocks.length counts word && event (word.drop m)) =
      FiniteProbRecord.eventMass (multicolourDepletingAtoms m stocks)
        (fun word => decide (colourCounts stocks.length word = counts)) *
      FiniteProbRecord.eventMass (multicolourDepletingAtoms n (depletingState stocks counts)) event := by
  rw [multicolourDepletingAtoms_append, eventMass_flatMap]
  have rows : ((multicolourDepletingAtoms m stocks).map (fun front =>
      FiniteProbRecord.eventMass
        ((multicolourDepletingAtoms n (depletingUpdate stocks front.1)).map
          (fun back => (front.1 ++ back.1, front.2 * back.2)))
        (fun word => depletingCountsEvent m stocks.length counts word && event (word.drop m)))) =
      (multicolourDepletingAtoms m stocks).map (fun front =>
        if decide (colourCounts stocks.length front.1 = counts) then front.2 *
          FiniteProbRecord.eventMass (multicolourDepletingAtoms n (depletingState stocks counts)) event else 0) := by
    apply List.map_congr_left
    intro front member
    rw [FiniteProbRecord.eventMass_map_weight]
    have length := (multicolourDepletingAtoms_support m stocks front member).1
    have ev : (fun back => depletingCountsEvent m stocks.length counts (front.1 ++ back) &&
        event ((front.1 ++ back).drop m)) =
        (fun back => decide (colourCounts stocks.length front.1 = counts) && event back) := by
      funext back
      simp only [depletingCountsEvent, ← length, List.take_left, List.drop_left]
    rw [ev]
    by_cases same : colourCounts stocks.length front.1 = counts
    · simp only [same, decide_true, Bool.true_and, if_true]
      rw [depletingUpdate_counts, same]
    · simp only [same, decide_false, Bool.false_and, Bool.false_eq_true, if_false, FiniteProbRecord.eventMass_false, Nat.mul_zero]
  rw [rows]
  exact eventMass_factor_sum (multicolourDepletingAtoms m stocks)
    (fun word => decide (colourCounts stocks.length word = counts)) _


theorem depletingCountsEvent_positive (m n : Nat) (stocks counts : List Nat)
    (within : m + n ≤ stocks.sum) (supported : depletingCountsSupported m stocks counts) :
    (multicolourDepletingDistro (m + n) stocks within).record.EventPositive
      (depletingCountsEvent m stocks.length counts) := by
  have factor := depletingCountsEvent_mass m n stocks counts topEvent
  have event : (fun word => depletingCountsEvent m stocks.length counts word && topEvent (word.drop m)) =
      depletingCountsEvent m stocks.length counts := by funext word; exact Bool.and_true _
  rw [event, FiniteProbRecord.eventMass_top, multicolourDepletingAtoms_totalMass] at factor
  change 0 < FiniteProbRecord.eventMass (multicolourDepletingAtoms (m + n) stocks) _
  rw [factor]
  exact Nat.mul_pos supported (fallingFactorial_pos _ _ (depletingCounts_remaining m n stocks counts within supported))

/-- The future of the actual conditioned path record. -/
def depletingCountsContinuation (m n : Nat) (stocks counts : List Nat)
    (within : m + n ≤ stocks.sum) (supported : depletingCountsSupported m stocks counts) : Distro (List Nat) :=
  ⟨((multicolourDepletingDistro (m + n) stocks within).record.conditionOn
    (depletingCountsEvent m stocks.length counts) (depletingCountsEvent_positive m n stocks counts within supported)).map (List.drop m)⟩

/-- Conditioning on supported counts gives the complete future path law
from the remaining stocks. All future Boolean events are covered. -/
theorem depletingCountsContinuation_updated (m n : Nat) (stocks counts : List Nat)
    (within : m + n ≤ stocks.sum) (supported : depletingCountsSupported m stocks counts) :
    (depletingCountsContinuation m n stocks counts within supported).SameLaw
      (multicolourDepletingDistro n (depletingState stocks counts)
        (depletingCounts_remaining m n stocks counts within supported)) := by
  intro event
  refine QProb.equiv_trans (FiniteProbRecord.map_probVal _ _ event) ?_
  refine QProb.equiv_trans (FiniteProbRecord.conditionOn_probVal _ _ _
    (depletingCountsEvent_positive m n stocks counts within supported)) ?_
  have top := depletingCountsEvent_mass m n stocks counts topEvent
  have ev : (fun word => depletingCountsEvent m stocks.length counts word && topEvent (word.drop m)) =
      depletingCountsEvent m stocks.length counts := by funext word; exact Bool.and_true _
  rw [ev, FiniteProbRecord.eventMass_top, multicolourDepletingAtoms_totalMass] at top
  simp only [FiniteProbRecord.probVal, QProb.Equiv, QProb.div, multicolourDepletingDistro, ofWeightedAtoms]
  rw [depletingCountsEvent_mass, top]
  simp only [multicolourDepletingAtoms_totalMass]
  ac_rfl

/-- Each subsequent count block is hypergeometric in the remaining population. -/
theorem depletingCountsContinuation_hypergeometric (m n : Nat) (stocks counts : List Nat)
    (within : m + n ≤ stocks.sum) (supported : depletingCountsSupported m stocks counts) :
    ((depletingCountsContinuation m n stocks counts within supported).map (colourCounts stocks.length)).SameLaw
      (multivariateHypergeometricDistro n (depletingState stocks counts)
        (binom_pos_of_le _ _ (depletingCounts_remaining m n stocks counts within supported))) := by
  have paths := (depletingCountsContinuation_updated m n stocks counts within supported).map (colourCounts stocks.length)
  have counts := multicolourDepleting_hypergeometric n (depletingState stocks counts)
    (depletingCounts_remaining m n stocks counts within supported)
  rw [depletingState_length] at counts
  exact paths.trans counts

/-- Conditional next-draw probability in the original stock units. -/
theorem depleting_next_after_counts (m : Nat) (stocks counts : List Nat)
    (within : m + 1 ≤ stocks.sum) (supported : depletingCountsSupported m stocks counts)
    (index : Nat) (valid : index < stocks.length) :
    QProb.Equiv ((depletingCountsContinuation m 1 stocks counts within supported).pmf [index])
      ⟨stocks.getD index 0 - counts.getD index 0, stocks.sum - m, by omega⟩ := by
  have data := depletingCountsSupported_data m stocks counts supported
  have conserved := depletingState_sum stocks counts data.2.2
  have remaining : (depletingState stocks counts).sum = stocks.sum - m := by rw [data.2.1] at conserved; omega
  refine QProb.equiv_trans (depletingCountsContinuation_updated m 1 stocks counts within supported
    (FiniteProbRecord.singletonEvent [index])) ?_
  have next := multicolourDepleting_one_colour (depletingState stocks counts) (by rw [remaining]; omega)
    index (by rw [depletingState_length]; exact valid)
  simpa only [depletingState_getD, remaining] using next

/-- The conditional next draw is the actual categorical law of the
remaining stocks, retaining zero-stock categories. -/
theorem depleting_next_categorical (m : Nat) (stocks counts : List Nat)
    (within : m + 1 ≤ stocks.sum) (supported : depletingCountsSupported m stocks counts) :
    (depletingCountsContinuation m 1 stocks counts within supported).SameLaw
      ((listCategoricalDistro (depletingState stocks counts)
        (by have bound := depletingCounts_remaining m 1 stocks counts within supported; omega)).map
          (fun colour => [colour.val])) := by
  have future := depletingCountsContinuation_updated m 1 stocks counts within supported
  rw [multicolourDepleting_one_categorical (depletingState stocks counts)
    (by have bound := depletingCounts_remaining m 1 stocks counts within supported; omega)] at future
  exact future

end Thesis.Probability.Distros
