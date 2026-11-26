import Thesis.Probability.Distros.DepletingConditioning
import Thesis.Probability.FiniteRecordSums

/-!
Ordered-prefix conditioning and count sufficiency for removal sampling.

The evidence event records the entire observed prefix, and its positive
singleton mass is required before conditioning. Exact path splitting shows
that the future starts from the stocks left by those removals. Forgetting
the prefix order gives the same complete future law as retaining it, since
the remaining state depends only on colour counts. The last theorem reads
the next-colour probability in original stock units and uses a horizon
with at least one ball remaining; an exhausted population has no next draw.
-/

namespace Thesis.Probability.Distros

/-- The complete ordered prefix is genuine evidence on the actual path record. -/
def depletingPrefixEvent (history : List Nat) : Event (List Nat) :=
  fun word => decide (word.take history.length = history)

/-- Support of a specified ordered prefix in the actual experiment of its
own length. A syntactically valid list alone need not have positive mass. -/
def depletingHistorySupported (stocks history : List Nat) : Prop :=
  0 < FiniteProbRecord.eventMass (multicolourDepletingAtoms history.length stocks)
    (FiniteProbRecord.singletonEvent history)

instance (stocks history : List Nat) : Decidable (depletingHistorySupported stocks history) := by
  unfold depletingHistorySupported
  infer_instance

/-- Count-only evidence includes the exact-prefix event, so forgetting
order preserves positive support. -/
theorem depletingHistorySupported_counts (stocks history : List Nat)
    (supported : depletingHistorySupported stocks history) :
    depletingCountsSupported history.length stocks (colourCounts stocks.length history) := by
  have monotone := FiniteProbRecord.eventMass_mono (multicolourDepletingAtoms history.length stocks)
    (FiniteProbRecord.singletonEvent history) (fun word => decide (colourCounts stocks.length word = colourCounts stocks.length history))
    (by intro word selected; have same : word = history := of_decide_eq_true selected; rw [same]; exact decide_eq_true rfl)
  exact Nat.lt_of_lt_of_le supported monotone

theorem depletingHistory_remaining (stocks history : List Nat) (n : Nat)
    (within : history.length + n ≤ stocks.sum) (supported : depletingHistorySupported stocks history) :
    n ≤ (depletingUpdate stocks history).sum := by
  rw [depletingUpdate_counts]
  exact depletingCounts_remaining history.length n stocks (colourCounts stocks.length history) within
    (depletingHistorySupported_counts stocks history supported)

/-- Factor a selected ordered prefix from any suffix event. This equality
of raw masses precedes normalization and does not require positive evidence. -/
theorem depletingPrefixEvent_mass (history : List Nat) (n : Nat) (stocks : List Nat)
    (event : Event (List Nat)) :
    FiniteProbRecord.eventMass (multicolourDepletingAtoms (history.length + n) stocks)
      (fun word => depletingPrefixEvent history word && event (word.drop history.length)) =
      FiniteProbRecord.eventMass (multicolourDepletingAtoms history.length stocks)
        (FiniteProbRecord.singletonEvent history) *
      FiniteProbRecord.eventMass (multicolourDepletingAtoms n (depletingUpdate stocks history)) event := by
  rw [multicolourDepletingAtoms_append, eventMass_flatMap]
  have rows : ((multicolourDepletingAtoms history.length stocks).map (fun front =>
      FiniteProbRecord.eventMass
        ((multicolourDepletingAtoms n (depletingUpdate stocks front.1)).map
          (fun back => (front.1 ++ back.1, front.2 * back.2)))
        (fun word => depletingPrefixEvent history word && event (word.drop history.length)))) =
      (multicolourDepletingAtoms history.length stocks).map (fun front =>
        if FiniteProbRecord.singletonEvent history front.1 then front.2 *
          FiniteProbRecord.eventMass (multicolourDepletingAtoms n (depletingUpdate stocks history)) event else 0) := by
    apply List.map_congr_left
    intro front member
    rw [FiniteProbRecord.eventMass_map_weight]
    have length := (multicolourDepletingAtoms_support history.length stocks front member).1
    have ev : (fun back => depletingPrefixEvent history (front.1 ++ back) &&
        event ((front.1 ++ back).drop history.length)) =
        (fun back => decide (front.1 = history) && event back) := by
      funext back
      simp only [depletingPrefixEvent, ← length, List.take_left, List.drop_left]
    rw [ev]
    by_cases same : front.1 = history
    · simp only [same, decide_true, Bool.true_and, FiniteProbRecord.singletonEvent, if_true]
    · simp only [FiniteProbRecord.singletonEvent, same, decide_false, Bool.false_and, Bool.false_eq_true,
        if_false, FiniteProbRecord.eventMass_false, Nat.mul_zero]
  rw [rows]
  exact FiniteProbRecord.eventMass_factor_sum _ (FiniteProbRecord.singletonEvent history) _


theorem depletingPrefixEvent_positive (history : List Nat) (n : Nat) (stocks : List Nat)
    (within : history.length + n ≤ stocks.sum) (supported : depletingHistorySupported stocks history) :
    (multicolourDepletingDistro (history.length + n) stocks within).record.EventPositive (depletingPrefixEvent history) := by
  have factor := depletingPrefixEvent_mass history n stocks topEvent
  have ev : (fun word => depletingPrefixEvent history word && topEvent (word.drop history.length)) =
      depletingPrefixEvent history := by funext word; exact Bool.and_true _
  rw [ev, FiniteProbRecord.eventMass_top, multicolourDepletingAtoms_totalMass] at factor
  change 0 < FiniteProbRecord.eventMass (multicolourDepletingAtoms (history.length + n) stocks) _
  rw [factor]
  exact Nat.mul_pos supported (fallingFactorial_pos _ _ (depletingHistory_remaining stocks history n within supported))

/-- Condition on supported ordered evidence and retain only the suffix.
The horizon bound and support proof jointly guarantee enough remaining stock. -/
def depletingPrefixContinuation (history : List Nat) (n : Nat) (stocks : List Nat)
    (within : history.length + n ≤ stocks.sum) (supported : depletingHistorySupported stocks history) : Distro (List Nat) :=
  ⟨((multicolourDepletingDistro (history.length + n) stocks within).record.conditionOn
    (depletingPrefixEvent history) (depletingPrefixEvent_positive history n stocks within supported)).map
      (List.drop history.length)⟩

/-- Full ordered-history conditioning removes precisely the observed balls. -/
theorem depletingPrefixContinuation_updated (history : List Nat) (n : Nat) (stocks : List Nat)
    (within : history.length + n ≤ stocks.sum) (supported : depletingHistorySupported stocks history) :
    (depletingPrefixContinuation history n stocks within supported).SameLaw
      (multicolourDepletingDistro n (depletingUpdate stocks history)
        (depletingHistory_remaining stocks history n within supported)) := by
  intro event
  refine QProb.equiv_trans (FiniteProbRecord.map_probVal _ _ event) ?_
  refine QProb.equiv_trans (FiniteProbRecord.conditionOn_probVal _ _ _
    (depletingPrefixEvent_positive history n stocks within supported)) ?_
  have top := depletingPrefixEvent_mass history n stocks topEvent
  have ev : (fun word => depletingPrefixEvent history word && topEvent (word.drop history.length)) =
      depletingPrefixEvent history := by funext word; exact Bool.and_true _
  rw [ev, FiniteProbRecord.eventMass_top, multicolourDepletingAtoms_totalMass] at top
  simp only [FiniteProbRecord.probVal, QProb.Equiv, QProb.div, multicolourDepletingDistro, ofWeightedAtoms]
  rw [depletingPrefixEvent_mass, top]
  simp only [multicolourDepletingAtoms_totalMass]
  ac_rfl

/-- Counts are sufficient for removal paths as well: observing their order
or only their counts gives the same complete future law. -/
theorem depletingPrefix_counts_sufficient (history : List Nat) (n : Nat) (stocks : List Nat)
    (within : history.length + n ≤ stocks.sum) (supported : depletingHistorySupported stocks history) :
    (depletingPrefixContinuation history n stocks within supported).SameLaw
      (depletingCountsContinuation history.length n stocks (colourCounts stocks.length history) within
        (depletingHistorySupported_counts stocks history supported)) := by
  have ordered := depletingPrefixContinuation_updated history n stocks within supported
  simp only [depletingUpdate_counts] at ordered
  exact ordered.trans (depletingCountsContinuation_updated history.length n stocks
    (colourCounts stocks.length history) within (depletingHistorySupported_counts stocks history supported)).symm

/-- The next-draw numerator is the selected remaining stock. The total
remaining stock is positive because the declared horizon includes one further draw. -/
theorem depleting_next_after_prefix (history stocks : List Nat)
    (within : history.length + 1 ≤ stocks.sum) (supported : depletingHistorySupported stocks history)
    (index : Nat) (valid : index < stocks.length) :
    QProb.Equiv ((depletingPrefixContinuation history 1 stocks within supported).pmf [index])
      ⟨stocks.getD index 0 - (colourCounts stocks.length history).getD index 0, stocks.sum - history.length, by omega⟩ :=
  QProb.equiv_trans (depletingPrefix_counts_sufficient history 1 stocks within supported (FiniteProbRecord.singletonEvent [index]))
    (depleting_next_after_counts history.length stocks (colourCounts stocks.length history) within
      (depletingHistorySupported_counts stocks history supported) index valid)

end Thesis.Probability.Distros
