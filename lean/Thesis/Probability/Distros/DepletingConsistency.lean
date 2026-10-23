import Thesis.Probability.Distros.DepletingPrefix
import Thesis.Probability.FiniteRecordSums

namespace Thesis.Probability.Distros

/-- The unnormalized first-block mass factors by the number of possible
ordered suffix samples. Zero-weight, overdrawn prefixes are ignored exactly. -/
theorem multicolourDepletingAtoms_prefix_mass (m n : Nat) (stocks : List Nat) (event : Event (List Nat)) :
    FiniteProbRecord.eventMass (multicolourDepletingAtoms (m + n) stocks) (fun word => event (word.take m)) =
      FiniteProbRecord.eventMass (multicolourDepletingAtoms m stocks) event * fallingFactorial (stocks.sum - m) n := by
  rw [multicolourDepletingAtoms_append, eventMass_flatMap]
  have rows : (multicolourDepletingAtoms m stocks).map (fun front =>
      FiniteProbRecord.eventMass ((multicolourDepletingAtoms n (depletingUpdate stocks front.1)).map
        (fun back => (front.1 ++ back.1, front.2 * back.2))) (fun word => event (word.take m))) =
      (multicolourDepletingAtoms m stocks).map (fun front =>
        if event front.1 then front.2 * fallingFactorial (stocks.sum - m) n else 0) := by
    apply List.map_congr_left
    intro front member
    rw [FiniteProbRecord.eventMass_map_weight]
    have shape := multicolourDepletingAtoms_support m stocks front member
    have ev : (fun back => event ((front.1 ++ back).take m)) = (fun _ => event front.1) := by
      funext back
      simp only [← shape.1, List.take_left]
    rw [ev]
    cases selected : event front.1 with
    | false => simp only [selected, Bool.false_eq_true, if_false, FiniteProbRecord.eventMass_false, Nat.mul_zero]
    | true =>
        simp only [selected, if_true, FiniteProbRecord.eventMass_top, multicolourDepletingAtoms_totalMass]
        by_cases zero : front.2 = 0
        · simp only [zero, Nat.zero_mul]
        · have bounded := jointFalling_positive_within _ stocks
            (multicolourDepletingAtoms_kernel_positive m stocks front member (Nat.pos_of_ne_zero zero))
          have conserved := depletingState_sum stocks (colourCounts stocks.length front.1) bounded
          have total : (colourCounts stocks.length front.1).sum = m := (colourCounts_sum _ _ shape.2).trans shape.1
          have remaining : (depletingUpdate stocks front.1).sum = stocks.sum - m := by
            rw [depletingUpdate_counts]
            rw [total] at conserved
            omega
          change front.2 * FiniteProbRecord.eventMass
            (multicolourDepletingAtoms n (depletingUpdate stocks front.1)) topEvent = _
          rw [FiniteProbRecord.eventMass_top, multicolourDepletingAtoms_totalMass, remaining]
  rw [rows]
  exact FiniteProbRecord.eventMass_factor_sum _ event _

/-- Extending a valid sampling horizon preserves every first-block event. -/
theorem multicolourDepleting_prefix_consistent (m n : Nat) (stocks : List Nat) (within : m + n ≤ stocks.sum) :
    ((multicolourDepletingDistro (m + n) stocks within).map (List.take m)).SameLaw
      (multicolourDepletingDistro m stocks (by omega)) := by
  intro event
  change FiniteProbRecord.eventMass
      ((multicolourDepletingAtoms (m + n) stocks).map (fun atom => (atom.1.take m, atom.2))) event *
      (multicolourDepletingDistro m stocks (by omega)).record.den =
    FiniteProbRecord.eventMass (multicolourDepletingAtoms m stocks) event *
      (multicolourDepletingDistro (m + n) stocks within).record.den
  rw [multicolourDepleting_den, multicolourDepleting_den, FiniteProbRecord.eventMass_map_labels,
    multicolourDepletingAtoms_prefix_mass, fallingFactorial_add]
  ac_rfl

/-- The first count block has its own hypergeometric law, independently
of how many further draws will subsequently be taken. -/
theorem multicolourDepleting_prefix_hypergeometric (m n : Nat) (stocks : List Nat) (within : m + n ≤ stocks.sum) :
    ((multicolourDepletingDistro (m + n) stocks within).map
      (fun word => colourCounts stocks.length (word.take m))).SameLaw
      (multivariateHypergeometricDistro m stocks (binom_pos_of_le _ _ (by omega))) := by
  have first := (multicolourDepleting_prefix_consistent m n stocks within).map (colourCounts stocks.length)
  rw [Distro.map_comp] at first
  exact first.trans (multicolourDepleting_hypergeometric m stocks (by omega))

/-- Successive count blocks use the remaining population. This is a joint
law identity on the actual full sampling record, rather than an assumption
that the two blocks are independent. -/
theorem multicolourDepleting_blocks (m n : Nat) (stocks counts : List Nat)
    (within : m + n ≤ stocks.sum) (supported : depletingCountsSupported m stocks counts)
    (event : Event (List Nat)) :
    QProb.Equiv ((multicolourDepletingDistro (m + n) stocks within).record.probVal (fun word =>
      depletingCountsEvent m stocks.length counts word && event (colourCounts stocks.length (word.drop m))))
      (QProb.mul
        ((multivariateHypergeometricDistro m stocks (binom_pos_of_le _ _ (by omega))).pmf counts)
        ((multivariateHypergeometricDistro n (depletingState stocks counts)
          (binom_pos_of_le _ _ (depletingCounts_remaining m n stocks counts within supported))).record.probVal event)) := by
  let before := multicolourDepletingDistro m stocks (by omega)
  let after := multicolourDepletingDistro n (depletingState stocks counts)
    (depletingCounts_remaining m n stocks counts within supported)
  let countEvent : Event (List Nat) := fun word => decide (colourCounts stocks.length word = counts)
  let futureEvent : Event (List Nat) := fun word => event (colourCounts stocks.length word)
  have data := depletingCountsSupported_data m stocks counts supported
  have conserved := depletingState_sum stocks counts data.2.2
  have remaining : (depletingState stocks counts).sum = stocks.sum - m := by rw [data.2.1] at conserved; omega
  have factor : QProb.Equiv ((multicolourDepletingDistro (m + n) stocks within).record.probVal (fun word =>
      depletingCountsEvent m stocks.length counts word && futureEvent (word.drop m)))
      (QProb.mul (before.record.probVal countEvent) (after.record.probVal futureEvent)) := by
    change FiniteProbRecord.eventMass (multicolourDepletingAtoms (m + n) stocks) _ * (before.record.den * after.record.den) =
      (FiniteProbRecord.eventMass (multicolourDepletingAtoms m stocks) countEvent *
        FiniteProbRecord.eventMass (multicolourDepletingAtoms n (depletingState stocks counts)) futureEvent) *
          (multicolourDepletingDistro (m + n) stocks within).record.den
    rw [depletingCountsEvent_mass]
    dsimp only [before, after]
    rw [multicolourDepleting_den, multicolourDepleting_den, multicolourDepleting_den, remaining, fallingFactorial_add] <;> ac_rfl
  have first := QProb.equiv_trans (QProb.equiv_symm (before.map_probVal (colourCounts stocks.length)
    (FiniteProbRecord.singletonEvent counts)))
    (multicolourDepleting_hypergeometric m stocks (by omega) (FiniteProbRecord.singletonEvent counts))
  have countLaw := multicolourDepleting_hypergeometric n (depletingState stocks counts)
    (depletingCounts_remaining m n stocks counts within supported)
  rw [depletingState_length] at countLaw
  have second := QProb.equiv_trans (QProb.equiv_symm (after.map_probVal (colourCounts stocks.length) event)) (countLaw event)
  exact QProb.equiv_trans factor (QProb.mul_congr first second)

end Thesis.Probability.Distros
