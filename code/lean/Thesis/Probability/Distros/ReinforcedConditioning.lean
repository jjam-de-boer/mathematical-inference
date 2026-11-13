import Thesis.Probability.Distros.ReinforcedHistory
import Thesis.Probability.FiniteRecordSums
namespace Thesis.Probability.Distros
open Combinatorics

/-- Observe only the colour counts in the first `m` draws. -/
def reinforcedCountsEvent (m colours : Nat) (counts : List Nat) : Event (List Nat) :=
  fun word => decide (colourCounts colours (word.take m) = counts)

def reinforcedCountsSupported (m : Nat) (alphas : List Nat) (increment : Nat) (counts : List Nat) : Prop :=
  0 < FiniteProbRecord.eventMass (reinforcedUrnAtoms m alphas increment)
    (fun word => decide (colourCounts alphas.length word = counts))

instance (m : Nat) (alphas : List Nat) (increment : Nat) (counts : List Nat) :
    Decidable (reinforcedCountsSupported m alphas increment counts) := by
  unfold reinforcedCountsSupported
  infer_instance

/-- Compatibility spelling for the general record-level weighted-sum fact.
Current clients use its foundational owner, which assumes no urn mechanism. -/
theorem eventMass_factor_sum (atoms : List (Ω × Nat)) (evidence : Event Ω) (factor : Nat) :
    (atoms.map (fun atom => if evidence atom.1 then atom.2 * factor else 0)).sum =
      FiniteProbRecord.eventMass atoms evidence * factor :=
  FiniteProbRecord.eventMass_factor_sum atoms evidence factor

/-- Every future event factors through the observed count vector and its
updated urn. This is the finite sufficient-statistic factorization. -/
theorem reinforcedCountsEvent_mass (m n : Nat) (alphas counts : List Nat) (increment : Nat)
    (event : Event (List Nat)) :
    FiniteProbRecord.eventMass (reinforcedUrnAtoms (m + n) alphas increment)
      (fun word => reinforcedCountsEvent m alphas.length counts word && event (word.drop m)) =
      FiniteProbRecord.eventMass (reinforcedUrnAtoms m alphas increment)
        (fun word => decide (colourCounts alphas.length word = counts)) *
      FiniteProbRecord.eventMass (reinforcedUrnAtoms n (reinforcedState increment alphas counts) increment) event := by
  rw [reinforcedUrnAtoms_append, eventMass_flatMap]
  have rows : ((reinforcedUrnAtoms m alphas increment).map (fun front =>
      FiniteProbRecord.eventMass
        ((reinforcedUrnAtoms n (reinforcedUpdate alphas increment front.1) increment).map
          (fun back => (front.1 ++ back.1, front.2 * back.2)))
        (fun word => reinforcedCountsEvent m alphas.length counts word && event (word.drop m)))) =
      (reinforcedUrnAtoms m alphas increment).map (fun front =>
        if decide (colourCounts alphas.length front.1 = counts) then front.2 *
          FiniteProbRecord.eventMass (reinforcedUrnAtoms n (reinforcedState increment alphas counts) increment) event else 0) := by
    apply List.map_congr_left
    intro front member
    rw [FiniteProbRecord.eventMass_map_weight]
    have length := (reinforcedUrn_word_support m alphas increment front member).1
    have ev : (fun back => reinforcedCountsEvent m alphas.length counts (front.1 ++ back) &&
        event ((front.1 ++ back).drop m)) =
        (fun back => decide (colourCounts alphas.length front.1 = counts) && event back) := by
      funext back
      simp only [reinforcedCountsEvent, ← length, List.take_left, List.drop_left]
    rw [ev]
    by_cases same : colourCounts alphas.length front.1 = counts
    · simp only [same, decide_true, Bool.true_and, if_true]
      rw [reinforcedUpdate_counts, same]
    · simp only [same, decide_false, Bool.false_and, Bool.false_eq_true, if_false, FiniteProbRecord.eventMass_false, Nat.mul_zero]
  rw [rows]
  exact FiniteProbRecord.eventMass_factor_sum (reinforcedUrnAtoms m alphas increment)
    (fun word => decide (colourCounts alphas.length word = counts)) _

theorem reinforcedCountsEvent_positive (m n : Nat) (alphas counts : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (dimension : counts.length = alphas.length)
    (supported : reinforcedCountsSupported m alphas increment counts) :
    (reinforcedUrnDistro (m + n) alphas increment positive).record.EventPositive
      (reinforcedCountsEvent m alphas.length counts) := by
  have factor := reinforcedCountsEvent_mass m n alphas counts increment topEvent
  have ev : (fun word => reinforcedCountsEvent m alphas.length counts word && topEvent (word.drop m)) =
      reinforcedCountsEvent m alphas.length counts := by funext word; exact Bool.and_true _
  rw [ev, FiniteProbRecord.eventMass_top, totalMass_reinforcedUrnAtoms] at factor
  change 0 < FiniteProbRecord.eventMass (reinforcedUrnAtoms (m + n) alphas increment) _
  rw [factor]
  apply Nat.mul_pos supported
  apply stepRising_pos
  rw [reinforcedState_sum _ _ _ dimension]
  omega

/-- Condition the actual path law on prefix counts and retain its future. -/
def reinforcedCountsContinuation (m n : Nat) (alphas counts : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (dimension : counts.length = alphas.length)
    (supported : reinforcedCountsSupported m alphas increment counts) : Distro (List Nat) :=
  ⟨((reinforcedUrnDistro (m + n) alphas increment positive).record.conditionOn
    (reinforcedCountsEvent m alphas.length counts)
    (reinforcedCountsEvent_positive m n alphas counts increment positive dimension supported)).map (List.drop m)⟩

/-- Counts are sufficient: forgetting the order of the observed draws
still gives exactly the urn whose parameters are increased by `d * counts`. -/
theorem reinforcedCountsContinuation_updated (m n : Nat) (alphas counts : List Nat) (increment : Nat)
    (positive : 0 < alphas.sum) (dimension : counts.length = alphas.length)
    (supported : reinforcedCountsSupported m alphas increment counts) :
    (reinforcedCountsContinuation m n alphas counts increment positive dimension supported).SameLaw
      (reinforcedUrnDistro n (reinforcedState increment alphas counts) increment
        (by rw [reinforcedState_sum _ _ _ dimension]; omega)) := by
  intro event
  refine QProb.equiv_trans (FiniteProbRecord.map_probVal _ _ event) ?_
  refine QProb.equiv_trans (FiniteProbRecord.conditionOn_probVal _ _ _
    (reinforcedCountsEvent_positive m n alphas counts increment positive dimension supported)) ?_
  have top := reinforcedCountsEvent_mass m n alphas counts increment topEvent
  have ev : (fun word => reinforcedCountsEvent m alphas.length counts word && topEvent (word.drop m)) =
      reinforcedCountsEvent m alphas.length counts := by funext word; exact Bool.and_true _
  rw [ev, FiniteProbRecord.eventMass_top, totalMass_reinforcedUrnAtoms] at top
  simp only [FiniteProbRecord.probVal, QProb.Equiv, QProb.div, reinforcedUrnDistro, ofWeightedAtoms]
  rw [reinforcedCountsEvent_mass, top]
  simp only [totalMass_reinforcedUrnAtoms]
  ac_rfl

end Thesis.Probability.Distros
