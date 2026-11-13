import Thesis.Probability.Distros.ReinforcedHistory
import Thesis.Probability.Distros.CategoricalSampling
namespace Thesis.Probability.Distros
open Combinatorics

/-- Raw weight of a specified ordered path, including zero for impossible
colours. -/
def reinforcedWordWeight : List Nat → Nat → List Nat → Nat
  | _, _, [] => 1
  | alphas, increment, colour :: history => alphas.getD colour 0 *
      reinforcedWordWeight (alphas.modify colour (fun a => a + increment)) increment history

theorem reinforcedWordWeight_kernel (alphas : List Nat) (increment : Nat) (history : List Nat)
    (valid : ∀ colour ∈ history, colour < alphas.length) :
    reinforcedWordWeight alphas increment history = stepKernel increment alphas (colourCounts alphas.length history) := by
  induction history generalizing alphas with
  | nil => exact (stepKernel_zeros increment alphas).symm
  | cons colour history ih =>
      have hi := valid colour (List.mem_cons_self ..)
      simp only [reinforcedWordWeight, colourCounts]
      rw [stepKernel_increment increment alphas _ (colourCounts_length _ _).symm colour hi, ih]
      · rw [List.length_modify]
      · intro other member
        simpa only [List.length_modify] using valid other (List.mem_cons_of_mem _ member)

theorem reinforcedUrn_word_mass (alphas : List Nat) (increment : Nat) (history : List Nat)
    (valid : ∀ colour ∈ history, colour < alphas.length) :
    FiniteProbRecord.eventMass (reinforcedUrnAtoms history.length alphas increment)
      (FiniteProbRecord.singletonEvent history) = reinforcedWordWeight alphas increment history := by
  induction history generalizing alphas with
  | nil => simp only [reinforcedUrnAtoms, FiniteProbRecord.eventMass,
      FiniteProbRecord.singletonEvent, decide_true, if_true, Nat.add_zero, reinforcedWordWeight]
  | cons colour history ih =>
      rw [List.length_cons, reinforcedUrnAtoms, eventMass_flatMap]
      have rows : ((finWeighted alphas.length (fun i => alphas.getD i.val 0)).map
          (fun head => FiniteProbRecord.eventMass
            ((reinforcedUrnAtoms history.length (alphas.modify head.1.val (fun a => a + increment)) increment).map
              (fun rest => (head.1.val :: rest.1, head.2 * rest.2)))
            (FiniteProbRecord.singletonEvent (colour :: history)))) =
          (finWeighted alphas.length (fun i => alphas.getD i.val 0)).map
            (fun head => head.2 * (if head.1.val = colour then
              FiniteProbRecord.eventMass (reinforcedUrnAtoms history.length
                (alphas.modify head.1.val (fun a => a + increment)) increment)
                (FiniteProbRecord.singletonEvent history) else 0)) := by
        apply List.map_congr_left
        intro head _
        rw [FiniteProbRecord.eventMass_map_weight]
        by_cases same : head.1.val = colour
        · simp only [same, if_true]
          congr 1
          apply FiniteProbRecord.eventMass_congr
          intro rest
          simp only [FiniteProbRecord.singletonEvent, List.cons.injEq, true_and]
        · have ev : (fun rest => FiniteProbRecord.singletonEvent (colour :: history) (head.1.val :: rest)) =
              (fun _ => false) := by
            funext rest
            simp only [FiniteProbRecord.singletonEvent, List.cons.injEq, same, false_and, decide_false]
          rw [ev, FiniteProbRecord.eventMass_false, if_neg same]
      rw [rows, ← natIntegral_eq_sum _ (fun head : Fin alphas.length => if head.val = colour then
        FiniteProbRecord.eventMass (reinforcedUrnAtoms history.length
          (alphas.modify head.val (fun a => a + increment)) increment) (FiniteProbRecord.singletonEvent history) else 0)]
      rw [categorical_head_select alphas colour (fun index => FiniteProbRecord.eventMass
        (reinforcedUrnAtoms history.length (alphas.modify index (fun a => a + increment)) increment)
        (FiniteProbRecord.singletonEvent history)) (valid colour (List.mem_cons_self ..))]
      rw [ih]
      · rfl
      · intro other member
        simpa only [List.length_modify] using valid other (List.mem_cons_of_mem _ member)

/-- The probability of an ordered valid word is its product of coordinate
rising factors divided by the rising total. -/
theorem reinforcedUrn_word_pmf (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum)
    (history : List Nat) (valid : ∀ colour ∈ history, colour < alphas.length) :
    QProb.Equiv ((reinforcedUrnDistro history.length alphas increment positive).pmf history)
      ⟨stepKernel increment alphas (colourCounts alphas.length history), stepRising alphas.sum increment history.length,
        stepRising_pos _ _ _ positive⟩ := by
  change FiniteProbRecord.eventMass (reinforcedUrnAtoms history.length alphas increment)
    (FiniteProbRecord.singletonEvent history) * stepRising alphas.sum increment history.length =
      stepKernel increment alphas (colourCounts alphas.length history) *
        (reinforcedUrnDistro history.length alphas increment positive).record.den
  rw [reinforcedUrn_word_mass alphas increment history valid, reinforcedWordWeight_kernel alphas increment history valid,
    reinforcedUrn_den]

/-- Equal count vectors give equal word probabilities, for arbitrary
reinforcement and any number of colours. -/
theorem reinforcedUrn_exchangeable (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum)
    (history other : List Nat) (length : history.length = other.length)
    (valid : ∀ colour ∈ history, colour < alphas.length) (validOther : ∀ colour ∈ other, colour < alphas.length)
    (counts : colourCounts alphas.length history = colourCounts alphas.length other) :
    QProb.Equiv ((reinforcedUrnDistro history.length alphas increment positive).pmf history)
      ((reinforcedUrnDistro history.length alphas increment positive).pmf other) := by
  have second := reinforcedUrn_word_pmf alphas increment positive other validOther
  rw [← length, ← counts] at second
  exact QProb.equiv_trans (reinforcedUrn_word_pmf alphas increment positive history valid) (QProb.equiv_symm second)

theorem reinforcedUrn_permutation (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum)
    (history other : List Nat) (perm : history.Perm other)
    (valid : ∀ colour ∈ history, colour < alphas.length) :
    QProb.Equiv ((reinforcedUrnDistro history.length alphas increment positive).pmf history)
      ((reinforcedUrnDistro history.length alphas increment positive).pmf other) :=
  reinforcedUrn_exchangeable alphas increment positive history other perm.length_eq valid
    (fun colour member => valid colour (perm.mem_iff.mpr member)) (colourCounts_perm alphas.length perm)

end Thesis.Probability.Distros
