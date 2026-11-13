import Thesis.Probability.Distros.ReinforcedAggregation
namespace Thesis.Probability.Distros
open Combinatorics

/-- The parameter vector after observing a count vector. Missing counts
leave the corresponding parameters unchanged. -/
def reinforcedState (increment : Nat) : List Nat → List Nat → List Nat
  | [], _ => []
  | alphas, [] => alphas
  | alpha :: alphas, count :: counts => (alpha + increment * count) :: reinforcedState increment alphas counts

def reinforcedUpdate : List Nat → Nat → List Nat → List Nat
  | alphas, _, [] => alphas
  | alphas, increment, colour :: history =>
      reinforcedUpdate (alphas.modify colour (fun a => a + increment)) increment history

theorem reinforcedState_length (increment : Nat) (alphas counts : List Nat) :
    (reinforcedState increment alphas counts).length = alphas.length := by
  induction alphas generalizing counts with
  | nil => rfl
  | cons alpha alphas ih => cases counts <;> simp only [reinforcedState, List.length_cons, ih]

theorem reinforcedState_modify_alpha (increment : Nat) (alphas counts : List Nat) (i : Nat) :
    reinforcedState increment (alphas.modify i (fun a => a + increment)) counts =
      (reinforcedState increment alphas counts).modify i (fun a => a + increment) := by
  induction alphas generalizing counts i with
  | nil => simp only [List.modify_nil, reinforcedState]
  | cons alpha alphas ih =>
      cases counts with
      | nil => cases i <;> simp only [List.modify_zero_cons, List.modify_succ_cons, reinforcedState]
      | cons count counts => cases i with
          | zero => simp only [reinforcedState, List.modify_zero_cons]; congr 1; omega
          | succ i => simp only [reinforcedState, List.modify_succ_cons, ih]

theorem reinforcedState_modify_count (increment : Nat) (alphas counts : List Nat)
    (dimension : counts.length = alphas.length) (i : Nat) :
    reinforcedState increment alphas (counts.modify i (fun c => c + 1)) =
      (reinforcedState increment alphas counts).modify i (fun a => a + increment) := by
  induction alphas generalizing counts i with
  | nil => simp only [reinforcedState, List.modify_nil]
  | cons alpha alphas ih => cases counts with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons count counts => cases i with
          | zero => simp only [reinforcedState, List.modify_zero_cons, Nat.mul_add, Nat.mul_one]; congr 1; omega
          | succ i => simp only [reinforcedState, List.modify_succ_cons, ih counts (Nat.succ.inj dimension)]

theorem reinforcedState_zero (increment : Nat) (alphas : List Nat) :
    reinforcedState increment alphas (List.replicate alphas.length 0) = alphas := by
  induction alphas with
  | nil => rfl
  | cons alpha alphas ih => simp only [List.length_cons, List.replicate_succ, reinforcedState, Nat.mul_zero, Nat.add_zero, ih]

/-- The parameter update depends only on the observed counts. -/
theorem reinforcedUpdate_counts (alphas : List Nat) (increment : Nat) (history : List Nat) :
    reinforcedUpdate alphas increment history = reinforcedState increment alphas (colourCounts alphas.length history) := by
  induction history generalizing alphas with
  | nil => exact (reinforcedState_zero increment alphas).symm
  | cons colour history ih =>
      simp only [reinforcedUpdate, ih, List.length_modify, colourCounts]
      rw [reinforcedState_modify_alpha, reinforcedState_modify_count _ _ _ (colourCounts_length _ _)]

theorem reinforcedState_sum (increment : Nat) (alphas counts : List Nat) (dimension : counts.length = alphas.length) :
    (reinforcedState increment alphas counts).sum = alphas.sum + increment * counts.sum := by
  induction alphas generalizing counts with
  | nil => cases counts with
      | nil => simp only [reinforcedState, List.sum_nil, Nat.mul_zero, Nat.add_zero]
      | cons count counts => simp only [List.length_cons, List.length_nil] at dimension; omega
  | cons alpha alphas ih => cases counts with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons count counts => simp only [reinforcedState, List.sum_cons, ih counts (Nat.succ.inj dimension), Nat.mul_add]; omega

theorem reinforcedState_getD (increment : Nat) (alphas counts : List Nat) (dimension : counts.length = alphas.length)
    (i : Nat) (within : i < alphas.length) :
    (reinforcedState increment alphas counts).getD i 0 = alphas.getD i 0 + increment * counts.getD i 0 := by
  induction alphas generalizing counts i with
  | nil => simp only [List.length_nil] at within; omega
  | cons alpha alphas ih => cases counts with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons count counts => cases i with
          | zero => rfl
          | succ i => exact ih counts (Nat.succ.inj dimension) i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)

theorem reinforcedUpdate_length (alphas : List Nat) (increment : Nat) (history : List Nat) :
    (reinforcedUpdate alphas increment history).length = alphas.length := by
  rw [reinforcedUpdate_counts, reinforcedState_length]

theorem reinforcedUpdate_positive (alphas : List Nat) (increment : Nat) (history : List Nat) (positive : 0 < alphas.sum) :
    0 < (reinforcedUpdate alphas increment history).sum := by
  rw [reinforcedUpdate_counts, reinforcedState_sum _ _ _ (colourCounts_length _ _)]
  omega

/-- Splitting the actual sequential atom list at any fixed time. -/
theorem reinforcedUrnAtoms_append (m n : Nat) (alphas : List Nat) (increment : Nat) :
    reinforcedUrnAtoms (m + n) alphas increment =
      (reinforcedUrnAtoms m alphas increment).flatMap (fun front =>
        (reinforcedUrnAtoms n (reinforcedUpdate alphas increment front.1) increment).map
          (fun back => (front.1 ++ back.1, front.2 * back.2))) := by
  induction m generalizing alphas with
  | zero => simp only [Nat.zero_add, reinforcedUrnAtoms, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, reinforcedUpdate, List.nil_append, Nat.one_mul]; exact (List.map_id' _).symm
  | succ m ih =>
      have index : m + 1 + n = (m + n) + 1 := by omega
      rw [index, reinforcedUrnAtoms]
      simp only [ih, reinforcedUrnAtoms, List.flatMap_assoc, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
        reinforcedUpdate, List.cons_append, Nat.mul_assoc]

end Thesis.Probability.Distros
