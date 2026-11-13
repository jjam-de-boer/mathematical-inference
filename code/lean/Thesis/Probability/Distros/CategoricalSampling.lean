import Thesis.Probability.Distros.CategoricalProduct
import Thesis.Probability.Distros.Moments

namespace Thesis.Probability.Distros
open Combinatorics

/-!
# Shared finite categorical sampling facts

Counts and selected-head integrals belong below both reinforced and depleting
urn histories. The list-update lemmas describe natural coordinate counts;
none assumes a particular update mechanism or a positive colour weight.
`colourCounts_sum` does require every listed colour to lie in the declared
range: out-of-range list updates deliberately do not create a new coordinate.

Read the coordinate-update identities first, then count conservation and
permutation invariance, and finally the finite selected-head integral.
The original public namespaces, statements and proof bodies are retained.
`MultinomialAggregation`, `CategoricalAggregation` and the original reinforced
modules reexport these results through their ordinary imports.
-/

/-- Updating one existing coordinate adds exactly its increment to the total. -/
theorem sum_modify_add (counts : List Nat) (index increment : Nat) (within : index < counts.length) :
    (counts.modify index (fun old => old + increment)).sum = counts.sum + increment := by
  induction counts generalizing index with
  | nil => simp only [List.length_nil] at within; omega
  | cons count counts ih =>
      cases index with
      | zero => simp only [List.modify_zero_cons, List.sum_cons]; omega
      | succ index =>
          simp only [List.modify_succ_cons, List.sum_cons]
          rw [ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
          omega

/-- A zero increment leaves every coordinate unchanged, even out of range. -/
theorem modify_add_zero (values : List Nat) (index : Nat) : values.modify index (fun x => x + 0) = values := by
  induction values generalizing index with
  | nil => exact List.modify_nil _ _
  | cons value values ih =>
      cases index with
      | zero => simp only [List.modify_zero_cons, Nat.add_zero]
      | succ index => rw [List.modify_succ_cons, ih]

/-- Natural additions at two coordinates commute, including equal indices. -/
theorem modify_add_comm (values : List Nat) (i a j b : Nat) :
    ((values.modify i (fun x => x + a)).modify j (fun x => x + b)) =
      ((values.modify j (fun x => x + b)).modify i (fun x => x + a)) := by
  induction values generalizing i j with
  | nil => simp only [List.modify_nil]
  | cons value values ih =>
      cases i <;> cases j
      · simp only [List.modify_zero_cons]; congr 1; omega
      · simp only [List.modify_zero_cons, List.modify_succ_cons]
      · simp only [List.modify_zero_cons, List.modify_succ_cons]
      · simp only [List.modify_succ_cons, ih]

/-- Every valid word contributes one count per letter, including an empty word. -/
theorem colourCounts_sum (colours : Nat) (word : List Nat)
    (valid : ∀ colour ∈ word, colour < colours) : (colourCounts colours word).sum = word.length := by
  induction word with
  | nil => simp only [colourCounts, List.sum_replicate_nat, Nat.mul_zero, List.length_nil]
  | cons colour word ih =>
      rw [colourCounts, sum_modify_add _ colour 1 (by rw [colourCounts_length]; exact valid colour (List.mem_cons_self ..)),
        ih (fun other member => valid other (List.mem_cons_of_mem _ member)), List.length_cons]

/-- Permuting a word preserves its entire count vector, not only its sum. -/
theorem colourCounts_perm (colours : Nat) {history other : List Nat} (perm : history.Perm other) :
    colourCounts colours history = colourCounts colours other := by
  induction perm with
  | nil => rfl
  | cons head _ ih => simp only [colourCounts, ih]
  | swap a b tail => exact modify_add_comm _ _ _ _ _
  | trans _ _ ih ih' => exact ih.trans ih'

/-- Integrating a selected head of a categorical list. -/
theorem categorical_head_select (alphas : List Nat) (colour : Nat) (f : Nat → Nat)
    (within : colour < alphas.length) :
    natIntegral (finWeighted alphas.length (fun i => alphas.getD i.val 0))
      (fun i => if i.val = colour then f i.val else 0) = alphas.getD colour 0 * f colour := by
  rw [natIntegral_finWeighted alphas.length _ (fun i => if i = colour then f i else 0)]
  have terms : natSum alphas.length (fun i => finWeight (fun j : Fin alphas.length => alphas.getD j.val 0) i *
      (if i = colour then f i else 0)) =
      natSum alphas.length (fun i => (if i = colour then alphas.getD colour 0 else 0) * f i) := by
    apply natSum_congr
    intro i hi
    by_cases same : i = colour
    · subst i; simp only [finWeight, dif_pos within, if_true]
    · simp only [same, if_false, Nat.mul_zero, Nat.zero_mul]
  rw [terms, natSum_spike, if_pos within]

end Thesis.Probability.Distros
