import Thesis.Probability.Distros.OccupancyCovarianceEntries
import Thesis.Probability.Distros.ProbabilityGrid

namespace Thesis.Probability.Distros
open Combinatorics

/-- Coefficients agree as rational values on precisely the positive-weight
colours. Zero-weight categories retain their arbitrary coefficients. -/
def CoefficientsConstantOnPositive (weights : List Nat) (coefficients : Nat → SignedRatio) : Prop :=
  ∃ c : SignedRatio, ∀ i, i < weights.length → 0 < weights.getD i 0 → SignedRatio.Equiv (coefficients i) c

private theorem finWeighted_atom_weight (n : Nat) (weights : Fin n → Nat) (atom : Fin n × Nat)
    (member : atom ∈ finWeighted n weights) : atom.2 = weights atom.1 := by
  induction n with
  | zero => simp only [finWeighted, List.not_mem_nil] at member
  | succ n ih =>
      rw [finWeighted] at member
      rcases List.mem_append.mp member with earlier | last
      · rcases List.mem_map.mp earlier with ⟨old, listed, same⟩
        cases same
        exact ih (fun i => weights i.castSucc) old listed
      · have same := List.mem_singleton.mp last
        cases same
        rfl

theorem reinforcedUrn_one_categorical (weights : List Nat) (increment : Nat) (positive : 0 < weights.sum) :
    reinforcedUrnDistro 1 weights increment positive = (listCategoricalDistro weights positive).map (fun i => [i.val]) := by
  apply Distro.eq_of_atoms
  change reinforcedUrnAtoms 1 weights increment =
    (finWeighted weights.length (fun i => weights.getD i.val 0)).map (fun atom => ([atom.1.val], atom.2))
  simp only [reinforcedUrnAtoms, List.map_cons, List.map_nil, Nat.mul_one]
  exact List.map_eq_flatMap.symm

theorem reinforcedCount_one_categorical (weights : List Nat) (increment : Nat) (positive : 0 < weights.sum) :
    (reinforcedCountDistro 1 weights increment positive).SameLaw
      ((listCategoricalDistro weights positive).map (fun i => colourCounts weights.length [i.val])) := by
  have law := reinforcedUrn_count_correspondence 1 weights increment positive
  rw [reinforcedUrn_one_categorical, Distro.map_comp] at law
  exact law.symm

theorem rationalLinearCombination_one_colour (colours : Nat) (coefficients : Nat → SignedRatio) (index : Nat) (within : index < colours) :
    SignedRatio.Equiv (rationalLinearCombination (List.range colours) coefficients countResponse (colourCounts colours [index]))
      (coefficients index) := by
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem (List.range colours) _
    (fun j => if j = index then coefficients index else SignedRatio.zero) ?_)
    (SignedRatio.listSum_range_select colours index coefficients within)
  intro j member
  have jWithin := List.mem_range.mp member
  have empty : (colourCounts colours []).getD j 0 = 0 := by
    change (List.replicate colours 0).getD j 0 = 0
    rw [← List.getElem_eq_getD (h := by simpa only [List.length_replicate] using jWithin) 0]
    exact List.getElem_replicate (by simpa only [List.length_replicate] using jWithin)
  have coordinate := colourCounts_cons_coordinate colours index j [] jWithin
  rw [empty, Nat.add_zero] at coordinate
  change SignedRatio.Equiv (SignedRatio.mul (coefficients j)
    (QProb.ofNat ((colourCounts colours [index]).getD j 0)).toSignedRatio)
    (if j = index then coefficients index else SignedRatio.zero)
  rw [coordinate]
  by_cases same : j = index
  · subst j
    simp only [colourIndicator, if_true]
    exact SignedRatio.mul_one _
  · simp only [colourIndicator, if_neg same, if_neg (Ne.symm same)]
    exact SignedRatio.mul_zero _

/-- The one-draw covariance form has no other null directions: coefficients
must agree on positive colours, while null categories impose no obligation. -/
theorem reinforcedCount_one_covarianceForm_zero_iff (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Nat → SignedRatio) :
    ((reinforcedCountDistro 1 weights 0 positive).occupancyCovarianceForm weights.length coefficients).num = 0 ↔
      CoefficientsConstantOnPositive weights coefficients := by
  let μ := reinforcedCountDistro 1 weights 0 positive
  let categorical := listCategoricalDistro weights positive
  let response := rationalLinearCombination (List.range weights.length) coefficients countResponse
  have moved := (reinforcedCount_one_categorical weights 0 positive).rationalVariance response
  rw [Distro.rationalVariance_map] at moved
  have equivalent : categorical.AlmostSurely (fun i => SignedRatio.Equiv
      (response (colourCounts weights.length [i.val])) (coefficients i.val)) :=
    fun atom _ _ => rationalLinearCombination_one_colour weights.length coefficients atom.1.val atom.1.isLt
  have categoricalVariance := categorical.rationalCovariance_congr_positive
    (fun i => response (colourCounts weights.length [i.val])) (fun i => coefficients i.val)
    (fun i => response (colourCounts weights.length [i.val])) (fun i => coefficients i.val) equivalent equivalent
  have form := SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.rationalVariance_linearCombination (List.range weights.length) countResponse coefficients))
    (SignedRatio.equiv_trans moved categoricalVariance)
  rw [SignedRatio.equiv_num_zero_iff form, categorical.rationalVariance_zero_iff_constant]
  constructor
  · rintro ⟨c, constant⟩
    refine ⟨c, ?_⟩
    intro i within weight
    exact constant (⟨i, within⟩, weights.getD i 0) (finWeighted_cell_mem _ _ _) weight
  · rintro ⟨c, constant⟩
    refine ⟨c, ?_⟩
    intro atom member weight
    have same := finWeighted_atom_weight weights.length (fun i => weights.getD i.val 0) atom member
    exact constant atom.1.val atom.1.isLt (by rw [← same]; exact weight)

private theorem ratio_mul_num_zero_iff (factor value : SignedRatio) (nonzero : factor.num ≠ 0) :
    (SignedRatio.mul factor value).num = 0 ↔ value.num = 0 := by
  change factor.num * value.num = 0 ↔ value.num = 0
  constructor
  · intro zero
    rcases Int.mul_eq_zero.mp zero with first | second
    · exact False.elim (nonzero first)
    · exact second
  · intro zero
    rw [zero, Int.mul_zero]

private theorem nat_cast_nonzero (value : Nat) (positive : 0 < value) : (value : Int) ≠ 0 :=
  fun zero => Nat.ne_of_gt positive (Int.ofNat_inj.mp zero)

/-- Exact parameter-only null criterion for every natural reinforcement.
Zero trials make every direction null; otherwise exactly the positive-colour
constant coefficients are null. Rational presentations need not be reduced. -/
theorem reinforcedCount_covarianceForm_zero_iff (n increment : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Nat → SignedRatio) :
    ((reinforcedCountDistro n weights increment positive).occupancyCovarianceForm weights.length coefficients).num = 0 ↔
      n = 0 ∨ CoefficientsConstantOnPositive weights coefficients := by
  by_cases zero : n = 0
  · subst n
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact (SignedRatio.equiv_zero_iff _).mp (reinforcedCount_covarianceForm_zero_trials increment weights positive coefficients)
  · have factorPositive : 0 < n * (weights.sum + increment * n) := Nat.mul_pos (Nat.pos_of_ne_zero zero) (by omega)
    have scalar := reinforcedCount_covarianceForm_scaled n increment weights positive coefficients
    have criterion := (SignedRatio.equiv_num_zero_iff scalar).trans
      ((ratio_mul_num_zero_iff _ _ (nat_cast_nonzero _ factorPositive)).trans
        (reinforcedCount_one_covarianceForm_zero_iff weights positive coefficients))
    constructor
    · intro null
      exact Or.inr (criterion.mp null)
    · intro null
      rcases null with impossible | constant
      · exact False.elim (zero impossible)
      · exact criterion.mpr constant

theorem multinomial_covarianceForm_zero_iff (n : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Nat → SignedRatio) :
    ((multinomialDistro n weights positive).occupancyCovarianceForm weights.length coefficients).num = 0 ↔
      n = 0 ∨ CoefficientsConstantOnPositive weights coefficients := by
  simpa only [reinforcedCount_zero] using reinforcedCount_covarianceForm_zero_iff n 0 weights positive coefficients

/-- The full criterion also covers empty and one-ball populations. A proper
nonempty sample has the same null coefficient geometry as one categorical draw. -/
theorem multivariateHypergeometric_covarianceForm_zero_iff (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (coefficients : Nat → SignedRatio) :
    ((multivariateHypergeometricDistro n stocks positive).occupancyCovarianceForm stocks.length coefficients).num = 0 ↔
      n = 0 ∨ n = stocks.sum ∨ CoefficientsConstantOnPositive stocks coefficients := by
  by_cases zero : n = 0
  · subst n
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact (SignedRatio.equiv_zero_iff _).mp (multivariateHypergeometric_covarianceForm_zero_trials stocks positive coefficients)
  · by_cases full : n = stocks.sum
    · subst n
      constructor
      · intro _
        exact Or.inr (Or.inl rfl)
      · intro _
        exact (SignedRatio.equiv_zero_iff _).mp (multivariateHypergeometric_covarianceForm_full_population stocks positive coefficients)
    · have sample := hypergeometric_draws_le_total stocks.sum n positive
      have population : 1 < stocks.sum := by omega
      have factorPositive : 0 < n * (stocks.sum - n) := Nat.mul_pos (by omega) (by omega)
      have scalar := multivariateHypergeometric_covarianceForm_scaled n stocks positive population coefficients
      have criterion := (SignedRatio.equiv_num_zero_iff scalar).trans
        ((ratio_mul_num_zero_iff _ _ (nat_cast_nonzero _ factorPositive)).trans
          (reinforcedCount_one_covarianceForm_zero_iff stocks (by omega) coefficients))
      constructor
      · intro null
        exact Or.inr (Or.inr (criterion.mp null))
      · intro null
        rcases null with impossible | impossible | constant
        · exact False.elim (zero impossible)
        · exact False.elim (full impossible)
        · exact criterion.mpr constant

end Thesis.Probability.Distros
