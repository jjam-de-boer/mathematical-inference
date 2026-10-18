import Thesis.Probability.Distros.HighestFactorialMoments
import Thesis.Probability.Distros.DepletingPrefix

namespace Thesis.Probability.Distros
open Combinatorics

/-- Every coordinatewise feasible count vector has a positive falling kernel,
including the empty vector and zero-stock coordinates with zero counts. -/
theorem jointFalling_pos_of_within (counts stocks : List Nat)
    (within : depletingCountsWithin counts stocks) : 0 < jointFalling counts stocks := by
  induction counts generalizing stocks with
  | nil => cases stocks with
      | nil => exact Nat.zero_lt_one
      | cons stock stocks => exact False.elim within
  | cons count counts ih => cases stocks with
      | nil => exact False.elim within
      | cons stock stocks =>
          exact Nat.mul_pos (fallingFactorial_pos stock count within.1) (ih stocks within.2)

/-- Recursive stock availability is exactly equal dimension and the familiar
coordinate bounds, with no positivity requirement on an individual stock. -/
theorem depletingCountsWithin_iff_coordinates (counts stocks : List Nat) :
    depletingCountsWithin counts stocks ↔ counts.length = stocks.length ∧
      ∀ index, index < stocks.length → counts.getD index 0 ≤ stocks.getD index 0 := by
  induction counts generalizing stocks with
  | nil => cases stocks with
      | nil => simp [depletingCountsWithin]
      | cons stock stocks => simp [depletingCountsWithin]
  | cons count counts ih => cases stocks with
      | nil => simp [depletingCountsWithin]
      | cons stock stocks =>
          constructor
          · intro within
            have tail := (ih stocks).mp within.2
            refine ⟨by simp only [List.length_cons, tail.1], ?_⟩
            intro index bound
            cases index with
            | zero => exact within.1
            | succ index =>
                exact tail.2 index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using bound)
          · intro data
            refine ⟨data.2 0 (by simp only [List.length_cons]; omega), (ih stocks).mpr ⟨Nat.succ.inj data.1, ?_⟩⟩
            intro index bound
            exact data.2 (index + 1) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using bound)

/-- Counts have positive probability exactly when they have the right shape,
total and coordinatewise stock availability. No supportedness oracle is needed. -/
theorem depletingCountsSupported_iff (m : Nat) (stocks counts : List Nat) :
    depletingCountsSupported m stocks counts ↔ counts.length = stocks.length ∧
      counts.sum = m ∧ depletingCountsWithin counts stocks := by
  constructor
  · exact depletingCountsSupported_data m stocks counts
  · rintro ⟨dimension, total, bounded⟩
    have within : m ≤ stocks.sum := by
      have upper := depletingCountsWithin_sum_le counts stocks bounded
      omega
    let μ := multicolourDepletingDistro m stocks within
    let ν := multivariateHypergeometricDistro m stocks (binom_pos_of_le _ _ within)
    have formula := multivariateHypergeometric_pmf_highestOrder m stocks counts
      (binom_pos_of_le _ _ within) dimension total
    have kernel := jointFalling_pos_of_within counts stocks bounded
    have positive : 0 < (ν.pmf counts).num := (QProb.equiv_num_pos_iff formula).mpr (by
      change 0 < (fallingFactorial m m * jointFalling counts stocks) * 1
      exact Nat.mul_pos (Nat.mul_pos (fallingFactorial_pos m m (Nat.le_refl _)) kernel) Nat.zero_lt_one)
    have mapped := μ.map_probVal (colourCounts stocks.length) (FiniteProbRecord.singletonEvent counts)
    have law := multicolourDepleting_hypergeometric m stocks within (FiniteProbRecord.singletonEvent counts)
    have same := QProb.equiv_trans (QProb.equiv_symm mapped) law
    exact (QProb.equiv_num_pos_iff same).mpr positive

/-- Explicit, indexed support conditions suitable for public conditioning APIs. -/
theorem depletingCountsSupported_iff_coordinates (m : Nat) (stocks counts : List Nat) :
    depletingCountsSupported m stocks counts ↔ counts.length = stocks.length ∧ counts.sum = m ∧
      ∀ index, index < stocks.length → counts.getD index 0 ≤ stocks.getD index 0 := by
  rw [depletingCountsSupported_iff]
  constructor
  · rintro ⟨dimension, total, within⟩
    exact ⟨dimension, total, ((depletingCountsWithin_iff_coordinates counts stocks).mp within).2⟩
  · rintro ⟨dimension, total, bounds⟩
    exact ⟨dimension, total, (depletingCountsWithin_iff_coordinates counts stocks).mpr ⟨dimension, bounds⟩⟩

/-- Out-of-alphabet words have zero probability, at every permitted horizon. -/
theorem multicolourDepleting_pmf_zero_of_invalid (n : Nat) (stocks : List Nat)
    (within : n ≤ stocks.sum) (history : List Nat)
    (invalid : ¬ ∀ colour ∈ history, colour < stocks.length) :
    QProb.Equiv ((multicolourDepletingDistro n stocks within).pmf history) QProb.zero := by
  apply Distro.pmf_zero_of_almostSure_ne
  intro atom member _ same
  apply invalid
  have data := multicolourDepletingAtoms_support n stocks atom member
  simpa only [same] using data.2

/-- The probability of a removal-sampling word is invariant under permutation.
The statement also covers zero-stock and out-of-alphabet words of probability zero. -/
theorem multicolourDepleting_exchangeable (stocks history other : List Nat)
    (within : history.length ≤ stocks.sum) (perm : history.Perm other) :
    QProb.Equiv ((multicolourDepletingDistro history.length stocks within).pmf history)
      ((multicolourDepletingDistro history.length stocks within).pmf other) := by
  by_cases valid : ∀ colour ∈ history, colour < stocks.length
  · have otherValid : ∀ colour ∈ other, colour < stocks.length :=
      fun colour member => valid colour (perm.mem_iff.mpr member)
    have length : other.length = history.length := perm.length_eq.symm
    have first := multicolourDepleting_word_pmf stocks history valid within
    have second := multicolourDepleting_word_pmf stocks other otherValid
      (by simpa only [length] using within)
    have second' : QProb.Equiv ((multicolourDepletingDistro history.length stocks within).pmf other)
        ⟨jointFalling (colourCounts stocks.length other) stocks, fallingFactorial stocks.sum history.length,
          fallingFactorial_pos _ _ within⟩ := by simpa only [length] using second
    rw [colourCounts_perm stocks.length perm] at first
    exact QProb.equiv_trans first (QProb.equiv_symm second')
  · have otherInvalid : ¬ ∀ colour ∈ other, colour < stocks.length :=
      fun otherValid => valid (fun colour member => otherValid colour (perm.mem_iff.mp member))
    exact QProb.equiv_trans (multicolourDepleting_pmf_zero_of_invalid _ stocks within history valid)
      (QProb.equiv_symm (multicolourDepleting_pmf_zero_of_invalid _ stocks within other otherInvalid))

/-- Condition the actual path record using explicit shape, total and stock bounds.
Zero-stock categories remain present in the resulting future path law. -/
def depletingCountsContinuationOfBounds (m n : Nat) (stocks counts : List Nat)
    (within : m + n ≤ stocks.sum) (dimension : counts.length = stocks.length) (total : counts.sum = m)
    (bounds : ∀ index, index < stocks.length → counts.getD index 0 ≤ stocks.getD index 0) : Distro (List Nat) :=
  depletingCountsContinuation m n stocks counts within
    ((depletingCountsSupported_iff_coordinates m stocks counts).mpr ⟨dimension, total, bounds⟩)

theorem depletingCountsContinuationOfBounds_updated (m n : Nat) (stocks counts : List Nat)
    (within : m + n ≤ stocks.sum) (dimension : counts.length = stocks.length) (total : counts.sum = m)
    (bounds : ∀ index, index < stocks.length → counts.getD index 0 ≤ stocks.getD index 0) :
    (depletingCountsContinuationOfBounds m n stocks counts within dimension total bounds).SameLaw
      (multicolourDepletingDistro n (depletingState stocks counts)
        (depletingCounts_remaining m n stocks counts within
          ((depletingCountsSupported_iff_coordinates m stocks counts).mpr ⟨dimension, total, bounds⟩))) :=
  depletingCountsContinuation_updated m n stocks counts within _

/-- The next-colour formula accepts only explicit feasible-count conditions. -/
theorem depleting_next_after_counts_of_bounds (m : Nat) (stocks counts : List Nat)
    (within : m + 1 ≤ stocks.sum) (dimension : counts.length = stocks.length) (total : counts.sum = m)
    (bounds : ∀ index, index < stocks.length → counts.getD index 0 ≤ stocks.getD index 0)
    (index : Nat) (valid : index < stocks.length) :
    QProb.Equiv ((depletingCountsContinuationOfBounds m 1 stocks counts within dimension total bounds).pmf [index])
      ⟨stocks.getD index 0 - counts.getD index 0, stocks.sum - m, by omega⟩ :=
  depleting_next_after_counts m stocks counts within _ index valid

end Thesis.Probability.Distros
