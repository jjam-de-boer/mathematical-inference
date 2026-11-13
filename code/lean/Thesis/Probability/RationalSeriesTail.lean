import Thesis.Probability.RationalGeometricSeries

namespace Thesis.Probability.RationalCauchySequence

/-- Termwise rational equivalence gives equal completed values even when the
two explicitly supplied Cauchy moduli differ. -/
theorem limit_congr (first second : RationalCauchySequence) (same : ∀ n, SignedRatio.Equiv (first.value n) (second.value n)) :
    ConstructiveReal.Equiv first.limit second.limit :=
  ConstructiveReal.equiv_trans (ConstructiveReal.equiv_symm first.toReal_limit)
    (ConstructiveReal.equiv_trans (RealCauchySequence.limit_congr first.toReal second.toReal
      (fun n => (ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr (same n))) second.toReal_limit)

end Thesis.Probability.RationalCauchySequence

namespace Thesis.Probability.RationalGeometricSeries
open SignedRatio

theorem block_congr (first second : Nat → SignedRatio) (same : ∀ n, Equiv (first n) (second n)) (start count : Nat) :
    Equiv (block first start count) (block second start count) := by
  induction count generalizing start with
  | zero => exact equiv_refl _
  | succ count ih => exact add_congr (same start) (ih (start + 1))

theorem block_shift (terms : Nat → SignedRatio) (offset start count : Nat) :
    Equiv (block (fun n => terms (offset + n)) start count) (block terms (offset + start) count) := by
  induction count generalizing start with
  | zero => exact equiv_refl _
  | succ count ih => simpa only [block, Nat.add_assoc] using add_congr (equiv_refl (terms (offset + start))) (ih (start + 1))

/-- Geometric domination may start after a finite prefix. -/
theorem partial_error_after (terms : Nat → SignedRatio) (offset coefficient : Nat)
    (bounded : ∀ n, QProb.LE (terms (offset + n)).magnitude (envelope coefficient n))
    (first second : Nat) (after : offset ≤ first) (ordered : first ≤ second) :
    QProb.LE (sub (partialSum terms second) (partialSum terms first)).magnitude (envelope (2 * coefficient) (first - offset)) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le ordered
  have shifted := block_shift terms offset (first - offset) count
  rw [show offset + (first - offset) = first by omega] at shifted
  have same := equiv_trans (partial_difference terms first count) (equiv_symm shifted)
  exact QProb.le_congr (QProb.equiv_symm (magnitude_congr same)) (QProb.equiv_refl _)
    (block_bound (fun n => terms (offset + n)) coefficient bounded (first - offset) count)

/-- An eventually dyadically dominated signed series has an explicit
Cauchy modulus including its finite prefix. -/
def eventualSequence (terms : Nat → SignedRatio) (offset coefficient : Nat)
    (bounded : ∀ n, QProb.LE (terms (offset + n)).magnitude (envelope coefficient n)) : RationalCauchySequence where
  value := partialSum terms
  modulus precision := offset + ((2 * coefficient * precision.den).log2 + 1)
  cauchy precision n m left right := by
    by_cases ordered : n ≤ m
    · have errors := QProb.le_trans (partial_error_after terms offset coefficient bounded n m (by omega) ordered)
        (envelope_small coefficient precision (n - offset) (by omega))
      exact ((magnitude_sub_le_iff _ _ _).mp errors).2
    · have reversed : m ≤ n := (Nat.le_total n m).resolve_left ordered
      have errors := QProb.le_trans (partial_error_after terms offset coefficient bounded m n (by omega) reversed)
        (envelope_small coefficient precision (m - offset) (by omega))
      exact ((magnitude_sub_le_iff _ _ _).mp errors).1

/-- Every truncation after the finite prefix has a certified remainder. -/
theorem eventual_remainder (terms : Nat → SignedRatio) (offset coefficient : Nat)
    (bounded : ∀ n, QProb.LE (terms (offset + n)).magnitude (envelope coefficient n)) (n : Nat) (after : offset ≤ n) :
    ConstructiveReal.Within (envelope (2 * coefficient) (n - offset)) (ConstructiveReal.ofSignedRatio (partialSum terms n))
      (eventualSequence terms offset coefficient bounded).limit := by
  let sums := eventualSequence terms offset coefficient bounded
  have tails : ∀ m, n ≤ m → ConstructiveReal.Within (envelope (2 * coefficient) (n - offset))
      (ConstructiveReal.ofSignedRatio (partialSum terms n)) (sums.toReal.value m) := by
    intro m later
    apply (ConstructiveReal.within_ofSignedRatio_iff _ _ _).mpr
    exact QProb.le_congr (magnitude_sub_symm _ _) (QProb.equiv_refl _)
      (partial_error_after terms offset coefficient bounded n m after later)
  have limits := RealCauchySequence.limit_within_of_tail (RealCauchySequence.constant (ConstructiveReal.ofSignedRatio (partialSum terms n)))
    sums.toReal (envelope (2 * coefficient) (n - offset)) n tails
  exact (ConstructiveReal.within_congr (RealCauchySequence.constant_limit _) sums.toReal_limit).mp limits

end Thesis.Probability.RationalGeometricSeries
