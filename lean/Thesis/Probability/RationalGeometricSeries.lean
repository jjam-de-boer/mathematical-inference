import Thesis.Probability.ConstructiveRealCauchyStability

namespace Thesis.Probability.RationalGeometricSeries
open SignedRatio

/-- A finite block of a signed rational series. -/
def block (terms : Nat → SignedRatio) (start : Nat) : Nat → SignedRatio
  | 0 => zero
  | count + 1 => add (terms start) (block terms (start + 1) count)

def partialSum (terms : Nat → SignedRatio) (count : Nat) : SignedRatio := block terms 0 count

/-- Explicit dyadic error bounds, including the zero coefficient. -/
def envelope (coefficient exponent : Nat) : QProb := ⟨coefficient, 2 ^ exponent, Nat.pow_pos (by decide)⟩

theorem block_split (terms : Nat → SignedRatio) (start first second : Nat) :
    Equiv (block terms start (first + second)) (add (block terms start first) (block terms (start + first) second)) := by
  induction first generalizing start with
  | zero => simpa only [Nat.zero_add, Nat.add_zero, block] using equiv_symm (zero_add (block terms start second))
  | succ first ih =>
      simp only [Nat.succ_add, block]
      rw [show start + (first + 1) = (start + 1) + first by omega]
      exact equiv_trans (add_congr (equiv_refl _) (ih (start + 1))) (equiv_symm (add_assoc _ _ _))

/-- A finite tail of dyadically dominated terms is at most twice the first
advertised term bound. There is no sign premise on the terms. -/
theorem block_bound (terms : Nat → SignedRatio) (coefficient : Nat)
    (bounded : ∀ n, QProb.LE (terms n).magnitude (envelope coefficient n)) (start count : Nat) :
    QProb.LE (block terms start count).magnitude (envelope (2 * coefficient) start) := by
  induction count generalizing start with
  | zero => exact QProb.zero_le _
  | succ count ih =>
      have estimate := QProb.le_trans (magnitude_add (terms start) (block terms (start + 1) count))
        (QProb.add_le_add (bounded start) (ih (start + 1)))
      have collect : QProb.Equiv (QProb.add (envelope coefficient start) (envelope (2 * coefficient) (start + 1)))
          (envelope (2 * coefficient) start) := by
        simp only [QProb.Equiv, QProb.add, envelope, Nat.pow_succ, Nat.two_mul, Nat.mul_two, Nat.mul_add, Nat.add_mul]
        ac_rfl
      exact QProb.le_congr (QProb.equiv_refl _) collect estimate

theorem partial_difference (terms : Nat → SignedRatio) (start count : Nat) :
    Equiv (sub (partialSum terms (start + count)) (partialSum terms start)) (block terms start count) := by
  have split := block_split terms 0 start count
  simp only [Nat.zero_add] at split
  have canceled : Equiv (sub (add (partialSum terms start) (block terms start count)) (partialSum terms start)) (block terms start count) :=
    equiv_trans (add_congr (add_comm _ _) (equiv_refl _))
      (equiv_trans (add_assoc _ _ _)
        (equiv_trans (add_congr (equiv_refl _) ((sub_equiv_zero_iff _ _).mpr (equiv_refl _))) (add_zero _)))
  exact equiv_trans (add_congr split (equiv_refl _)) canceled

theorem partial_error_of_le (terms : Nat → SignedRatio) (coefficient : Nat)
    (bounded : ∀ n, QProb.LE (terms n).magnitude (envelope coefficient n)) (first second : Nat) (ordered : first ≤ second) :
    QProb.LE (sub (partialSum terms second) (partialSum terms first)).magnitude (envelope (2 * coefficient) first) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le ordered
  exact QProb.le_congr (QProb.equiv_symm (magnitude_congr (partial_difference terms first count)))
    (QProb.equiv_refl _) (block_bound terms coefficient bounded first count)

/-- The selected dyadic tail bound is at most every requested positive
rational tolerance. The modulus uses a binary logarithm, not an unbounded search. -/
theorem envelope_small (coefficient : Nat) (precision : PositiveRatio) (n : Nat)
    (later : (2 * coefficient * precision.den).log2 + 1 ≤ n) : QProb.LE (envelope (2 * coefficient) n) precision.toQProb := by
  have large : 2 * coefficient * precision.den ≤ 2 ^ n :=
    Nat.le_trans (Nat.le_of_lt Nat.lt_log2_self) (Nat.pow_le_pow_right (by decide) later)
  exact Nat.le_trans large (Nat.le_mul_of_pos_left _ precision.num_pos)

/-- A signed rational series with an explicit dyadic domination certificate
has an effective Cauchy modulus and a computable real limit. -/
def sequence (terms : Nat → SignedRatio) (coefficient : Nat)
    (bounded : ∀ n, QProb.LE (terms n).magnitude (envelope coefficient n)) : RationalCauchySequence where
  value := partialSum terms
  modulus precision := (2 * coefficient * precision.den).log2 + 1
  cauchy precision n m left right := by
    by_cases ordered : n ≤ m
    · have errors := QProb.le_trans (partial_error_of_le terms coefficient bounded n m ordered) (envelope_small coefficient precision n left)
      exact ((magnitude_sub_le_iff _ _ _).mp errors).2
    · have reversed : m ≤ n := (Nat.le_total n m).resolve_left ordered
      have errors := QProb.le_trans (partial_error_of_le terms coefficient bounded m n reversed) (envelope_small coefficient precision m right)
      exact ((magnitude_sub_le_iff _ _ _).mp errors).1

/-- A certified remainder estimate holds at every truncation, independently
of the internal approximation indices chosen by the real completion. -/
theorem remainder (terms : Nat → SignedRatio) (coefficient : Nat)
    (bounded : ∀ n, QProb.LE (terms n).magnitude (envelope coefficient n)) (n : Nat) :
    ConstructiveReal.Within (envelope (2 * coefficient) n) (ConstructiveReal.ofSignedRatio (partialSum terms n))
      (sequence terms coefficient bounded).limit := by
  let sums := sequence terms coefficient bounded
  have tails : ∀ m, n ≤ m → ConstructiveReal.Within (envelope (2 * coefficient) n)
      (ConstructiveReal.ofSignedRatio (partialSum terms n)) (sums.toReal.value m) := by
    intro m later
    apply (ConstructiveReal.within_ofSignedRatio_iff _ _ _).mpr
    exact QProb.le_congr (magnitude_sub_symm _ _) (QProb.equiv_refl _) (partial_error_of_le terms coefficient bounded n m later)
  have limits := RealCauchySequence.limit_within_of_tail (RealCauchySequence.constant (ConstructiveReal.ofSignedRatio (partialSum terms n)))
    sums.toReal (envelope (2 * coefficient) n) n tails
  exact (ConstructiveReal.within_congr (RealCauchySequence.constant_limit _) sums.toReal_limit).mp limits

end Thesis.Probability.RationalGeometricSeries
