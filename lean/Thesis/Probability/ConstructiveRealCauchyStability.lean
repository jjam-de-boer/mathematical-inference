import Thesis.Probability.ConstructiveRealStability

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- A fixed closed error bound on sufficiently late sequence terms passes
to their effective limits. A common late index is computed from the moduli. -/
theorem limit_within_of_tail (first second : RealCauchySequence) (error : QProb) (tail : Nat)
    (bounded : ∀ n, tail ≤ n → Within error (first.value n) (second.value n)) : Within error first.limit second.limit := by
  apply within_of_forall_add_error
  intro precision
  let n := max tail (max (first.modulus precision.half.half.half) (second.modulus precision.half.half.half))
  have left := within_symm (first.tail_within precision.half n
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
  have right := second.tail_within precision.half n
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have combined := within_triangle (within_triangle left (bounded n (Nat.le_max_left _ _))) right
  have collected : QProb.Equiv (QProb.add (QProb.add precision.half.toQProb error) precision.half.toQProb)
      (QProb.add error precision.toQProb) :=
    QProb.equiv_trans (QProb.add_congr (QProb.add_comm _ _) (QProb.equiv_refl _))
      (QProb.equiv_trans (QProb.add_assoc _ _ _) (QProb.add_congr (QProb.equiv_refl _) precision.half_sum))
  exact within_mono combined (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

/-- Eventual closed order also passes to effective limits. -/
theorem limit_le_limit_of_tail (first second : RealCauchySequence) (tail : Nat)
    (compared : ∀ n, tail ≤ n → LE (first.value n) (second.value n)) : LE first.limit second.limit := by
  apply le_of_forall_rational_error
  intro precision
  let n := max tail (max (first.modulus precision.half.half.half) (second.modulus precision.half.half.half))
  have left := (first.tail_within precision.half n (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))).2
  have right := (second.tail_within precision.half n (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))).1
  have middle := add_le_add (compared n (Nat.le_max_left _ _)) (le_refl (ofSignedRatio precision.half.toSignedRatio))
  have shifted := add_le_add right (le_refl (ofSignedRatio precision.half.toSignedRatio))
  have collected : Equiv
      (ConstructiveReal.add (ConstructiveReal.add second.limit (ofSignedRatio precision.half.toSignedRatio))
        (ofSignedRatio precision.half.toSignedRatio))
      (ConstructiveReal.add second.limit (ofSignedRatio precision.toSignedRatio)) :=
    equiv_trans (add_assoc _ _ _) (add_congr (equiv_refl _)
      (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr precision.half_add_half)))
  exact (le_congr (equiv_refl _) collected).mp (le_trans left (le_trans middle shifted))

end Thesis.Probability.RealCauchySequence
