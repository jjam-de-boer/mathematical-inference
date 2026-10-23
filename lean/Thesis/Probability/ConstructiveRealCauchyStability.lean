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

end Thesis.Probability.RealCauchySequence
