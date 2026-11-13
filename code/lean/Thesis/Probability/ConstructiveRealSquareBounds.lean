import Thesis.Probability.ConstructiveRealOrderedRing

namespace Thesis.Probability.ConstructiveReal

private theorem sub_pair_cancel (a b c : ConstructiveReal) : Equiv (sub (add a b) (add b c)) (sub a c) :=
  equiv_trans (add_congr (equiv_refl _) (equiv_trans (neg_add b c) (add_comm _ _)))
    (equiv_trans (add_four _ _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg b)) (add_zero _)))

/-- Difference of squares in the constructed real ring. -/
theorem difference_squares (radius value : ConstructiveReal) :
    Equiv (mul (sub radius value) (add radius value)) (sub (mul radius radius) (mul value value)) :=
  equiv_trans (sub_mul _ _ _) (equiv_trans
    (add_congr (mul_add _ _ _) (neg_congr (equiv_trans (mul_add _ _ _)
      (add_congr (mul_comm _ _) (equiv_refl _))))) (sub_pair_cancel _ _ _))

/-- A two-sided order bound controls a square without deciding the sign of
the bounded real. This is used to turn Taylor remainders into distance bounds. -/
theorem square_le_of_two_sided {value radius : ConstructiveReal}
    (upper : LE value radius) (lower : LE (neg value) radius) : LE (mul value value) (mul radius radius) := by
  have first := (zero_le_sub_iff radius value).mpr upper
  have second := (le_congr (equiv_refl zero) (add_congr (equiv_refl radius) (neg_neg value))).mp
    ((zero_le_sub_iff radius (neg value)).mpr lower)
  have multiplied := mul_nonnegative first second
  exact (zero_le_sub_iff _ _).mp ((le_congr (equiv_refl _) (difference_squares radius value)).mp multiplied)

/-- Squared distance is bounded by the square of any certified rational
radius. Neither the real increment's sign nor its equality to zero is tested. -/
theorem within_square {error : QProb} {x y : ConstructiveReal} (close : Within error x y) :
    LE (mul (sub y x) (sub y x)) (ofSignedRatio (QProb.mul error error).toSignedRatio) := by
  let r := ofSignedRatio error.toSignedRatio
  have canceled (z : ConstructiveReal) : Equiv (add (add z r) (neg z)) r :=
    equiv_trans (add_congr (add_comm z r) (equiv_refl _))
      (equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg z)) (add_zero _)))
  have upper : LE (sub y x) r :=
    (le_congr (equiv_refl _) (canceled x)).mp (add_le_add close.2 (le_refl (neg x)))
  have reverse : LE (sub x y) r :=
    (le_congr (equiv_refl _) (canceled y)).mp (add_le_add close.1 (le_refl (neg y)))
  have negated : Equiv (neg (sub y x)) (sub x y) :=
    equiv_trans (neg_add y (neg x)) (equiv_trans (add_congr (equiv_refl _) (neg_neg x)) (add_comm _ _))
  have squared := square_le_of_two_sided upper ((le_congr negated (equiv_refl _)).mpr reverse)
  have rational : Equiv (mul r r) (ofSignedRatio (QProb.mul error error).toSignedRatio) := by
    rw [QProb.toSignedRatio_mul]
    exact ofSignedRatio_mul _ _
  exact (le_congr (equiv_refl _) rational).mp squared

end Thesis.Probability.ConstructiveReal
