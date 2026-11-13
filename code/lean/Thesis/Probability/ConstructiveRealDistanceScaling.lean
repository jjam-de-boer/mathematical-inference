import Thesis.Probability.ConstructiveRealDistanceAlgebra
import Thesis.Probability.ConstructiveRealStability

namespace Thesis.Probability.ConstructiveReal

theorem within_sub_right_iff (error : QProb) (offset x y : ConstructiveReal) :
    Within error (sub x offset) (sub y offset) ↔ Within error x y :=
  (within_congr (add_comm x (neg offset)) (add_comm y (neg offset))).trans
    (within_add_left_iff error (neg offset) x y)

theorem add_sub_cancel (x increment : ConstructiveReal) : Equiv (sub (add x increment) x) increment :=
  equiv_trans (add_congr (add_comm _ _) (equiv_refl _))
    (equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg x)) (add_zero _)))

theorem within_increment {error : QProb} {x y : ConstructiveReal} (close : Within error x y) :
    Within error (sub y x) zero :=
  within_symm ((within_congr ((sub_equiv_zero_iff x x).mpr (equiv_refl _)) (equiv_refl _)).mp
    ((within_sub_right_iff error x x y).mpr close))

/-- Multiplying by a fixed real has a computed rational Lipschitz bound.
The magnitude bound comes from its certified fine rational approximants. -/
theorem within_mul_right {error : QProb} {x y : ConstructiveReal} (close : Within error x y) (factor : ConstructiveReal) :
    Within (QProb.mul error (QProb.ofNat factor.rationalApproximation.magnitudeBound)) (mul x factor) (mul y factor) := by
  have compared := mul_within error QProb.zero close (within_refl QProb.zero factor)
  have collected : QProb.Equiv
      (QProb.add (QProb.mul error (QProb.ofNat factor.rationalApproximation.magnitudeBound))
        (QProb.mul (QProb.ofNat y.rationalApproximation.magnitudeBound) QProb.zero))
      (QProb.mul error (QProb.ofNat factor.rationalApproximation.magnitudeBound)) := by
    apply QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) ?_)
    · exact QProb.add_zero _
    · simp only [QProb.Equiv, QProb.mul, QProb.zero, Nat.mul_zero, Nat.zero_mul]
  exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal
