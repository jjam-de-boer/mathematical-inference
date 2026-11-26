import Thesis.Probability.ConstructiveRealOrderedRing
import Thesis.Probability.ConstructiveRealDistanceAlgebra

/-!
# Multiplication errors controlled by a value bound

If a nonnegative analytic factor lies below a supplied rational bound,
then multiplication by it scales the distance certificate by at most that
bound. The result uses the factor's value enclosure rather than the
numerators in any chosen rational approximation. It therefore applies
uniformly to all factors satisfying the same checked inequalities.
-/

namespace Thesis.Probability.ConstructiveReal

/-- A supplied nonnegative real upper bound gives a rational Lipschitz
constant for multiplication. The bound is about values, so it does not depend
on the numerator sizes of their rational presentations. -/
theorem within_mul_right_bounded {error bound : QProb} {x y factor : ConstructiveReal}
    (close : Within error x y) (nonnegative : LE zero factor)
    (bounded : LE factor (ofSignedRatio bound.toSignedRatio)) :
    Within (QProb.mul error bound) (mul x factor) (mul y factor) := by
  let e := ofSignedRatio error.toSignedRatio
  have ePositive : LE zero e := (ofSignedRatio_le_iff _ _).mpr
    ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le error))
  have eBound := mul_le_mul_nonnegative ePositive bounded
  have rational : Equiv (mul e (ofSignedRatio bound.toSignedRatio))
      (ofSignedRatio (QProb.mul error bound).toSignedRatio) := by
    rw [QProb.toSignedRatio_mul]
    exact ofSignedRatio_mul _ _
  have compared : LE (mul e factor) (ofSignedRatio (QProb.mul error bound).toSignedRatio) :=
    (le_congr (equiv_refl _) rational).mp eBound
  have oneSide (a b : ConstructiveReal) (ordered : LE a (add b e)) :
      LE (mul a factor) (add (mul b factor) (ofSignedRatio (QProb.mul error bound).toSignedRatio)) := by
    have multiplied := mul_le_mul_nonnegative_right nonnegative ordered
    exact le_trans ((le_congr (equiv_refl _) (add_mul b e factor)).mp multiplied)
      (add_le_add (le_refl _) compared)
  exact ⟨oneSide x y close.1, oneSide y x close.2⟩

end Thesis.Probability.ConstructiveReal
