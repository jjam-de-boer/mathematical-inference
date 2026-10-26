import Thesis.Probability.ConstructiveRealMomentConvexity
import Thesis.Probability.ConstructiveRealEntropyUniversalBound
import Thesis.Probability.ConstructiveRealSquareDistance

namespace Thesis.Probability.ConstructiveReal

private abbrev Expr := RationalPolynomial.Expression 4
private def a : Expr := .coordinate 0
private def b : Expr := .coordinate 1
private def t : Expr := .coordinate 2
private def u : Expr := .coordinate 3
private def half : SignedRatio := ⟨1, 2, by decide⟩
private def eighth : SignedRatio := ⟨1, 8, by decide⟩
private def four : SignedRatio := ⟨4, 1, by decide⟩
private theorem bound_average (x y errorX errorY : ConstructiveReal) :
    Equiv (midpoint (add x errorX) (add y errorY)) (add (midpoint x y) (midpoint errorX errorY)) :=
  RationalPolynomial.Expression.equalityCheck_sound_real
    (.mul (.add (.add a t) (.add b u)) (.constant half))
    (.add (.mul (.add a b) (.constant half)) (.mul (.add t u) (.constant half)))
    (by decide +kernel) (fun index => match index.val with | 0 => x | 1 => y | 2 => errorX | _ => errorY)

private theorem scaled_average (errorX errorY : ConstructiveReal) :
    Equiv (midpoint errorX errorY)
      (mul (ofSignedRatio eighth) (mul (ofSignedRatio four) (add errorX errorY))) :=
  RationalPolynomial.Expression.equalityCheck_sound_real
    (.mul (.add a b) (.constant half))
    (.mul (.constant eighth) (.mul (.constant four) (.add a b)))
    (by decide +kernel) (fun index => if index.val = 0 then errorX else errorY)

/-- A quantitative midpoint gap converts separate near-maximum certificates
into a squared-distance bound. This algebra uses only closed real order. -/
theorem squared_gap_of_near_maxima (x y mid distance errorX errorY : ConstructiveReal)
    (strong : LE (add (midpoint x y) (mul distance (ofSignedRatio eighth))) mid)
    (first : LE mid (add x errorX)) (second : LE mid (add y errorY)) :
    LE distance (mul (ofSignedRatio four) (add errorX errorY)) := by
  have halfPositive : LE zero (ofSignedRatio half) := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  have averaged := mul_le_mul_nonnegative_right halfPositive (add_le_add first second)
  have midBound : LE mid (add (midpoint x y) (midpoint errorX errorY)) :=
    (le_congr (midpoint_self mid) (bound_average x y errorX errorY)).mp averaged
  have reordered := (le_congr (add_comm _ _) (add_comm _ _)).mp (le_trans strong midBound)
  have gap := (add_le_add_right_iff _ _ (midpoint x y)).mp reordered
  have scaled : LE (mul (ofSignedRatio eighth) distance)
      (mul (ofSignedRatio eighth) (mul (ofSignedRatio four) (add errorX errorY))) :=
    (le_congr (mul_comm _ _) (scaled_average errorX errorY)).mp gap
  exact (mul_le_mul_positive_iff (ofSignedRatio eighth) (⟨1, 8, by decide, by decide⟩ : PositiveRatio)
    (le_refl _) _ _).mp scaled

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

/-- A certificate about all ideal competitors, separated from its particular
rational construction. This interface also applies to an attained optimizer. -/
def RealCompatibleLaw.NearOptimal {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw) (error : QProb) : Prop :=
  ∀ other : problem.RealCompatibleLaw, LE other.entropy (add law.entropy (ofSignedRatio error.toSignedRatio))

theorem EntropyApproximation.nearOptimal [DecidableEq A] {problem : PartialMomentProblem A} {tolerance : QProb}
    (approximation : problem.EntropyApproximation tolerance) : approximation.law.toReal.NearOptimal tolerance :=
  approximation.real_upper

/-- Two feasible near-maximum laws have squared distance at most four times
the sum of their entropy gaps. All declared coordinates, including forced
zeros, contribute to this estimate. -/
theorem RealCompatibleLaw.squaredDistance_le_of_nearOptimal {problem : PartialMomentProblem A}
    (first second : problem.RealCompatibleLaw) (errorX errorY : QProb)
    (optimalX : first.NearOptimal errorX) (optimalY : second.NearOptimal errorY) :
    LE (first.squaredDistance second) (ofSignedRatio (QProb.mul (QProb.ofNat 4) (QProb.add errorX errorY)).toSignedRatio) := by
  have bound := squared_gap_of_near_maxima first.entropy second.entropy (first.midpoint second).entropy
    (first.squaredDistance second) (ofSignedRatio errorX.toSignedRatio) (ofSignedRatio errorY.toSignedRatio)
    (first.strong_midpoint second) (optimalX _) (optimalY _)
  have collect : Equiv (mul (ofSignedRatio (⟨4, 1, by decide⟩ : SignedRatio))
      (add (ofSignedRatio errorX.toSignedRatio) (ofSignedRatio errorY.toSignedRatio)))
      (ofSignedRatio (QProb.mul (QProb.ofNat 4) (QProb.add errorX errorY)).toSignedRatio) := by
    rw [QProb.toSignedRatio_mul, QProb.toSignedRatio_add]
    exact equiv_trans (mul_congr (equiv_refl _) (ofSignedRatio_add _ _)) (ofSignedRatio_mul _ _)
  exact (le_congr (equiv_refl _) collect).mp bound

/-- An explicit rational gap threshold certifies every coordinate distance.
The executable tolerance comparison is on rationals, never on analytic values. -/
theorem RealCompatibleLaw.coordinate_within_of_nearOptimal {problem : PartialMomentProblem A}
    (first second : problem.RealCompatibleLaw) (errorX errorY : QProb) (radius : PositiveRatio)
    (optimalX : first.NearOptimal errorX) (optimalY : second.NearOptimal errorY)
    (small : QProb.LE (QProb.mul (QProb.ofNat 4) (QProb.add errorX errorY)) (QProb.mul radius.toQProb radius.toQProb))
    (index : Fin problem.cells.length) : Within radius.toQProb (first.mass index).value (second.mass index).value := by
  have squared := le_trans (first.coordinate_square_le_distance second index)
    (le_trans (first.squaredDistance_le_of_nearOptimal second errorX errorY optimalX optimalY)
      ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr small)))
  have radiusSquare : Equiv (mul (ofSignedRatio radius.toSignedRatio) (ofSignedRatio radius.toSignedRatio))
      (ofSignedRatio (QProb.mul radius.toQProb radius.toQProb).toSignedRatio) := by
    rw [QProb.toSignedRatio_mul]
    exact ofSignedRatio_mul _ _
  exact within_of_square_sub_le _ _ radius ((le_congr (equiv_refl _) radiusSquare).mpr squared)

end Thesis.Probability.Distros.PartialMomentProblem
