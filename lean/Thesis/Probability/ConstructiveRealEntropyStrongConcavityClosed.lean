import Thesis.Probability.ConstructiveRealEntropyStrongConcavity
import Thesis.Probability.ConstructiveRealPositiveUnitApproximation
import Thesis.Probability.ConstructiveRealEntropyLimits

namespace Thesis.Probability.ConstructiveReal

private def halfRatio : SignedRatio := ⟨1, 2, by decide⟩
private def eighthRatio : SignedRatio := ⟨1, 8, by decide⟩

/-- Quantitative midpoint concavity on the entire closed unit interval.
Zero coordinates and either endpoint order are included. Positive rational
approximations prove the pointwise estimate, and effective entropy/product
limits pass it to arbitrary analytic values without deciding real order. -/
theorem UnitIntervalValue.entropy_strong_midpoint (x y : UnitIntervalValue) :
    LE (add (mul (add x.entropy y.entropy) (ofSignedRatio ⟨1, 2, by decide⟩))
      (mul (mul (sub x.value y.value) (sub x.value y.value)) (ofSignedRatio ⟨1, 8, by decide⟩))) (x.midpoint y).entropy := by
  let mx := fun n => x.value.positiveUnitCenter (PositiveRatio.unitPrecision n)
  let my := fun n => y.value.positiveUnitCenter (PositiveRatio.unitPrecision n)
  let ux := fun n => UnitIntervalValue.ofQProb (mx n)
    (x.value.positiveUnitCenter_bounded x.nonnegative x.bounded (PositiveRatio.unitPrecision n))
  let uy := fun n => UnitIntervalValue.ofQProb (my n)
    (y.value.positiveUnitCenter_bounded y.nonnegative y.bounded (PositiveRatio.unitPrecision n))
  let sx := x.value.positiveUnitSequence x.nonnegative x.bounded
  let sy := y.value.positiveUnitSequence y.nonnegative y.bounded
  have nx (n : Nat) : LE zero (sx.value n) := (ux n).nonnegative
  have bx (n : Nat) : LE (sx.value n) one := (ux n).bounded
  have ny (n : Nat) : LE zero (sy.value n) := (uy n).nonnegative
  have by' (n : Nat) : LE (sy.value n) one := (uy n).bounded
  let hx := sx.mapEntropy nx bx
  let hy := sy.mapEntropy ny by'
  let half := RealCauchySequence.constant (ofSignedRatio halfRatio)
  let eighth := RealCauchySequence.constant (ofSignedRatio eighthRatio)
  let mean := (hx.add hy).mul half
  let difference := sx.sub sy
  let square := difference.mul difference
  let gap := square.mul eighth
  let left := mean.add gap
  let mid := (sx.add sy).mul half
  have nm (n : Nat) : LE zero (mid.value n) := ((ux n).midpoint (uy n)).nonnegative
  have bm (n : Nat) : LE (mid.value n) one := ((ux n).midpoint (uy n)).bounded
  let right := mid.mapEntropy nm bm
  have terms (n : Nat) : LE (left.value n) (right.value n) := by
    let p : PositiveRatio := ⟨(mx n).num, (mx n).den, x.value.positiveUnitCenter_positive (PositiveRatio.unitPrecision n), (mx n).den_pos⟩
    let q : PositiveRatio := ⟨(my n).num, (my n).den, y.value.positiveUnitCenter_positive (PositiveRatio.unitPrecision n), (my n).den_pos⟩
    exact positiveRational_entropy_strong_midpoint p q
      (x.value.positiveUnitCenter_bounded x.nonnegative x.bounded (PositiveRatio.unitPrecision n))
      (y.value.positiveUnitCenter_bounded y.nonnegative y.bounded (PositiveRatio.unitPrecision n))
  have inputX : Equiv sx.limit x.value := x.value.positiveUnitSequence_limit x.nonnegative x.bounded
  have inputY : Equiv sy.limit y.value := y.value.positiveUnitSequence_limit y.nonnegative y.bounded
  have entropyX : Equiv hx.limit x.entropy :=
    equiv_trans (sx.mapEntropy_limit nx bx)
      (realEntropyTerm_congr inputX (sx.le_limit zero nx) x.nonnegative (sx.limit_le one bx) x.bounded)
  have entropyY : Equiv hy.limit y.entropy :=
    equiv_trans (sy.mapEntropy_limit ny by')
      (realEntropyTerm_congr inputY (sy.le_limit zero ny) y.nonnegative (sy.limit_le one by') y.bounded)
  have halfLimit : Equiv half.limit (ofSignedRatio halfRatio) := RealCauchySequence.constant_limit _
  have eighthLimit : Equiv eighth.limit (ofSignedRatio eighthRatio) := RealCauchySequence.constant_limit _
  have meanLimit : Equiv mean.limit (mul (add x.entropy y.entropy) (ofSignedRatio halfRatio)) :=
    equiv_trans (RealCauchySequence.mul_limit _ _)
      (mul_congr (equiv_trans (RealCauchySequence.add_limit hx hy) (add_congr entropyX entropyY)) halfLimit)
  have differenceLimit : Equiv difference.limit (sub x.value y.value) :=
    equiv_trans (RealCauchySequence.sub_limit sx sy) (add_congr inputX (neg_congr inputY))
  have squareLimit : Equiv square.limit (mul (sub x.value y.value) (sub x.value y.value)) :=
    equiv_trans (RealCauchySequence.mul_limit difference difference) (mul_congr differenceLimit differenceLimit)
  have gapLimit : Equiv gap.limit (mul (mul (sub x.value y.value) (sub x.value y.value)) (ofSignedRatio eighthRatio)) :=
    equiv_trans (RealCauchySequence.mul_limit square eighth) (mul_congr squareLimit eighthLimit)
  have leftLimit : Equiv left.limit (add (mul (add x.entropy y.entropy) (ofSignedRatio halfRatio))
      (mul (mul (sub x.value y.value) (sub x.value y.value)) (ofSignedRatio eighthRatio))) :=
    equiv_trans (RealCauchySequence.add_limit mean gap) (add_congr meanLimit gapLimit)
  have midLimit : Equiv mid.limit (ConstructiveReal.midpoint x.value y.value) :=
    equiv_trans (RealCauchySequence.mul_limit (sx.add sy) half)
      (mul_congr (equiv_trans (RealCauchySequence.add_limit sx sy) (add_congr inputX inputY)) halfLimit)
  have rightLimit : Equiv right.limit (x.midpoint y).entropy :=
    equiv_trans (mid.mapEntropy_limit nm bm)
      (realEntropyTerm_congr midLimit (mid.le_limit zero nm) (x.midpoint y).nonnegative (mid.limit_le one bm) (x.midpoint y).bounded)
  exact (le_congr leftLimit rightLimit).mp (RealCauchySequence.limit_le_limit left right terms)

/-- Ordinary midpoint concavity follows by discarding only the proved
nonnegative quadratic gap. The zero boundary remains included. -/
theorem UnitIntervalValue.entropy_midpoint_concave (x y : UnitIntervalValue) :
    LE (mul (add x.entropy y.entropy) (ofSignedRatio ⟨1, 2, by decide⟩)) (x.midpoint y).entropy := by
  let average := mul (add x.entropy y.entropy) (ofSignedRatio halfRatio)
  have gapNonnegative : LE zero (mul (mul (sub x.value y.value) (sub x.value y.value)) (ofSignedRatio eighthRatio)) :=
    mul_nonnegative (square_nonnegative (sub x.value y.value)) ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel))
  have increased := (le_congr (add_zero average) (equiv_refl _)).mp (add_le_add (le_refl average) gapNonnegative)
  exact le_trans increased (x.entropy_strong_midpoint y)

end Thesis.Probability.ConstructiveReal
