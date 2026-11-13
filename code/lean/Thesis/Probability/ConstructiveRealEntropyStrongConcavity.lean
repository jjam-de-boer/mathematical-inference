import Thesis.Probability.ConstructiveRealEntropyCurvature
import Thesis.Probability.ConstructiveRealEntropySum

namespace Thesis.Probability.ConstructiveReal

private def halfRatio : SignedRatio := ⟨1, 2, by decide⟩
private def eighthRatio : SignedRatio := ⟨1, 8, by decide⟩
private abbrev Expr := RationalPolynomial.Expression 4
private def xVar : Expr := .coordinate 0
private def yVar : Expr := .coordinate 1
private def hxVar : Expr := .coordinate 2
private def hyVar : Expr := .coordinate 3
private def midpointVar : Expr := .mul (.add xVar yVar) (.constant halfRatio)
private def correction (x : Expr) : Expr := .mul (.mul x x) (.constant halfRatio)
private def correctedAverage : Expr := .sub
  (.mul (.add (.add hxVar (correction xVar)) (.add hyVar (correction yVar))) (.constant halfRatio))
  (correction midpointVar)
private def entropyGap : Expr := .add (.mul (.add hxVar hyVar) (.constant halfRatio))
  (.mul (.mul (.sub xVar yVar) (.sub xVar yVar)) (.constant eighthRatio))

private theorem quadratic_midpoint_identity (x y hx hy : ConstructiveReal) :
    Equiv (sub (mul (add (add hx (mul (mul x x) (ofSignedRatio halfRatio)))
        (add hy (mul (mul y y) (ofSignedRatio halfRatio)))) (ofSignedRatio halfRatio))
      (mul (mul (midpoint x y) (midpoint x y)) (ofSignedRatio halfRatio)))
      (add (mul (add hx hy) (ofSignedRatio halfRatio))
        (mul (mul (sub x y) (sub x y)) (ofSignedRatio eighthRatio))) :=
  RationalPolynomial.Expression.equalityCheck_sound_real correctedAverage entropyGap (by decide +kernel)
    (fun index => match index.val with | 0 => x | 1 => y | 2 => hx | _ => hy)

/-- Entropy has a quantitative midpoint gap of at least (x-y)^2/8 bits
on the positive unit interval. This version uses a supplied endpoint order;
the zero boundary and order-free extension require a separate limiting step.
The estimate is derived from uniform variation and finite partitions, rather
than assuming strict concavity or a nonconstructive mean-value theorem. -/
theorem realEntropyTerm_strong_midpoint_ordered (x y : ConstructiveReal) (lower : PositiveRatio)
    (insideX : entropyPositiveDomain lower x) (insideY : entropyPositiveDomain lower y) (ordered : LE x y) :
    let m := midpoint x y
    let insideM := midpoint_inside x y lower insideX insideY ordered
    LE (add (mul (add (x.realEntropyTerm (entropyPositiveNonnegative lower x insideX) insideX.2)
        (y.realEntropyTerm (entropyPositiveNonnegative lower y insideY) insideY.2)) (ofSignedRatio ⟨1, 2, by decide⟩))
      (mul (mul (sub x y) (sub x y)) (ofSignedRatio ⟨1, 8, by decide⟩)))
      (m.realEntropyTerm (entropyPositiveNonnegative lower m insideM) insideM.2) := by
  intro m insideM
  let hx := x.realEntropyTerm (entropyPositiveNonnegative lower x insideX) insideX.2
  let hy := y.realEntropyTerm (entropyPositiveNonnegative lower y insideY) insideY.2
  let hm := m.realEntropyTerm (entropyPositiveNonnegative lower m insideM) insideM.2
  let quadratic := mul (mul m m) (ofSignedRatio halfRatio)
  have halfNonnegative : LE zero (ofSignedRatio halfRatio) := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  have comparison := adjustedEntropy_midpoint x y lower insideX insideY ordered
  have scaled := mul_le_mul_nonnegative_right halfNonnegative comparison
  have reduced : LE (mul (add (adjustedEntropy lower x insideX) (adjustedEntropy lower y insideY)) (ofSignedRatio halfRatio))
      (adjustedEntropy lower m insideM) :=
    (le_congr (equiv_refl _) (midpoint_self (adjustedEntropy lower m insideM))).mp scaled
  have shifted := add_le_add reduced (le_refl (neg quadratic))
  have cancel : Equiv (sub (adjustedEntropy lower m insideM) quadratic) hm :=
    equiv_trans (add_assoc hm quadratic (neg quadratic))
      (equiv_trans (add_congr (equiv_refl hm) (add_neg quadratic)) (add_zero hm))
  exact (le_congr (quadratic_midpoint_identity x y hx hy) cancel).mp shifted

/-- Midpoints of auxiliary unit coordinates remain in the entropy domain. -/
def UnitIntervalValue.midpoint (x y : UnitIntervalValue) : UnitIntervalValue where
  value := ConstructiveReal.midpoint x.value y.value
  nonnegative := (midpoint_unit x.value y.value x.nonnegative y.nonnegative x.bounded y.bounded).1
  bounded := (midpoint_unit x.value y.value x.nonnegative y.nonnegative x.bounded y.bounded).2

private abbrev Expr2 := RationalPolynomial.Expression 2
private def squareForward : Expr2 := .mul (.sub (.coordinate 0) (.coordinate 1)) (.sub (.coordinate 0) (.coordinate 1))
private def squareReverse : Expr2 := .mul (.sub (.coordinate 1) (.coordinate 0)) (.sub (.coordinate 1) (.coordinate 0))
private theorem sub_square_comm (x y : ConstructiveReal) : Equiv (mul (sub x y) (sub x y)) (mul (sub y x) (sub y x)) :=
  RationalPolynomial.Expression.equalityCheck_sound_real squareForward squareReverse (by decide +kernel)
    (fun index => if index.val = 0 then x else y)

/-- The positive rational version has no endpoint order premise: that finite
comparison is computed, and the two branches agree by midpoint symmetry.
The following real extension will avoid any real-order decision. -/
theorem positiveRational_entropy_strong_midpoint (p q : PositiveRatio) (boundedP : p.num ≤ p.den) (boundedQ : q.num ≤ q.den) :
    let x := UnitIntervalValue.ofQProb p.toQProb boundedP
    let y := UnitIntervalValue.ofQProb q.toQProb boundedQ
    LE (add (mul (add x.entropy y.entropy) (ofSignedRatio ⟨1, 2, by decide⟩))
      (mul (mul (sub x.value y.value) (sub x.value y.value)) (ofSignedRatio ⟨1, 8, by decide⟩))) (x.midpoint y).entropy := by
  intro x y
  by_cases ordered : PositiveRatio.LE p q
  · have compared : LE x.value y.value :=
      (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff p.toQProb q.toQProb).mpr ordered)
    exact realEntropyTerm_strong_midpoint_ordered x.value y.value p ⟨le_refl x.value, x.bounded⟩ ⟨compared, y.bounded⟩ compared
  · have reverse : PositiveRatio.LE q p := (PositiveRatio.le_total p q).resolve_left ordered
    have compared : LE y.value x.value :=
      (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff q.toQProb p.toQProb).mpr reverse)
    have strong := realEntropyTerm_strong_midpoint_ordered y.value x.value q ⟨le_refl y.value, y.bounded⟩ ⟨compared, x.bounded⟩ compared
    have leftSame : Equiv
        (add (mul (add y.entropy x.entropy) (ofSignedRatio halfRatio))
          (mul (mul (sub y.value x.value) (sub y.value x.value)) (ofSignedRatio eighthRatio)))
        (add (mul (add x.entropy y.entropy) (ofSignedRatio halfRatio))
          (mul (mul (sub x.value y.value) (sub x.value y.value)) (ofSignedRatio eighthRatio))) :=
      add_congr (mul_congr (add_comm _ _) (equiv_refl _)) (mul_congr (sub_square_comm y.value x.value) (equiv_refl _))
    have rightSame : Equiv (y.midpoint x).entropy (x.midpoint y).entropy :=
      realEntropyTerm_congr (midpoint_comm y.value x.value) (y.midpoint x).nonnegative (x.midpoint y).nonnegative
        (y.midpoint x).bounded (x.midpoint y).bounded
    exact (le_congr leftSame rightSame).mp strong

end Thesis.Probability.ConstructiveReal
