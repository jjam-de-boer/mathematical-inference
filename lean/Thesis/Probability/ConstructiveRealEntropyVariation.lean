import Thesis.Probability.ConstructiveRealEntropyDerivative
import Thesis.Probability.ConstructiveRealSquareBounds

namespace Thesis.Probability.ConstructiveReal

private abbrev Expr := RationalPolynomial.Expression 5
private def xVar : Expr := .coordinate 0
private def yVar : Expr := .coordinate 1
private def logVar : Expr := .coordinate 2
private def cVar : Expr := .coordinate 3
private def inverseVar : Expr := .coordinate 4
private def deltaVar : Expr := .sub yVar xVar
private def zeroExpr : Expr := .constant SignedRatio.zero
private def expansionLeft : Expr := .sub zeroExpr (.mul yVar (.add logVar (.mul deltaVar (.mul cVar inverseVar))))
private def expansionRight : Expr := .sub
  (.sub (.sub zeroExpr (.mul xVar logVar)) (.mul deltaVar (.add logVar (.mul cVar (.mul xVar inverseVar)))))
  (.mul (.mul deltaVar deltaVar) (.mul cVar inverseVar))

private theorem entropy_product_expansion (x y logarithm c inverse : ConstructiveReal) :
    Equiv (sub zero (mul y (add logarithm (mul (sub y x) (mul c inverse)))))
      (sub (sub (sub zero (mul x logarithm)) (mul (sub y x) (add logarithm (mul c (mul x inverse)))))
        (mul (mul (sub y x) (sub y x)) (mul c inverse))) :=
  RationalPolynomial.Expression.equalityCheck_sound_real expansionLeft expansionRight (by decide +kernel)
    (fun index => match index.val with | 0 => x | 1 => y | 2 => logarithm | 3 => c | _ => inverse)

/-- A rational bound on the quadratic entropy remainder, depending only on
the supplied positive domain bound. It is independent of real presentations. -/
def entropyVariationFactor (lower : PositiveRatio) : Nat := 3 * lower.den

private theorem entropyVariationFactor_pos (lower : PositiveRatio) : 0 < entropyVariationFactor lower :=
  Nat.mul_pos (by decide) lower.den_pos

private theorem entropy_factor_bound (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) :
    LE zero (mul RationalLogSecant.limit (x.positiveInverse lower bounded)) ∧
      LE (mul RationalLogSecant.limit (x.positiveInverse lower bounded)) (ofSignedRatio (QProb.ofNat (entropyVariationFactor lower)).toSignedRatio) := by
  have cNonnegative : LE zero RationalLogSecant.limit :=
    le_trans ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel)) RationalLogSecant.one_le_limit
  have inverseNonnegative := x.positiveInverse_nonnegative lower bounded
  have dNonnegative : LE zero (ofSignedRatio (QProb.ofNat lower.den).toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le _))
  have upper := mul_le_mul RationalLogSecant.limit_le_three (x.positiveInverse_upper lower bounded) cNonnegative dNonnegative
  have collected : Equiv (mul (ofSignedRatio ⟨3, 1, by decide⟩) (ofSignedRatio (QProb.ofNat lower.den).toSignedRatio))
      (ofSignedRatio (QProb.ofNat (entropyVariationFactor lower)).toSignedRatio) :=
    equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by
      simp only [SignedRatio.Equiv, SignedRatio.mul, QProb.toSignedRatio, QProb.ofNat, entropyVariationFactor,
        Nat.one_mul, Int.natCast_one, Int.mul_one, Int.natCast_mul]
      rfl))
  exact ⟨mul_nonnegative cNonnegative inverseNonnegative, (le_congr (equiv_refl _) collected).mp upper⟩

private theorem within_zero_of_nonnegative {error : QProb} {value : ConstructiveReal}
    (nonnegative : LE zero value) (bounded : LE value (ofSignedRatio error.toSignedRatio)) : Within error value zero := by
  have errorPositive : LE zero (ofSignedRatio error.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le error))
  exact ⟨(le_congr (equiv_refl _) (zero_add _)).mpr bounded,
    (le_congr (zero_add zero) (equiv_refl _)).mp (add_le_add nonnegative errorPositive)⟩

private theorem entropy_quadratic_error (x y : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (precision radius : PositiveRatio)
    (small : PositiveRatio.LE radius (precision.divideNat (entropyVariationFactor lower) (entropyVariationFactor_pos lower)))
    (close : Within radius.toQProb x y) :
    Within (QProb.mul precision.toQProb radius.toQProb)
      (neg (mul (mul (sub y x) (sub y x)) (mul RationalLogSecant.limit (x.positiveInverse lower bounded)))) zero := by
  let factor := mul RationalLogSecant.limit (x.positiveInverse lower bounded)
  have factorBounds := entropy_factor_bound x lower bounded
  have square := within_zero_of_nonnegative (square_nonnegative (sub y x)) (within_square close)
  have multiplied := within_mul_right_bounded square factorBounds.1 factorBounds.2
  have reduced := (within_congr (equiv_refl _) (zero_mul factor)).mp multiplied
  have negated := (within_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mp (within_neg reduced)
  have enlarged := QProb.mul_le_mul small (QProb.le_refl (QProb.mul radius.toQProb (QProb.ofNat (entropyVariationFactor lower))))
  have before : QProb.Equiv
      (QProb.mul (QProb.mul radius.toQProb radius.toQProb) (QProb.ofNat (entropyVariationFactor lower)))
      (QProb.mul radius.toQProb (QProb.mul radius.toQProb (QProb.ofNat (entropyVariationFactor lower)))) := QProb.mul_assoc _ _ _
  have after : QProb.Equiv
      (QProb.mul (precision.divideNat (entropyVariationFactor lower) (entropyVariationFactor_pos lower)).toQProb
        (QProb.mul radius.toQProb (QProb.ofNat (entropyVariationFactor lower))))
      (QProb.mul precision.toQProb radius.toQProb) :=
    QProb.equiv_trans (QProb.equiv_symm (QProb.mul_assoc _ _ _))
      (QProb.equiv_trans (QProb.mul_congr (QProb.mul_comm _ _) (QProb.equiv_refl _))
        (QProb.equiv_trans (QProb.mul_assoc _ _ _) (QProb.equiv_trans
          (QProb.mul_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul precision _ _)) (QProb.mul_comm _ _))))
  exact within_mono negated (QProb.le_congr (QProb.equiv_symm before) after enlarged)

/-- A single entropy variation modulus works for all points in the supplied
positive part of [0,1]. Only the lower bound and accuracy enter its computation. -/
def entropyVariationModulus (lower precision : PositiveRatio) : PositiveRatio :=
  let first := logModulus lower precision.half
  let second := precision.half.divideNat (entropyVariationFactor lower) (entropyVariationFactor_pos lower)
  if PositiveRatio.LE first second then first else second

private theorem entropyVariationModulus_bounds (lower precision : PositiveRatio) :
    PositiveRatio.LE (entropyVariationModulus lower precision) (logModulus lower precision.half) ∧
      PositiveRatio.LE (entropyVariationModulus lower precision)
        (precision.half.divideNat (entropyVariationFactor lower) (entropyVariationFactor_pos lower)) := by
  by_cases ordered : PositiveRatio.LE (logModulus lower precision.half)
      (precision.half.divideNat (entropyVariationFactor lower) (entropyVariationFactor_pos lower))
  · simp only [entropyVariationModulus, if_pos ordered]
    exact ⟨PositiveRatio.le_refl _, ordered⟩
  · simp only [entropyVariationModulus, if_neg ordered]
    exact ⟨(PositiveRatio.le_total _ _).resolve_left ordered, PositiveRatio.le_refl _⟩

private theorem entropy_linear_expansion (x y : ConstructiveReal) (lower : PositiveRatio)
    (inside : entropyPositiveDomain lower x) :
    Equiv (neg (mul y (add (x.positiveLog2 lower inside.1)
        (mul (sub y x) (mul RationalLogSecant.limit (x.positiveInverse lower inside.1))))))
      (add (add (x.realEntropyTerm (entropyPositiveNonnegative lower x inside) inside.2)
          (mul (sub y x) (neg (add (x.positiveLog2 lower inside.1) RationalLogSecant.limit))))
        (neg (mul (mul (sub y x) (sub y x)) (mul RationalLogSecant.limit (x.positiveInverse lower inside.1))))) := by
  let logarithm := x.positiveLog2 lower inside.1
  let c := RationalLogSecant.limit
  let inverse := x.positiveInverse lower inside.1
  let delta := sub y x
  have unit : Equiv (mul c (mul x inverse)) c :=
    equiv_trans (mul_congr (equiv_refl c) (x.mul_positiveInverse lower inside.1)) (mul_one c)
  have base : Equiv (sub zero (mul x logarithm)) (x.realEntropyTerm (entropyPositiveNonnegative lower x inside) inside.2) :=
    equiv_trans (zero_add _) (equiv_symm (realEntropyTerm_formula x (entropyPositiveNonnegative lower x inside) inside.2 lower inside.1))
  have linear : Equiv
      (sub (sub zero (mul x logarithm)) (mul delta (add logarithm (mul c (mul x inverse)))))
      (add (x.realEntropyTerm (entropyPositiveNonnegative lower x inside) inside.2) (mul delta (neg (add logarithm c)))) :=
    equiv_trans (add_congr base (neg_congr (mul_congr (equiv_refl delta) (add_congr (equiv_refl logarithm) unit))))
      (add_congr (equiv_refl _) (equiv_symm (mul_neg delta (add logarithm c))))
  exact equiv_trans (equiv_symm (zero_add _))
    (equiv_trans (entropy_product_expansion x y logarithm c inverse) (add_congr linear (equiv_refl _)))

/-- A uniform first-variation certificate for entropy on a positive part of
[0,1]. The same explicit radius works for every pair of admissible points,
regardless of their rational enclosure presentations. The proof combines the
logarithm error scaled by a probability at most one with a bounded quadratic
remainder. This uniformity is needed for finite-partition calculus. -/
theorem realEntropyTerm_uniform_first_variation (x y : ConstructiveReal) (lower : PositiveRatio)
    (insideX : entropyPositiveDomain lower x) (insideY : entropyPositiveDomain lower y)
    (precision radius : PositiveRatio) (small : PositiveRatio.LE radius (entropyVariationModulus lower precision))
    (close : Within radius.toQProb x y) :
    Within (QProb.mul precision.toQProb radius.toQProb)
      (y.realEntropyTerm (entropyPositiveNonnegative lower y insideY) insideY.2)
      (add (x.realEntropyTerm (entropyPositiveNonnegative lower x insideX) insideX.2)
        (mul (sub y x) (neg (add (x.positiveLog2 lower insideX.1) RationalLogSecant.limit)))) := by
  let logarithm := x.positiveLog2 lower insideX.1
  let factor := mul RationalLogSecant.limit (x.positiveInverse lower insideX.1)
  let linear := add (x.realEntropyTerm (entropyPositiveNonnegative lower x insideX) insideX.2)
    (mul (sub y x) (neg (add logarithm RationalLogSecant.limit)))
  have thresholds := entropyVariationModulus_bounds lower precision
  have logError := positiveLog2_first_variation x y lower insideX.1 insideY.1 precision.half radius
    (PositiveRatio.le_trans small thresholds.1) close
  have multiplied := within_mul_right_bounded (bound := QProb.one) logError (entropyPositiveNonnegative lower y insideY) insideY.2
  have narrowed := within_mono multiplied (QProb.le_congr (QProb.equiv_refl _) (QProb.mul_one _) (QProb.le_refl _))
  have scaled : Within (QProb.mul precision.half.toQProb radius.toQProb)
      (neg (mul y (y.positiveLog2 lower insideY.1)))
      (neg (mul y (add logarithm (mul (sub y x) factor)))) :=
    (within_congr (neg_congr (mul_comm _ _)) (neg_congr (mul_comm _ _))).mp (within_neg narrowed)
  have compared : Within (QProb.mul precision.half.toQProb radius.toQProb)
      (y.realEntropyTerm (entropyPositiveNonnegative lower y insideY) insideY.2)
      (add linear (neg (mul (mul (sub y x) (sub y x)) factor))) :=
    (within_congr (equiv_symm (realEntropyTerm_formula y (entropyPositiveNonnegative lower y insideY) insideY.2 lower insideY.1))
      (entropy_linear_expansion x y lower insideX)).mp scaled
  have quadratic := entropy_quadratic_error x y lower insideX.1 precision.half radius
    (PositiveRatio.le_trans small thresholds.2) close
  have translated := (within_add_left_iff _ linear _ _).mpr quadratic
  have reduced := (within_congr (equiv_refl _) (add_zero linear)).mp translated
  have collected : QProb.Equiv
      (QProb.add (QProb.mul precision.half.toQProb radius.toQProb) (QProb.mul precision.half.toQProb radius.toQProb))
      (QProb.mul precision.toQProb radius.toQProb) :=
    QProb.equiv_trans (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))
      (QProb.mul_congr precision.half_sum (QProb.equiv_refl _))
  exact within_mono (within_triangle compared reduced) (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal
