import Thesis.Probability.ConstructiveRealLogExpCoefficient
import Thesis.Probability.ConstructiveDerivativeWithinScaling

namespace Thesis.Probability.ConstructiveReal

/-- The natural-log value of two, obtained as the positive reciprocal of
the derived bit-logarithm coefficient. Its compatibility with the Taylor
exponential is proved below rather than assumed by this normalization. -/
def lnTwo : ConstructiveReal :=
  RationalLogSecant.limit.positiveInverse PositiveRatio.one RationalLogSecant.one_le_limit

theorem coefficient_mul_lnTwo : Equiv (mul RationalLogSecant.limit lnTwo) one :=
  RationalLogSecant.limit.mul_positiveInverse PositiveRatio.one RationalLogSecant.one_le_limit


/-- The bit-to-natural conversion has an explicit positive rational lower
bound, computed from a finite enclosure of the logarithm coefficient. -/
theorem lnTwo_lower : LE (ofSignedRatio RationalLogSecant.limit.positiveInverseLower.toSignedRatio) lnTwo :=
  RationalLogSecant.limit.positiveInverse_lower PositiveRatio.one RationalLogSecant.one_le_limit

/-- Natural logarithm on an explicitly positive real domain, with the same
certified rational evaluation interface as the original base-two logarithm. -/
def positiveLn (x : ConstructiveReal) (lower : PositiveRatio) (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : ConstructiveReal :=
  mul (x.positiveLog2 lower bounded) lnTwo

theorem positiveLn_congr {x y : ConstructiveReal} (same : Equiv x y) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv (x.positiveLn lowerX boundedX) (y.positiveLn lowerY boundedY) :=
  mul_congr (positiveLog2_congr same lowerX lowerY boundedX boundedY) (equiv_refl lnTwo)

theorem positiveLn_one (lower : PositiveRatio) (bounded : LE (ofSignedRatio lower.toSignedRatio) one) :
    Equiv (one.positiveLn lower bounded) zero :=
  equiv_trans (mul_congr (positiveLog2_one lower bounded) (equiv_refl lnTwo)) (zero_mul lnTwo)

/-- Natural logarithms recover the argument of the actual Taylor
exponential. The coefficient identity used here was proved by additivity,
effective limits, and derivative uniqueness. -/
theorem positiveLn_exp (x : ConstructiveReal) : Equiv (x.exp.positiveLn x.expLower x.exp_lower) x :=
  equiv_trans (mul_congr (expLog2_value x) (equiv_refl lnTwo))
    (equiv_trans (mul_assoc x RationalLogSecant.limit lnTwo)
      (equiv_trans (mul_congr (equiv_refl x) coefficient_mul_lnTwo) (mul_one x)))

/-- The bit and natural-log conventions have the proved reciprocal units. -/
theorem positiveLog2_from_positiveLn (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) :
    Equiv (x.positiveLog2 lower bounded) (mul (x.positiveLn lower bounded) RationalLogSecant.limit) := by
  have unit : Equiv (mul lnTwo RationalLogSecant.limit) one :=
    equiv_trans (mul_comm lnTwo RationalLogSecant.limit) coefficient_mul_lnTwo
  exact equiv_symm (equiv_trans (mul_assoc (x.positiveLog2 lower bounded) lnTwo RationalLogSecant.limit)
    (equiv_trans (mul_congr (equiv_refl _) unit) (mul_one _)))

/-- The natural-log value of the rational two is the declared conversion
constant. The positivity bound can be supplied in any valid presentation. -/
theorem positiveLn_two (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) (ofSignedRatio (PositiveRatio.ofNat 2 (by decide)).toSignedRatio)) :
    Equiv ((ofSignedRatio (PositiveRatio.ofNat 2 (by decide)).toSignedRatio).positiveLn lower bounded) lnTwo := by
  have binary : Equiv ((ofSignedRatio (PositiveRatio.ofNat 2 (by decide)).toSignedRatio).positiveLog2 lower bounded) one :=
    equiv_trans (positiveLog2_ofPositiveRatio (PositiveRatio.ofNat 2 (by decide)) lower bounded)
      (ExactLog.interpret_ofSignedRatio SignedRatio.one)
  exact equiv_trans (mul_congr binary (equiv_refl lnTwo)) (one_mul lnTwo)


/-- Natural logarithms turn products into sums on their proved positive domains. -/
theorem positiveLn_mul (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv ((mul x y).positiveLn (lowerX.mul lowerY) (mul_positive_lower x y lowerX lowerY boundedX boundedY))
      (add (x.positiveLn lowerX boundedX) (y.positiveLn lowerY boundedY)) :=
  equiv_trans (mul_congr (positiveLog2_mul x y lowerX lowerY boundedX boundedY) (equiv_refl lnTwo)) (add_mul _ _ lnTwo)

theorem positiveLn_quotient (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv ((mul x (y.positiveInverse lowerY boundedY)).positiveLn (lowerX.mul y.positiveInverseLower)
      (mul_positive_lower x _ lowerX y.positiveInverseLower boundedX (y.positiveInverse_lower lowerY boundedY)))
      (sub (x.positiveLn lowerX boundedX) (y.positiveLn lowerY boundedY)) :=
  equiv_trans (mul_congr (positiveLog2_quotient x y lowerX lowerY boundedX boundedY) (equiv_refl lnTwo)) (sub_mul _ _ lnTwo)

/-- Natural-log differentiation has exactly the reciprocal slope. Its units
come from the proved log-exponential connection, and the positive domain
and quantitative modulus are retained from the bit-logarithm derivative. -/
def positiveLn_hasDerivativeWithinAt (point : ConstructiveReal) (lower : PositiveRatio)
    (inside : LE (ofSignedRatio lower.toSignedRatio) point) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) y)
      (fun y admitted => y.positiveLn lower admitted) point inside (point.positiveInverse lower inside) := by
  let inverse := point.positiveInverse lower inside
  let derivative := (positiveLog2_hasDerivativeWithinAt point lower inside).mul_constant lnTwo
  have slope : Equiv (mul (mul RationalLogSecant.limit inverse) lnTwo) inverse :=
    equiv_trans (mul_congr (mul_comm RationalLogSecant.limit inverse) (equiv_refl lnTwo))
      (equiv_trans (mul_assoc inverse RationalLogSecant.limit lnTwo)
        (equiv_trans (mul_congr (equiv_refl inverse) coefficient_mul_lnTwo) (mul_one inverse)))
  exact derivative.slope_congr slope

end Thesis.Probability.ConstructiveReal
