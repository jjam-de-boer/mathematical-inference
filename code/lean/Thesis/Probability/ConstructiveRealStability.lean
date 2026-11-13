import Thesis.Probability.ConstructiveRealCauchy
import Thesis.Probability.ConstructiveRealMultiplication

namespace Thesis.Probability.ConstructiveReal

/-- A closed rational error bound follows from bounds with every positive
rational slack. No arbitrary real equality or order decision is used. -/
theorem within_of_forall_add_error (error : QProb) (x y : ConstructiveReal)
    (bounded : ∀ precision : PositiveRatio, Within (QProb.add error precision.toQProb) x y) : Within error x y := by
  have collect (z : ConstructiveReal) (precision : PositiveRatio) :
      Equiv (add z (ofSignedRatio (QProb.add error precision.toQProb).toSignedRatio))
        (add (add z (ofSignedRatio error.toSignedRatio)) (ofSignedRatio precision.toSignedRatio)) := by
    rw [QProb.toSignedRatio_add]
    exact equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_add _ _))) (equiv_symm (add_assoc _ _ _))
  constructor
  · apply le_of_forall_rational_error
    intro precision
    exact (le_congr (equiv_refl _) (collect y precision)).mp (bounded precision).1
  · apply le_of_forall_rational_error
    intro precision
    exact (le_congr (equiv_refl _) (collect x precision)).mp (bounded precision).2

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.RegularRationalApproximation

/-- A real error certificate controls cross-errors between any two rational
approximants, including the two advertised approximation radii. -/
theorem error_of_limit_within (first second : RegularRationalApproximation) (error : QProb)
    (bounded : ConstructiveReal.Within error first.limit second.limit) (left right : PositiveRatio) :
    QProb.LE (SignedRatio.sub (first.value left) (second.value right)).magnitude
      (QProb.add error (QProb.add left.toQProb right.toQProb)) := by
  have compared := ConstructiveReal.within_triangle
    (ConstructiveReal.within_triangle (ConstructiveReal.within_symm (first.limit_within left)) bounded)
    (second.limit_within right)
  have reordered : QProb.Equiv (QProb.add (QProb.add left.toQProb error) right.toQProb)
      (QProb.add error (QProb.add left.toQProb right.toQProb)) :=
    QProb.equiv_trans (QProb.add_congr (QProb.add_comm _ _) (QProb.equiv_refl _)) (QProb.add_assoc _ _ _)
  exact QProb.le_congr (QProb.equiv_refl _) reordered ((ConstructiveReal.within_ofSignedRatio_iff _ _ _).mp compared)

/-- Fixed errors survive completion while a fixed multiple of the requested
approximation errors vanishes. The comparison precision is computed. -/
theorem limit_within_of_error_bound (first second : RegularRationalApproximation) (error : QProb) (factor : Nat)
    (bounded : ∀ left right, QProb.LE (SignedRatio.sub (first.value left) (second.value right)).magnitude
      (QProb.add error (QProb.mul (QProb.ofNat factor) (QProb.add left.toQProb right.toQProb)))) :
    ConstructiveReal.Within error first.limit second.limit := by
  apply ConstructiveReal.within_of_forall_add_error
  intro tolerance
  let denominator := 2 * (factor + 1)
  have positive : 0 < denominator := Nat.mul_pos (by decide) (Nat.zero_lt_succ factor)
  let precision := tolerance.divideNat denominator positive
  have middle := (ConstructiveReal.within_ofSignedRatio_iff _ _ _).mpr (bounded precision precision)
  have combined := ConstructiveReal.within_triangle
    (ConstructiveReal.within_triangle (first.limit_within precision) middle)
    (ConstructiveReal.within_symm (second.limit_within precision))
  have regrouped : QProb.Equiv
      (QProb.add (QProb.add precision.toQProb
        (QProb.add error (QProb.mul (QProb.ofNat factor) (QProb.add precision.toQProb precision.toQProb)))) precision.toQProb)
      (QProb.add error (QProb.mul precision.toQProb (QProb.ofNat denominator))) := by
    simp only [denominator, QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat,
      Nat.mul_one, Nat.one_mul, Nat.two_mul, Nat.mul_two, Nat.mul_add, Nat.add_mul]
    ac_rfl
  have same := QProb.equiv_trans regrouped (QProb.add_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul tolerance denominator positive))
  exact ConstructiveReal.within_mono combined (QProb.le_congr (QProb.equiv_refl _) same (QProb.le_refl _))

/-- Product perturbations have an explicit certified Lipschitz bound from
computable bounds on the rational approximants. -/
theorem product_within_bounded (a b c d : RegularRationalApproximation) (firstError secondError : QProb) (firstSize secondSize : Nat)
    (first : ConstructiveReal.Within firstError a.limit c.limit)
    (second : ConstructiveReal.Within secondError b.limit d.limit)
    (firstBounded : ∀ precision, PositiveRatio.LE precision PositiveRatio.one → QProb.LE (c.value precision).magnitude (QProb.ofNat firstSize))
    (secondBounded : ∀ precision, PositiveRatio.LE precision PositiveRatio.one → QProb.LE (b.value precision).magnitude (QProb.ofNat secondSize)) :
    ConstructiveReal.Within
      (QProb.add (QProb.mul firstError (QProb.ofNat secondSize))
        (QProb.mul (QProb.ofNat firstSize) secondError))
      (a.product b).limit (c.product d).limit := by
  apply limit_within_of_error_bound _ _ _ (secondSize + firstSize)
  intro left right
  let p := productPrecision a b left
  let q := productPrecision c d right
  let extra := QProb.add left.toQProb right.toQProb
  have firstBound : QProb.LE (SignedRatio.sub (a.value p) (c.value q)).magnitude (QProb.add firstError extra) :=
    QProb.le_trans (error_of_limit_within a c firstError first p q)
      (QProb.add_le_add (QProb.le_refl _) (QProb.add_le_add (productPrecision_le a b left) (productPrecision_le c d right)))
  have secondBound : QProb.LE (SignedRatio.sub (b.value p) (d.value q)).magnitude (QProb.add secondError extra) :=
    QProb.le_trans (error_of_limit_within b d secondError second p q)
      (QProb.add_le_add (QProb.le_refl _) (QProb.add_le_add (productPrecision_le a b left) (productPrecision_le c d right)))
  have productBound := SignedRatio.product_error_bound (a.value p) (b.value p) (c.value q) (d.value q)
    (QProb.add firstError extra) (QProb.add secondError extra) (QProb.ofNat firstSize) (QProb.ofNat secondSize)
    firstBound secondBound (firstBounded q (productPrecision_le_one c d right))
    (secondBounded p (productPrecision_le_one a b left))
  have collect : QProb.Equiv
      (QProb.add (QProb.mul (QProb.add firstError extra) (QProb.ofNat secondSize))
        (QProb.mul (QProb.ofNat firstSize) (QProb.add secondError extra)))
      (QProb.add (QProb.add (QProb.mul firstError (QProb.ofNat secondSize))
        (QProb.mul (QProb.ofNat firstSize) secondError))
        (QProb.mul (QProb.ofNat (secondSize + firstSize)) extra)) := by
    simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat, Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.add_mul]
    ac_rfl
  exact QProb.le_congr (QProb.equiv_refl _) collect productBound

/-- A version with automatically computed natural bounds. -/
theorem product_within (a b c d : RegularRationalApproximation) (firstError secondError : QProb)
    (first : ConstructiveReal.Within firstError a.limit c.limit)
    (second : ConstructiveReal.Within secondError b.limit d.limit) :
    ConstructiveReal.Within
      (QProb.add (QProb.mul firstError (QProb.ofNat b.magnitudeBound))
        (QProb.mul (QProb.ofNat c.magnitudeBound) secondError))
      (a.product b).limit (c.product d).limit :=
  product_within_bounded a b c d firstError secondError c.magnitudeBound b.magnitudeBound first second
    c.magnitude_bounded b.magnitude_bounded

/-- Real values within one unit have uniformly bounded fine rational
approximants. The bound uses only the fixed comparison presentation, so
unreduced numerators in the varying presentations do not affect it. -/
theorem magnitude_bounded_near (first second : RegularRationalApproximation)
    (near : ConstructiveReal.Within QProb.one first.limit second.limit)
    (precision : PositiveRatio) (small : PositiveRatio.LE precision PositiveRatio.one) :
    QProb.LE (first.value precision).magnitude (QProb.ofNat (second.magnitudeBound + 3)) := by
  have errors := error_of_limit_within first second QProb.one near precision PositiveRatio.one
  have three : QProb.LE
      (QProb.add QProb.one (QProb.add precision.toQProb PositiveRatio.one.toQProb)) (QProb.ofNat 3) :=
    QProb.le_congr (QProb.equiv_refl _) (by decide +kernel)
      (QProb.add_le_add (QProb.le_refl _) (QProb.add_le_add small (QProb.le_refl _)))
  have triangle := SignedRatio.magnitude_add (SignedRatio.sub (first.value precision) (second.value PositiveRatio.one))
    (second.value PositiveRatio.one)
  have bounded := QProb.le_trans triangle (QProb.add_le_add (QProb.le_trans errors three)
    (second.magnitude_bounded PositiveRatio.one (PositiveRatio.le_refl _)))
  have same : QProb.Equiv (QProb.add (QProb.ofNat 3) (QProb.ofNat second.magnitudeBound))
      (QProb.ofNat (second.magnitudeBound + 3)) := by
    simp only [QProb.Equiv, QProb.add, QProb.ofNat, Nat.mul_one]
    omega
  exact QProb.le_congr (SignedRatio.magnitude_congr (SignedRatio.sub_add_cancel _ _)) same bounded

end Thesis.Probability.RegularRationalApproximation

namespace Thesis.Probability.ConstructiveReal

/-- Supplied rational approximation bounds give a presentation-independent
choice of error constants, useful for whole effective sequences. -/
theorem mul_within_bounded {a b c d : ConstructiveReal} (firstError secondError : QProb) (firstSize secondSize : Nat)
    (first : Within firstError a c) (second : Within secondError b d)
    (firstBounded : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (c.rationalApproximation.value precision).magnitude (QProb.ofNat firstSize))
    (secondBounded : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (b.rationalApproximation.value precision).magnitude (QProb.ofNat secondSize)) :
    Within (QProb.add (QProb.mul firstError (QProb.ofNat secondSize)) (QProb.mul (QProb.ofNat firstSize) secondError))
      (mul a b) (mul c d) :=
  RegularRationalApproximation.product_within_bounded _ _ _ _ firstError secondError firstSize secondSize
    ((within_congr a.rationalApproximation_limit c.rationalApproximation_limit).mpr first)
    ((within_congr b.rationalApproximation_limit d.rationalApproximation_limit).mpr second) firstBounded secondBounded

/-- Certified continuity of the constructed real multiplication. The natural
constants are computed from finite rational enclosures of the supplied inputs. -/
theorem mul_within {a b c d : ConstructiveReal} (firstError secondError : QProb)
    (first : Within firstError a c) (second : Within secondError b d) :
    Within
      (QProb.add (QProb.mul firstError (QProb.ofNat b.rationalApproximation.magnitudeBound))
        (QProb.mul (QProb.ofNat c.rationalApproximation.magnitudeBound) secondError))
      (mul a b) (mul c d) :=
  RegularRationalApproximation.product_within _ _ _ _ firstError secondError
    ((within_congr a.rationalApproximation_limit c.rationalApproximation_limit).mpr first)
    ((within_congr b.rationalApproximation_limit d.rationalApproximation_limit).mpr second)

end Thesis.Probability.ConstructiveReal
