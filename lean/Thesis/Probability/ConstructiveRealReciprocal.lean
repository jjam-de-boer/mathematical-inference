import Thesis.Probability.ConstructiveRealOrderedRing
import Thesis.Probability.RationalReciprocal

namespace Thesis.Probability.ConstructiveReal

private def positiveEndpoint (x : ConstructiveReal) (lower : PositiveRatio) (precision : PositiveRatio) : SignedRatio :=
  if SignedRatio.LE lower.toSignedRatio (x.enclose precision).lower then (x.enclose precision).lower else lower.toSignedRatio

private theorem endpoint_lower (x : ConstructiveReal) (lower : PositiveRatio) (precision : PositiveRatio) :
    SignedRatio.LE lower.toSignedRatio (positiveEndpoint x lower precision) := by
  unfold positiveEndpoint
  split
  · assumption
  · exact SignedRatio.le_refl _

/-- A strictly positive rational approximation, computed by comparison of
rational endpoints with the supplied positive lower bound. -/
def positiveCenter (x : ConstructiveReal) (lower : PositiveRatio) (precision : PositiveRatio) : PositiveRatio :=
  PositiveRatio.ofSignedPositive (positiveEndpoint x lower precision)
    (SignedRatio.positive_of_lower lower _ (endpoint_lower x lower precision))

private theorem positiveCenter_value (x : ConstructiveReal) (lower : PositiveRatio) (precision : PositiveRatio) :
    SignedRatio.Equiv (x.positiveCenter lower precision).toSignedRatio (positiveEndpoint x lower precision) :=
  PositiveRatio.ofSignedPositive_value _ _

theorem positiveCenter_lower (x : ConstructiveReal) (lower : PositiveRatio) (precision : PositiveRatio) :
    PositiveRatio.LE lower (x.positiveCenter lower precision) := by
  apply (SignedRatio.toSignedRatio_le_iff _ _).mp
  exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm (positiveCenter_value _ _ _))).mp
    (endpoint_lower x lower precision)

theorem positiveCenter_within (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (precision : PositiveRatio) :
    Within precision.toQProb x (ofSignedRatio (x.positiveCenter lower precision).toSignedRatio) := by
  apply (within_congr (equiv_refl _) ((ofSignedRatio_equiv_iff _ _).mpr (positiveCenter_value _ _ _))).mpr
  have original := x.lower_within precision
  by_cases positive : SignedRatio.LE lower.toSignedRatio (x.enclose precision).lower
  · simpa only [positiveEndpoint, if_pos positive] using original
  · have below := (SignedRatio.le_total lower.toSignedRatio (x.enclose precision).lower).resolve_left positive
    have lowered := add_le_add ((ofSignedRatio_le_iff _ _).mpr below) (le_refl (ofSignedRatio precision.toSignedRatio))
    have raised := le_trans bounded (within_refl precision.toQProb x).1
    simpa only [positiveEndpoint, if_neg positive] using
      (show Within precision.toQProb x (ofSignedRatio lower.toSignedRatio) from ⟨le_trans original.1 lowered, raised⟩)

/-- The clamped center is still below the real value: both the rational
endpoint and the supplied lower bound are valid lower bounds. -/
theorem positiveCenter_le (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (precision : PositiveRatio) :
    LE (ofSignedRatio (x.positiveCenter lower precision).toSignedRatio) x := by
  apply (le_congr ((ofSignedRatio_equiv_iff _ _).mpr (positiveCenter_value _ _ _)) (equiv_refl _)).mpr
  unfold positiveEndpoint
  split
  · exact x.lower_bound precision
  · exact bounded

/-- Exact rational inputs give the same positive center value at every
precision, independently of unreduced fraction presentations. -/
theorem positiveCenter_ofPositiveRatio (value lower precision : PositiveRatio) (bounded : PositiveRatio.LE lower value) :
    PositiveRatio.Equiv ((ofSignedRatio value.toSignedRatio).positiveCenter lower precision) value := by
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  have compared : SignedRatio.LE lower.toSignedRatio value.toSignedRatio := (SignedRatio.toSignedRatio_le_iff _ _).mpr bounded
  simpa only [positiveEndpoint, ofSignedRatio, if_pos compared] using
    positiveCenter_value (ofSignedRatio value.toSignedRatio) lower precision

/-- A real above a given positive rational has a regular positive rational
presentation with the same certified error radius. -/
def positiveApproximation (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : RegularRationalApproximation where
  value precision := (x.positiveCenter lower precision).toSignedRatio
  regular first second :=
    ((SignedRatio.magnitude_sub_le_iff _ _ _).mp ((within_ofSignedRatio_iff _ _ _).mp
      (within_triangle (within_symm (x.positiveCenter_within lower bounded first))
        (x.positiveCenter_within lower bounded second)))).1

theorem positiveApproximation_limit (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : Equiv (x.positiveApproximation lower bounded).limit x :=
  (x.positiveApproximation lower bounded).limit_unique_within x (x.positiveCenter_within lower bounded)

/-- Refining by the square of a computable inverse bound makes reciprocal
rational approximants regular at the requested output precision. -/
def reciprocalApproximation (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : RegularRationalApproximation where
  value precision := (x.positiveCenter lower (precision.divideNat (lower.den * lower.den) (Nat.mul_pos lower.den_pos lower.den_pos))).inv.toSignedRatio
  regular first second := by
    let factor := lower.den * lower.den
    have positive : 0 < factor := Nat.mul_pos lower.den_pos lower.den_pos
    let p := first.divideNat factor positive
    let q := second.divideNat factor positive
    have errors := (x.positiveApproximation lower bounded).error_bound p q
    have inverses := PositiveRatio.inverse_error_bound lower (x.positiveCenter lower p) (x.positiveCenter lower q)
      (x.positiveCenter_lower lower p) (x.positiveCenter_lower lower q)
    have scaled := QProb.le_trans inverses (QProb.mul_le_mul errors (QProb.le_refl (QProb.ofNat factor)))
    have collect := QProb.equiv_trans (QProb.add_mul_distrib p.toQProb q.toQProb (QProb.ofNat factor))
      (QProb.add_congr (PositiveRatio.divide_mul first factor positive) (PositiveRatio.divide_mul second factor positive))
    exact ((SignedRatio.magnitude_sub_le_iff _ _ _).mp
      (QProb.le_congr (QProb.equiv_refl _) collect scaled)).1

/-- Reciprocal on an explicitly positive domain. The bound is computational
input; no decision of arbitrary real equality with zero is required. -/
def positiveInverse (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : ConstructiveReal := (x.reciprocalApproximation lower bounded).limit

theorem positiveInverse_nonnegative (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : LE zero (x.positiveInverse lower bounded) := by
  apply RegularRationalApproximation.limit_nonnegative
  intro precision
  exact (SignedRatio.zero_le_iff_nonnegative _).mpr (PositiveRatio.signed_nonnegative _)

/-- Every requested reciprocal approximant has the advertised real error. -/
theorem positiveInverse_within (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (precision : PositiveRatio) :
    Within precision.toQProb (x.positiveInverse lower bounded)
      (ofSignedRatio ((x.reciprocalApproximation lower bounded).value precision)) :=
  (x.reciprocalApproximation lower bounded).limit_within precision

/-- The computed reciprocal satisfies its defining algebraic equation. -/
theorem mul_positiveInverse (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : Equiv (mul x (x.positiveInverse lower bounded)) one := by
  let a := x.positiveApproximation lower bounded
  let b := x.reciprocalApproximation lower bounded
  have inverseProduct : Equiv (a.product b).limit one.rationalApproximation.limit := by
    apply RegularRationalApproximation.limit_equiv_of_error_bound _ _ (2 * lower.den)
    intro left right
    let p := RegularRationalApproximation.productPrecision a b left
    let q := p.divideNat (lower.den * lower.den) (Nat.mul_pos lower.den_pos lower.den_pos)
    let c := x.positiveCenter lower p
    let d := x.positiveCenter lower q
    have canceled : SignedRatio.Equiv
        (SignedRatio.sub (SignedRatio.mul c.toSignedRatio d.inv.toSignedRatio) SignedRatio.one)
        (SignedRatio.mul (SignedRatio.sub c.toSignedRatio d.toSignedRatio) d.inv.toSignedRatio) :=
      SignedRatio.equiv_symm (SignedRatio.equiv_trans (SignedRatio.sub_mul _ _ _)
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.neg_congr (PositiveRatio.signed_mul_inv d))))
    have errors := a.error_bound p q
    have larger : QProb.LE left.toQProb (QProb.add left.toQProb right.toQProb) :=
      QProb.le_congr (QProb.add_zero _) (QProb.equiv_refl _) (QProb.add_le_add (QProb.le_refl _) (QProb.zero_le _))
    have pBound : QProb.LE p.toQProb (QProb.add left.toQProb right.toQProb) :=
      QProb.le_trans (RegularRationalApproximation.productPrecision_le a b left) larger
    have qBound : QProb.LE q.toQProb (QProb.add left.toQProb right.toQProb) :=
      QProb.le_trans (PositiveRatio.divideNat_le p _ _) pBound
    have inverseSize : QProb.LE d.inv.toSignedRatio.magnitude (QProb.ofNat lower.den) :=
      QProb.le_congr (QProb.equiv_symm (PositiveRatio.signed_magnitude _)) (QProb.equiv_refl _)
        (PositiveRatio.inverse_bound lower d (x.positiveCenter_lower lower q))
    have productBound := QProb.mul_le_mul (QProb.le_trans errors (QProb.add_le_add pBound qBound)) inverseSize
    have collect : QProb.Equiv
        (QProb.mul (QProb.add (QProb.add left.toQProb right.toQProb) (QProb.add left.toQProb right.toQProb)) (QProb.ofNat lower.den))
        (QProb.mul (QProb.ofNat (2 * lower.den)) (QProb.add left.toQProb right.toQProb)) := by
      simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat, Nat.mul_one, Nat.one_mul, Nat.two_mul, Nat.mul_add, Nat.add_mul]
      ac_rfl
    exact QProb.le_congr
      (QProb.equiv_symm (QProb.equiv_trans (SignedRatio.magnitude_congr canceled) (SignedRatio.magnitude_mul _ _))) collect productBound
  have aligned : Equiv (mul x (x.positiveInverse lower bounded)) (a.product b).limit :=
    RegularRationalApproximation.product_congr _ _ _ _
      (equiv_trans x.rationalApproximation_limit (equiv_symm (x.positiveApproximation_limit lower bounded)))
      ((x.positiveInverse lower bounded).rationalApproximation_limit)
  exact equiv_trans aligned (equiv_trans inverseProduct one.rationalApproximation_limit)

/-- An inverse is unique by ring algebra, independently of the lower bound
or rational endpoint presentation used in its computation. -/
theorem inverse_unique (x y z : ConstructiveReal) (first : Equiv (mul x y) one) (second : Equiv (mul x z) one) : Equiv y z :=
  equiv_trans (equiv_symm (mul_one y))
    (equiv_trans (mul_congr (equiv_refl _) (equiv_symm second))
      (equiv_trans (equiv_symm (mul_assoc _ _ _))
        (equiv_trans (mul_congr (equiv_trans (mul_comm _ _) first) (equiv_refl _)) (one_mul z))))

theorem positiveInverse_congr {x y : ConstructiveReal} (same : Equiv x y) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv (x.positiveInverse lowerX boundedX) (y.positiveInverse lowerY boundedY) :=
  inverse_unique x _ _ (mul_positiveInverse x lowerX boundedX)
    (equiv_trans (mul_congr same (equiv_refl _)) (mul_positiveInverse y lowerY boundedY))

/-- Agreement with exact rational reciprocals, for any valid domain witness. -/
theorem ofPositiveRatio_inverse (value lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) (ofSignedRatio value.toSignedRatio)) :
    Equiv ((ofSignedRatio value.toSignedRatio).positiveInverse lower bounded) (ofSignedRatio value.inv.toSignedRatio) :=
  inverse_unique _ _ _ (mul_positiveInverse _ _ _) (equiv_trans (ofSignedRatio_mul _ _)
    ((ofSignedRatio_equiv_iff _ _).mpr (PositiveRatio.signed_mul_inv value)))

/-- Multiplication by an explicitly positive real preserves and reflects
closed order. Reflection uses its computed reciprocal. -/
theorem mul_le_mul_positive_iff (factor : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) factor) (a b : ConstructiveReal) :
    LE (mul factor a) (mul factor b) ↔ LE a b := by
  have factorPositive : LE zero factor := le_trans
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr lower.signed_nonnegative)) bounded
  constructor
  · intro compared
    have multiplied := mul_le_mul_nonnegative (positiveInverse_nonnegative factor lower bounded) compared
    have cancel (value : ConstructiveReal) : Equiv (mul (factor.positiveInverse lower bounded) (mul factor value)) value :=
      equiv_trans (equiv_symm (mul_assoc _ _ _))
        (equiv_trans (mul_congr (equiv_trans (mul_comm _ _) (mul_positiveInverse factor lower bounded)) (equiv_refl _)) (one_mul value))
    exact (le_congr (cancel a) (cancel b)).mp multiplied
  · intro compared
    exact mul_le_mul_nonnegative factorPositive compared

/-- Reciprocal reverses order on explicitly positive real arguments. -/
theorem positiveInverse_antitone (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y)
    (compared : LE x y) : LE (y.positiveInverse lowerY boundedY) (x.positiveInverse lowerX boundedX) := by
  let ix := x.positiveInverse lowerX boundedX
  let iy := y.positiveInverse lowerY boundedY
  have multiplied := mul_le_mul_nonnegative (positiveInverse_nonnegative y lowerY boundedY)
    (mul_le_mul_nonnegative (positiveInverse_nonnegative x lowerX boundedX) compared)
  have left : Equiv (mul iy (mul ix x)) iy :=
    equiv_trans (mul_congr (equiv_refl _) (equiv_trans (mul_comm _ _) (mul_positiveInverse x lowerX boundedX))) (mul_one iy)
  have right : Equiv (mul iy (mul ix y)) ix :=
    equiv_trans (equiv_symm (mul_assoc _ _ _))
      (equiv_trans (mul_congr (mul_comm _ _) (equiv_refl _))
        (equiv_trans (mul_assoc _ _ _)
          (equiv_trans (mul_congr (equiv_refl _) (equiv_trans (mul_comm _ _) (mul_positiveInverse y lowerY boundedY))) (mul_one ix))))
  exact (le_congr left right).mp multiplied

/-- The same natural reciprocal bound used by the algorithm is a bound on
the resulting real value. -/
theorem positiveInverse_upper (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) :
    LE (x.positiveInverse lower bounded) (ofSignedRatio (QProb.ofNat lower.den).toSignedRatio) := by
  apply le_of_forall_rational_error
  intro precision
  have centerBound : LE (ofSignedRatio ((x.reciprocalApproximation lower bounded).value precision))
      (ofSignedRatio (QProb.ofNat lower.den).toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr
      (PositiveRatio.inverse_bound lower _ (x.positiveCenter_lower lower _)))
  exact le_trans (x.positiveInverse_within lower bounded precision).1
    (add_le_add centerBound (le_refl _))

end Thesis.Probability.ConstructiveReal
