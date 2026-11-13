import Thesis.Probability.ConstructiveRealScaling
import Thesis.Probability.ExactLogEnclosure
import Thesis.Probability.ExactLogRationalArithmetic
import Thesis.Probability.ExactLogSeparation

namespace Thesis.Probability.ExactLog

private theorem rational_order {a b : SignedRatio} (bounded : LE (ofSignedRatio a) (ofSignedRatio b)) : SignedRatio.LE a b :=
  (SignedRatio.le_iff_cross _ _).mpr ((ofSignedRatio_le_iff _ _).mp bounded)

private theorem embed_order {a b : SignedRatio} (bounded : SignedRatio.LE a b) : LE (ofSignedRatio a) (ofSignedRatio b) :=
  (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.le_iff_cross _ _).mp bounded)

private def rationalEnclosure (x : ExactLog) (precision : PositiveRatio) : RationalEnclosure precision := by
  let bracket := x.enclose precision.toQProb precision.num_pos
  let lower : SignedRatio := ⟨bracket.lower, bracket.den, bracket.den_pos⟩
  let upper : SignedRatio := ⟨bracket.lower + (bracket.width : Int), bracket.den, bracket.den_pos⟩
  refine ⟨lower, upper, rational_order (le_trans bracket.lower_bound bracket.upper_bound), ?_⟩
  have width : (bracket.width : Int) * (precision.den : Int) ≤ (precision.num : Int) * (bracket.den : Int) := by
    rw [← Int.natCast_mul, ← Int.natCast_mul, Int.ofNat_le]
    exact Nat.le_of_lt bracket.width_lt
  have multiplied := Int.mul_le_mul_of_nonneg_right width (Int.natCast_nonneg bracket.den)
  apply (SignedRatio.le_iff_cross _ _).mpr
  simp only [lower, upper, SignedRatio.add, PositiveRatio.toSignedRatio, PositiveRatio.toQProb,
    QProb.toSignedRatio, Int.natCast_mul, Int.add_mul, Int.mul_add,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at multiplied ⊢
  omega

/-- Interpret an exact symbolic logarithm by its existing certified rational
bisection algorithm. This constructs a value, rather than postulating semantics. -/
def interpret (x : ExactLog) : ConstructiveReal where
  enclose precision := rationalEnclosure x precision
  coherent first second := rational_order
    (le_trans (x.enclose first.toQProb first.num_pos).lower_bound
      (x.enclose second.toQProb second.num_pos).upper_bound)

theorem interpret_lower (x : ExactLog) (precision : PositiveRatio) :
    LE (ofSignedRatio (x.interpret.enclose precision).lower) x :=
  (x.enclose precision.toQProb precision.num_pos).lower_bound

theorem interpret_upper (x : ExactLog) (precision : PositiveRatio) :
    LE x (ofSignedRatio (x.interpret.enclose precision).upper) :=
  (x.enclose precision.toQProb precision.num_pos).upper_bound

/-- Semantic order is preserved by the computable interpretation. -/
theorem interpret_mono {x y : ExactLog} (bounded : LE x y) : ConstructiveReal.LE x.interpret y.interpret :=
  fun first second => rational_order (le_trans (x.interpret_lower first) (le_trans bounded (y.interpret_upper second)))

theorem interpret_congr {x y : ExactLog} (same : Equiv x y) : ConstructiveReal.Equiv x.interpret y.interpret := by
  have bounds := (equiv_iff_le _ _).mp same
  exact ⟨interpret_mono bounds.1, interpret_mono bounds.2⟩

/-- Rational bits have the same value in both representations. -/
theorem interpret_ofSignedRatio (value : SignedRatio) :
    ConstructiveReal.Equiv (ofSignedRatio value).interpret (ConstructiveReal.ofSignedRatio value) := by
  constructor
  · intro first second
    exact rational_order ((ofSignedRatio value).interpret_lower first)
  · intro first second
    exact rational_order ((ofSignedRatio value).interpret_upper second)

private theorem upper_near (x : ExactLog) (precision : PositiveRatio) :
    LE (ofSignedRatio (x.interpret.enclose precision).upper) (add x (ofSignedRatio precision.toSignedRatio)) := by
  have widened := embed_order (x.interpret.enclose precision).width
  have separated := (le_congr (equiv_refl _) (equiv_symm (ofSignedRatio_add _ _))).mp widened
  exact le_trans separated (add_le_add (x.interpret_lower precision) (le_refl _))

private theorem lower_near (x : ExactLog) (precision : PositiveRatio) :
    LE x (add (ofSignedRatio (x.interpret.enclose precision).lower) (ofSignedRatio precision.toSignedRatio)) := by
  have widened := embed_order (x.interpret.enclose precision).width
  exact le_trans (x.interpret_upper precision)
    ((le_congr (equiv_refl _) (equiv_symm (ofSignedRatio_add _ _))).mp widened)

/-- Arbitrarily small positive rational slack forces exact logarithmic order. -/
theorem le_of_forall_rational_error (x y : ExactLog)
    (bounded : ∀ error : PositiveRatio, LE x (add y (ofSignedRatio error.toSignedRatio))) : LE x y := by
  apply le_of_multiples_le_add_one
  intro n
  cases n with
  | zero =>
      have nonnegative : LE zero (log (PositiveRatio.ofNat 2 (by decide))) := by decide +kernel
      have compared := (add_le_add_right_iff _ _ zero).mpr nonnegative
      rw [add_zero] at compared
      exact (le_congr (equiv_symm (scaleNat_zero _))
        (add_congr (equiv_symm (scaleNat_zero _)) (equiv_refl _))).mp compared
  | succ n =>
      let error : PositiveRatio := ⟨1, n + 1, by decide, Nat.zero_lt_succ n⟩
      have amplified := (scaleNat_le_scaleNat_iff (n + 1) (Nat.zero_lt_succ n) _ _).mpr (bounded error)
      rw [scaleNat_add] at amplified
      have unit : SignedRatio.Equiv (SignedRatio.scaleNat (n + 1) error.toSignedRatio) SignedRatio.one := by
        simp only [SignedRatio.Equiv, SignedRatio.scaleNat, error, PositiveRatio.toSignedRatio,
          PositiveRatio.toQProb, QProb.toSignedRatio, SignedRatio.one, Int.natCast_one, Int.mul_one, Int.one_mul]
      have exactUnit := equiv_trans (scaleNat_ofSignedRatio (n + 1) error.toSignedRatio) (ofSignedRatio_congr unit)
      exact (le_congr (equiv_refl _) (add_congr (equiv_refl _) exactUnit)).mp amplified

/-- The interpretation reflects order as well as preserving it. -/
theorem interpret_le_iff (x y : ExactLog) : ConstructiveReal.LE x.interpret y.interpret ↔ LE x y := by
  constructor
  · intro compared
    apply le_of_forall_rational_error
    intro precision
    have bridge := embed_order (compared precision.half precision.half)
    have first := le_trans (x.lower_near precision.half) (add_le_add bridge (le_refl _))
    have last := le_trans first (add_le_add (y.upper_near precision.half) (le_refl _))
    have collected : Equiv
        (add (add y (ofSignedRatio precision.half.toSignedRatio)) (ofSignedRatio precision.half.toSignedRatio))
        (add y (ofSignedRatio precision.toSignedRatio)) := by
      rw [add_assoc]
      exact add_congr (equiv_refl _)
        (equiv_trans (ofSignedRatio_add _ _) (ofSignedRatio_congr precision.half_add_half))
    exact (le_congr (equiv_refl _) collected).mp last
  · exact interpret_mono

theorem interpret_equiv_iff (x y : ExactLog) : ConstructiveReal.Equiv x.interpret y.interpret ↔ Equiv x y := by
  rw [equiv_iff_le]
  exact ⟨fun same => ⟨(interpret_le_iff _ _).mp same.1, (interpret_le_iff _ _).mp same.2⟩,
    fun same => ⟨interpret_mono same.1, interpret_mono same.2⟩⟩

/-- Addition of exact logarithms agrees with addition of their analytic values. -/
theorem interpret_add (x y : ExactLog) :
    ConstructiveReal.Equiv (add x y).interpret (ConstructiveReal.add x.interpret y.interpret) := by
  constructor
  · intro first second
    apply rational_order
    have bounded := le_trans ((add x y).interpret_lower first)
      (add_le_add (x.interpret_upper second.half) (y.interpret_upper second.half))
    exact (le_congr (equiv_refl _) (ofSignedRatio_add _ _)).mp bounded
  · intro first second
    apply rational_order
    have bounded := le_trans (add_le_add (x.interpret_lower first.half) (y.interpret_lower first.half))
      ((add x y).interpret_upper second)
    exact (le_congr (ofSignedRatio_add _ _) (equiv_refl _)).mp bounded

/-- Real negation and exact logarithmic negation agree. -/
theorem interpret_neg (x : ExactLog) :
    ConstructiveReal.Equiv (neg x).interpret (ConstructiveReal.neg x.interpret) := by
  constructor
  · intro first second
    apply rational_order
    change LE (ofSignedRatio ((neg x).interpret.enclose first).lower)
      (ofSignedRatio (SignedRatio.neg (x.interpret.enclose second).lower))
    rw [ofSignedRatio_neg]
    exact le_trans ((neg x).interpret_lower first)
      ((neg_le_neg_iff _ _).mpr (x.interpret_lower second))
  · intro first second
    apply rational_order
    change LE (ofSignedRatio (SignedRatio.neg (x.interpret.enclose first).upper))
      (ofSignedRatio ((neg x).interpret.enclose second).upper)
    rw [ofSignedRatio_neg]
    exact le_trans ((neg_le_neg_iff _ _).mpr (x.interpret_upper first))
      ((neg x).interpret_upper second)

theorem interpret_listSum (values : List ExactLog) :
    ConstructiveReal.Equiv (listSum values).interpret (ConstructiveReal.listSum (values.map interpret)) := by
  induction values with
  | nil => exact interpret_ofSignedRatio SignedRatio.zero
  | cons value rest ih =>
      exact ConstructiveReal.equiv_trans (interpret_add _ _)
        (ConstructiveReal.add_congr (ConstructiveReal.equiv_refl _) ih)

theorem interpret_scaleNat (n : Nat) (x : ExactLog) :
    ConstructiveReal.Equiv (scaleNat n x).interpret (ConstructiveReal.scaleNat n x.interpret) := by
  induction n with
  | zero =>
      exact ConstructiveReal.equiv_trans (interpret_congr (scaleNat_zero x))
        (interpret_ofSignedRatio SignedRatio.zero)
  | succ n ih =>
      exact ConstructiveReal.equiv_trans (interpret_congr (scaleNat_succ n x))
        (ConstructiveReal.equiv_trans (interpret_add _ _)
          (ConstructiveReal.add_congr ih (ConstructiveReal.equiv_refl _)))

theorem interpret_divideNat (x : ExactLog) (n : Nat) (positive : 0 < n) :
    ConstructiveReal.Equiv (divideNat x n positive).interpret (ConstructiveReal.divideNat x.interpret n positive) := by
  constructor
  · intro first second
    apply rational_order
    change LE (ofSignedRatio ((divideNat x n positive).interpret.enclose first).lower)
      (ofSignedRatio (SignedRatio.divideNat
        (x.interpret.enclose (second.mul (PositiveRatio.ofNat n positive))).upper n positive))
    rw [ofSignedRatio_divideNat]
    exact le_trans ((divideNat x n positive).interpret_lower first)
      ((divideNat_le_divideNat_iff n positive _ _).mpr (x.interpret_upper _))
  · intro first second
    apply rational_order
    change LE (ofSignedRatio (SignedRatio.divideNat
        (x.interpret.enclose (first.mul (PositiveRatio.ofNat n positive))).lower n positive))
      (ofSignedRatio ((divideNat x n positive).interpret.enclose second).upper)
    rw [ofSignedRatio_divideNat]
    exact le_trans ((divideNat_le_divideNat_iff n positive _ _).mpr (x.interpret_lower _))
      ((divideNat x n positive).interpret_upper second)

/-- Every existing exact rational-weight operation has the same analytic value. -/
theorem interpret_scaleRatio (weight : QProb) (x : ExactLog) :
    ConstructiveReal.Equiv (scaleRatio weight x).interpret (ConstructiveReal.scaleRatio weight x.interpret) :=
  ConstructiveReal.equiv_trans (interpret_divideNat (scaleNat weight.num x) weight.den weight.den_pos)
    (ConstructiveReal.divideNat_congr (interpret_scaleNat weight.num x) weight.den weight.den_pos)

end Thesis.Probability.ExactLog
