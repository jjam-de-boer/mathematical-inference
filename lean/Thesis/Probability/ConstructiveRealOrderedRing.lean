import Thesis.Probability.ConstructiveRealRing
import Thesis.Probability.ConstructiveRealCauchy

namespace Thesis.Probability.SignedRatio

theorem zero_le_iff_nonnegative (value : SignedRatio) : LE zero value ↔ Nonnegative value := by
  rw [le_iff_cross]
  simp only [zero, Int.zero_mul, Int.natCast_one, Int.mul_one, Nonnegative]

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.ConstructiveReal

/-- Clamp a rational endpoint, rather than deciding the sign of a real. -/
def nonnegativeCenter (x : ConstructiveReal) (precision : PositiveRatio) : SignedRatio :=
  if SignedRatio.LE SignedRatio.zero (x.enclose precision).lower then (x.enclose precision).lower else SignedRatio.zero

theorem nonnegativeCenter_nonnegative (x : ConstructiveReal) (precision : PositiveRatio) :
    SignedRatio.LE SignedRatio.zero (x.nonnegativeCenter precision) := by
  unfold nonnegativeCenter
  split
  · assumption
  · exact SignedRatio.le_refl _

/-- Clamping does not worsen the endpoint error for a nonnegative real.
The hypothesis is a proof, not a decidable sign test on that real. -/
theorem nonnegativeCenter_within (x : ConstructiveReal) (nonnegative : LE zero x) (precision : PositiveRatio) :
    Within precision.toQProb x (ofSignedRatio (x.nonnegativeCenter precision)) := by
  have original := x.lower_within precision
  by_cases positive : SignedRatio.LE SignedRatio.zero (x.enclose precision).lower
  · simpa only [nonnegativeCenter, if_pos positive] using original
  · have below := (SignedRatio.le_total SignedRatio.zero (x.enclose precision).lower).resolve_left positive
    have lowered := add_le_add ((ofSignedRatio_le_iff _ _).mpr below)
      (le_refl (ofSignedRatio precision.toSignedRatio))
    have raised := le_trans nonnegative (within_refl precision.toQProb x).1
    simpa only [nonnegativeCenter, if_neg positive] using
      (show Within precision.toQProb x zero from ⟨le_trans original.1 lowered, raised⟩)

/-- A nonnegative real has a regular net of nonnegative rational values. -/
def nonnegativeApproximation (x : ConstructiveReal) (nonnegative : LE zero x) : RegularRationalApproximation where
  value := x.nonnegativeCenter
  regular first second :=
    ((SignedRatio.magnitude_sub_le_iff _ _ _).mp ((within_ofSignedRatio_iff _ _ _).mp
      (within_triangle (within_symm (x.nonnegativeCenter_within nonnegative first))
        (x.nonnegativeCenter_within nonnegative second)))).1

theorem nonnegativeApproximation_limit (x : ConstructiveReal) (nonnegative : LE zero x) :
    Equiv (x.nonnegativeApproximation nonnegative).limit x :=
  (x.nonnegativeApproximation nonnegative).limit_unique_within x (x.nonnegativeCenter_within nonnegative)

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.RegularRationalApproximation

/-- Closed nonnegativity passes to a computed regular-net limit. -/
theorem limit_nonnegative (approximation : RegularRationalApproximation)
    (nonnegative : ∀ precision, SignedRatio.LE SignedRatio.zero (approximation.value precision)) :
    ConstructiveReal.LE ConstructiveReal.zero approximation.limit := by
  apply ConstructiveReal.le_of_forall_rational_error
  intro precision
  exact ConstructiveReal.le_trans ((ConstructiveReal.ofSignedRatio_le_iff _ _).mpr (nonnegative precision))
    (approximation.limit_within precision).2

end Thesis.Probability.RegularRationalApproximation

namespace Thesis.Probability.ConstructiveReal

/-- The computed real multiplication preserves nonnegativity without a
case split on either real input. -/
theorem mul_nonnegative {x y : ConstructiveReal} (first : LE zero x) (second : LE zero y) : LE zero (mul x y) := by
  let a := x.nonnegativeApproximation first
  let b := y.nonnegativeApproximation second
  have productPositive : LE zero (a.product b).limit := by
    apply RegularRationalApproximation.limit_nonnegative
    intro precision
    apply (SignedRatio.zero_le_iff_nonnegative _).mpr
    exact SignedRatio.nonnegative_mul
      ((SignedRatio.zero_le_iff_nonnegative _).mp (x.nonnegativeCenter_nonnegative _))
      ((SignedRatio.zero_le_iff_nonnegative _).mp (y.nonnegativeCenter_nonnegative _))
  have same : Equiv (mul x y) (a.product b).limit :=
    RegularRationalApproximation.product_congr _ _ _ _
      (equiv_trans x.rationalApproximation_limit (equiv_symm (x.nonnegativeApproximation_limit first)))
      (equiv_trans y.rationalApproximation_limit (equiv_symm (y.nonnegativeApproximation_limit second)))
  exact (le_congr (equiv_refl _) same).mpr productPositive

/-- Multiplication by a nonnegative factor preserves closed order. -/
theorem mul_le_mul_nonnegative {a b factor : ConstructiveReal} (positive : LE zero factor) (compared : LE a b) :
    LE (mul factor a) (mul factor b) := by
  have differencePositive := mul_nonnegative positive ((zero_le_sub_iff b a).mpr compared)
  have distributed := (le_congr (equiv_refl zero) (mul_sub factor b a)).mp differencePositive
  exact (zero_le_sub_iff _ _).mp distributed

theorem mul_le_mul_nonnegative_right {a b factor : ConstructiveReal} (positive : LE zero factor) (compared : LE a b) :
    LE (mul a factor) (mul b factor) :=
  (le_congr (mul_comm _ _) (mul_comm _ _)).mp (mul_le_mul_nonnegative positive compared)

theorem mul_le_mul {a b c d : ConstructiveReal} (first : LE a b) (second : LE c d)
    (leftPositive : LE zero a) (rightPositive : LE zero d) : LE (mul a c) (mul b d) :=
  le_trans (mul_le_mul_nonnegative leftPositive second) (mul_le_mul_nonnegative_right rightPositive first)

/-- A square is nonnegative for every real presentation, without deciding
whether that real is nonnegative or nonpositive. -/
theorem square_nonnegative (x : ConstructiveReal) : LE zero (mul x x) := by
  apply RegularRationalApproximation.limit_nonnegative
  intro precision
  exact (SignedRatio.zero_le_iff_nonnegative _).mpr (SignedRatio.nonnegative_square _)

/-- Squaring preserves order for nonnegative inputs. -/
theorem square_le_square {a b : ConstructiveReal} (positive : LE zero a) (compared : LE a b) :
    LE (mul a a) (mul b b) := mul_le_mul compared compared positive (le_trans positive compared)

/-- Every natural power of a nonnegative real is nonnegative. -/
theorem pow_nonnegative {x : ConstructiveReal} (positive : LE zero x) (n : Nat) : LE zero (pow x n) := by
  induction n with
  | zero => exact (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  | succ n ih => exact mul_nonnegative ih positive

theorem pow_mono {x y : ConstructiveReal} (positive : LE zero x) (compared : LE x y) (n : Nat) :
    LE (pow x n) (pow y n) := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact mul_le_mul ih compared (pow_nonnegative positive n) (le_trans positive compared)

theorem listSum_nonnegative (values : List ConstructiveReal) (positive : ∀ value ∈ values, LE zero value) :
    LE zero (listSum values) := by
  induction values with
  | nil => exact le_refl _
  | cons value rest ih =>
      have bounded := add_le_add (positive value (List.mem_cons_self ..))
        (ih (fun other member => positive other (List.mem_cons_of_mem _ member)))
      exact (le_congr (zero_add zero) (equiv_refl _)).mp bounded

end Thesis.Probability.ConstructiveReal
