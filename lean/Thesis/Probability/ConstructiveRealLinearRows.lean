import Thesis.Probability.ConstructiveRealKernelElimination
import Thesis.Probability.ConstructiveRealLattice
import Thesis.Probability.ConstructiveRealReciprocal

namespace Thesis.Probability.ConstructiveReal

private theorem difference_add_cancel (first second : ConstructiveReal) : Equiv (add (sub first second) second) first :=
  equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _)
    (equiv_trans (add_comm _ _) (add_neg second))) (add_zero first))

theorem add_le_iff_le_sub (first second upper : ConstructiveReal) :
    LE (add first second) upper ↔ LE first (sub upper second) :=
  (le_congr (equiv_refl _) (equiv_symm (difference_add_cancel upper second))).trans
    (add_le_add_right_iff first (sub upper second) second)

theorem neg_le_iff_nonnegative_add (first second : ConstructiveReal) :
    LE (neg first) second ↔ LE zero (add second first) :=
  (zero_le_sub_iff second (neg first)).symm.trans (le_congr (equiv_refl _) (add_congr (equiv_refl _) (neg_neg first)))

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal
open Distros.RationalLinear

/-- Fixed integral coefficient rows with auxiliary analytic right-hand
sides. Real row satisfaction is a proposition, with no decision instance. -/
structure Inequality (variables : Nat) where
  coefficients : Fin variables → Int
  bound : ConstructiveReal

def Inequality.Holds (row : Inequality variables) (values : Fin variables → ConstructiveReal) : Prop :=
  LE (realDot variables row.coefficients values) row.bound

def Satisfies (rows : List (Inequality variables)) (values : Fin variables → ConstructiveReal) : Prop :=
  ∀ row ∈ rows, row.Holds values

def Inequality.pivot (row : Inequality (variables + 1)) : Int := row.coefficients (Fin.last variables)
def Inequality.trim (row : Inequality (variables + 1)) : Inequality variables := ⟨fun i => row.coefficients i.castSucc, row.bound⟩
def Inequality.residual (row : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal) : ConstructiveReal :=
  sub row.bound (realDot variables row.trim.coefficients values)

/-- Reciprocal of a known positive integer coefficient. No analytic inverse
or search for a nonzero coefficient is needed. -/
def integerInverse (coefficient : Int) (positive : 0 < coefficient) : ConstructiveReal :=
  ofSignedRatio ⟨1, coefficient.toNat, by omega⟩

theorem integer_mul_inverse (coefficient : Int) (positive : 0 < coefficient) :
    Equiv (mul (realInteger coefficient) (integerInverse coefficient positive)) one := by
  apply equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr ?_)
  have cast : (coefficient.toNat : Int) = coefficient := Int.toNat_of_nonneg (by omega)
  simp only [SignedRatio.Equiv, SignedRatio.mul, SignedRatio.one, Int.natCast_one, Int.mul_one, Int.one_mul,
    Nat.one_mul, cast]

theorem integer_inverse_cancel (coefficient : Int) (positive : 0 < coefficient) (value : ConstructiveReal) :
    Equiv (mul (realInteger coefficient) (mul (integerInverse coefficient positive) value)) value :=
  equiv_trans (equiv_symm (mul_assoc _ _ _))
    (equiv_trans (mul_congr (integer_mul_inverse coefficient positive) (equiv_refl _)) (one_mul value))

def integerLower (coefficient : Int) (positive : 0 < coefficient) : PositiveRatio := .ofNat coefficient.toNat (by omega)

theorem integerLower_le (coefficient : Int) (positive : 0 < coefficient) :
    LE (ofSignedRatio (integerLower coefficient positive).toSignedRatio) (realInteger coefficient) := by
  apply (ofSignedRatio_le_iff _ _).mpr
  have cast : (coefficient.toNat : Int) = coefficient := Int.toNat_of_nonneg (by omega)
  change SignedRatio.LE ⟨(coefficient.toNat : Int), 1, by decide⟩ ⟨coefficient, 1, by decide⟩
  rw [cast]
  exact SignedRatio.le_refl _

theorem positive_scale_le_iff (coefficient : Int) (positive : 0 < coefficient) (value upper : ConstructiveReal) :
    LE (mul (realInteger coefficient) value) upper ↔ LE value (mul (integerInverse coefficient positive) upper) :=
  (le_congr (equiv_refl _) (equiv_symm (integer_inverse_cancel coefficient positive upper))).trans
    (mul_le_mul_positive_iff (realInteger coefficient) (integerLower coefficient positive) (integerLower_le coefficient positive) _ _)

def Inequality.upperValue (row : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal) : ConstructiveReal :=
  if positive : 0 < row.pivot then mul (integerInverse row.pivot positive) (row.residual values) else zero

def Inequality.lowerValue (row : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal) : ConstructiveReal :=
  if negative : row.pivot < 0 then mul (integerInverse (-row.pivot) (by omega)) (neg (row.residual values)) else zero

theorem Inequality.holds_extend_iff (row : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal) (last : ConstructiveReal) :
    row.Holds (FiniteLinear.extend values last) ↔ LE (mul (realInteger row.pivot) last) (row.residual values) :=
  (le_congr (IntegerRowSpace.realDot_extend variables row.coefficients values last) (equiv_refl _)).trans (add_le_iff_le_sub _ _ _)

theorem Inequality.holds_upper_iff (row : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal)
    (last : ConstructiveReal) (positive : 0 < row.pivot) :
    row.Holds (FiniteLinear.extend values last) ↔ LE last (row.upperValue values) := by
  rw [row.holds_extend_iff]
  simp only [Inequality.upperValue, dif_pos positive]
  exact positive_scale_le_iff row.pivot positive last (row.residual values)

private theorem integer_neg (coefficient : Int) : Equiv (realInteger (-coefficient)) (neg (realInteger coefficient)) :=
  ofSignedRatio_neg ⟨coefficient, 1, by decide⟩

theorem Inequality.holds_lower_iff (row : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal)
    (last : ConstructiveReal) (negative : row.pivot < 0) :
    row.Holds (FiniteLinear.extend values last) ↔ LE (row.lowerValue values) last := by
  have positive : 0 < -row.pivot := by omega
  have factor : Equiv (realInteger row.pivot) (neg (realInteger (-row.pivot))) :=
    equiv_symm (equiv_trans (neg_congr (integer_neg row.pivot)) (neg_neg _))
  have negated : Equiv (mul (realInteger row.pivot) last) (neg (mul (realInteger (-row.pivot)) last)) :=
    equiv_trans (mul_congr factor (equiv_refl _)) (neg_mul _ _)
  have lowerCancel := integer_inverse_cancel (-row.pivot) positive (neg (row.residual values))
  calc
    row.Holds (FiniteLinear.extend values last) ↔ LE (mul (realInteger row.pivot) last) (row.residual values) := row.holds_extend_iff values last
    _ ↔ LE (neg (mul (realInteger (-row.pivot)) last)) (row.residual values) := le_congr negated (equiv_refl _)
    _ ↔ LE (neg (row.residual values)) (neg (neg (mul (realInteger (-row.pivot)) last))) := (neg_le_neg_iff _ _).symm
    _ ↔ LE (neg (row.residual values)) (mul (realInteger (-row.pivot)) last) := le_congr (equiv_refl _) (neg_neg _)
    _ ↔ LE (mul (realInteger (-row.pivot)) (mul (integerInverse (-row.pivot) positive) (neg (row.residual values))))
        (mul (realInteger (-row.pivot)) last) := le_congr (equiv_symm lowerCancel) (equiv_refl _)
    _ ↔ LE (mul (integerInverse (-row.pivot) positive) (neg (row.residual values))) last :=
      mul_le_mul_positive_iff _ (integerLower (-row.pivot) positive) (integerLower_le (-row.pivot) positive) _ _
    _ ↔ LE (row.lowerValue values) last := by simp only [Inequality.lowerValue, dif_pos negative]

theorem Inequality.holds_zero_iff (row : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal)
    (last : ConstructiveReal) (zeroPivot : row.pivot = 0) : row.Holds (FiniteLinear.extend values last) ↔ row.trim.Holds values := by
  have evaluation := IntegerRowSpace.realDot_extend variables row.coefficients values last
  change Equiv _ (add (mul (realInteger row.pivot) last) _) at evaluation
  rw [zeroPivot] at evaluation
  exact le_congr (equiv_trans evaluation (equiv_trans (add_congr (zero_mul last) (equiv_refl _)) (zero_add _))) (equiv_refl _)

/-- Fraction-free elimination still uses only integer pivot signs; the
right-hand sides are combined by analytic arithmetic. -/
def combine (upper lower : Inequality (variables + 1)) : Inequality variables :=
  ⟨fun i => -lower.pivot * upper.coefficients i.castSucc + upper.pivot * lower.coefficients i.castSucc,
    add (mul (realInteger (-lower.pivot)) upper.bound) (mul (realInteger upper.pivot) lower.bound)⟩

private theorem difference_add (a b c d : ConstructiveReal) :
    Equiv (sub (add a b) (add c d)) (add (sub a c) (sub b d)) :=
  equiv_trans (add_congr (equiv_refl _) (neg_add c d)) (add_four _ _ _ _)

theorem combine_holds_residual_iff (upper lower : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal) :
    (combine upper lower).Holds values ↔ LE zero
      (add (mul (realInteger (-lower.pivot)) (upper.residual values)) (mul (realInteger upper.pivot) (lower.residual values))) := by
  have expanded : Equiv (realDot variables (combine upper lower).coefficients values)
      (add (mul (realInteger (-lower.pivot)) (realDot variables upper.trim.coefficients values))
        (mul (realInteger upper.pivot) (realDot variables lower.trim.coefficients values))) :=
    equiv_trans (realDot_add_coefficients variables _ _ values)
      (add_congr (realDot_scale_coefficients variables (-lower.pivot) _ values) (realDot_scale_coefficients variables upper.pivot _ values))
  have residual : Equiv (sub (combine upper lower).bound (realDot variables (combine upper lower).coefficients values))
      (add (mul (realInteger (-lower.pivot)) (upper.residual values)) (mul (realInteger upper.pivot) (lower.residual values))) :=
    equiv_trans (add_congr (equiv_refl _) (neg_congr expanded))
    (equiv_trans (difference_add _ _ _ _) (add_congr (equiv_symm (mul_sub _ _ _)) (equiv_symm (mul_sub _ _ _))))
  exact (zero_le_sub_iff _ _).symm.trans (le_congr (equiv_refl _) residual)

/-- The projected row is precisely compatibility of the original analytic
lower and upper endpoints. No comparison of the endpoints is decided. -/
theorem combine_holds_iff (upper lower : Inequality (variables + 1)) (values : Fin variables → ConstructiveReal)
    (positive : 0 < upper.pivot) (negative : lower.pivot < 0) :
    (combine upper lower).Holds values ↔ LE (lower.lowerValue values) (upper.upperValue values) := by
  let a := realInteger upper.pivot
  let b := realInteger (-lower.pivot)
  let ia := integerInverse upper.pivot positive
  let ib := integerInverse (-lower.pivot) (by omega)
  let up := upper.residual values
  let lo := lower.residual values
  have bUpper : Equiv (mul b (mul ia up)) (mul ia (mul b up)) :=
    equiv_trans (equiv_symm (mul_assoc _ _ _)) (equiv_trans (mul_congr (mul_comm _ _) (equiv_refl _)) (mul_assoc _ _ _))
  have endpoints : LE (mul ib (neg lo)) (mul ia up) ↔ LE zero (add (mul b up) (mul a lo)) := by
    calc
      _ ↔ LE (mul b (mul ib (neg lo))) (mul b (mul ia up)) :=
        (mul_le_mul_positive_iff b (integerLower (-lower.pivot) (by omega)) (integerLower_le (-lower.pivot) (by omega)) _ _).symm
      _ ↔ LE (neg lo) (mul ia (mul b up)) := le_congr (integer_inverse_cancel (-lower.pivot) (by omega) (neg lo)) bUpper
      _ ↔ LE (mul a (neg lo)) (mul b up) := (positive_scale_le_iff upper.pivot positive _ _).symm
      _ ↔ LE (neg (mul a lo)) (mul b up) := le_congr (mul_neg _ _) (equiv_refl _)
      _ ↔ LE zero (add (mul b up) (mul a lo)) := neg_le_iff_nonnegative_add _ _
  exact (combine_holds_residual_iff upper lower values).trans (by
    simpa only [Inequality.lowerValue, Inequality.upperValue, dif_pos negative, dif_pos positive] using endpoints.symm)

end Thesis.Probability.AnalyticLinear
