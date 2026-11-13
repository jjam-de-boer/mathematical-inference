import Thesis.Probability.Distros.RationalLinearObjective

namespace Thesis.Probability.Distros.RationalLinear

/-!
# Reversible positive scaling of exact rational linear constraints

Conditional optimization will replace response masses `w` by `z = t * w`,
where `t` is the reciprocal of a positive evidence probability. A row
`a · w ≤ b` then becomes `a · z ≤ b * t`. Since the existing elimination
engine requires integer coefficients, clear the displayed denominator of
`b`: the new row is `b.den * a · z - b.num * t ≤ 0`.

This module proves that translation in both directions for every strictly
positive rational scale. It retains unreduced fractions, arbitrary signed
row coefficients and zero coordinates. The inverse is explicit finite data.
Zero or negative scales are deliberately excluded from the equivalence;
later conditional normalization must establish positivity, not assume it.

These are linear-system preservation results. No conditional extrema,
native-model coverage or general nonlinear feasibility result is asserted.
-/

private theorem mul_le_mul_positive_iff (factor left right : SignedRatio)
    (positive : 0 < factor.num) :
    SignedRatio.LE (SignedRatio.mul factor left) (SignedRatio.mul factor right) ↔
      SignedRatio.LE left right := by
  rw [SignedRatio.le_iff_cross, SignedRatio.le_iff_cross]
  simp only [SignedRatio.mul, Int.natCast_mul]
  have factorPositive : 0 < factor.num * (factor.den : Int) :=
    Int.mul_pos positive (by have h := factor.den_pos; omega)
  have first : factor.num * left.num * ((factor.den : Int) * (right.den : Int)) =
      (factor.num * (factor.den : Int)) * (left.num * (right.den : Int)) := by ac_rfl
  have second : factor.num * right.num * ((factor.den : Int) * (left.den : Int)) =
      (factor.num * (factor.den : Int)) * (right.num * (left.den : Int)) := by ac_rfl
  rw [first, second]
  exact Int.mul_le_mul_left factorPositive

private theorem scaleInt_mul_value (coefficient : Int) (factor value : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.scaleInt coefficient (SignedRatio.mul factor value))
      (SignedRatio.mul factor (SignedRatio.scaleInt coefficient value)) := by
  simp only [SignedRatio.Equiv, SignedRatio.scaleInt, SignedRatio.mul,
    Int.natCast_mul]
  ac_rfl

/-- A common rational factor commutes with the finite integer dot product.
The statement compares fractions extensionally and never normalizes them. -/
theorem dot_mul_values (variables : Nat) (coefficients : Fin variables → Int)
    (values : Fin variables → SignedRatio) (factor : SignedRatio) :
    SignedRatio.Equiv (dot variables coefficients (fun i => SignedRatio.mul factor (values i)))
      (SignedRatio.mul factor (dot variables coefficients values)) := by
  induction variables with
  | zero => exact SignedRatio.equiv_symm (SignedRatio.mul_zero factor)
  | succ variables ih =>
      exact SignedRatio.equiv_trans
        (SignedRatio.add_congr (scaleInt_mul_value _ _ _)
          (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc)))
        (SignedRatio.equiv_symm (SignedRatio.mul_add factor _ _))

private def appendCoefficient (coefficients : Fin variables → Int) (last : Int) : Fin (variables + 1) → Int :=
  fun i => if earlier : i.val < variables then coefficients ⟨i.val, earlier⟩ else last

private theorem appendCoefficient_last (coefficients : Fin variables → Int) (last : Int) :
    appendCoefficient coefficients last (Fin.last variables) = last := by
  simp only [appendCoefficient, Fin.val_last, dif_neg (Nat.lt_irrefl variables)]

private theorem appendCoefficient_castSucc (coefficients : Fin variables → Int) (last : Int) (i : Fin variables) :
    appendCoefficient coefficients last i.castSucc = coefficients i := by
  simp only [appendCoefficient, Fin.val_castSucc, dif_pos i.isLt]

/-- Retain an ordinary row while appending an unused final coordinate.
Evidence normalization uses this for its two exact-value inequalities. -/
def Inequality.extendZero (row : Inequality variables) : Inequality (variables + 1) where
  coefficients := appendCoefficient row.coefficients 0
  bound := row.bound

theorem Inequality.extendZero_dot (row : Inequality variables)
    (values : Fin variables → SignedRatio) (last : SignedRatio) :
    SignedRatio.Equiv (dot (variables + 1) row.extendZero.coefficients (extend values last))
      (dot variables row.coefficients values) := by
  unfold Inequality.extendZero
  rw [dot_extend]
  simp only [appendCoefficient_last, appendCoefficient_castSucc]
  exact SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.zero_scaleInt last) (SignedRatio.equiv_refl _))
    (SignedRatio.zero_add _)

theorem Inequality.extendZero_holds_iff (row : Inequality variables)
    (values : Fin variables → SignedRatio) (last : SignedRatio) :
    row.extendZero.Holds (extend values last) ↔ row.Holds values :=
  SignedRatio.le_congr (row.extendZero_dot values last) (SignedRatio.equiv_refl _)

/-- Append the scale coordinate and clear the row bound's positive natural
denominator. The resulting inequality has a literal zero right-hand side. -/
def Inequality.homogenize (row : Inequality variables) : Inequality (variables + 1) where
  coefficients := appendCoefficient (fun i => (row.bound.den : Int) * row.coefficients i) (-row.bound.num)
  bound := SignedRatio.zero

private theorem clear_bound (bound scale : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.scaleInt (bound.den : Int) (SignedRatio.mul bound scale))
      (SignedRatio.scaleInt bound.num scale) := by
  simp only [SignedRatio.Equiv, SignedRatio.scaleInt, SignedRatio.mul,
    Nat.one_mul, Int.natCast_mul]
  ac_rfl

/-- The integer row expresses exactly the intended scaled inequality,
even before positivity of the separate scale coordinate has been established. -/
theorem Inequality.homogenize_holds_iff (row : Inequality variables)
    (values : Fin variables → SignedRatio) (scale : SignedRatio) :
    row.homogenize.Holds (extend values scale) ↔
      SignedRatio.LE (dot variables row.coefficients values) (SignedRatio.mul row.bound scale) := by
  unfold Inequality.Holds Inequality.homogenize
  rw [dot_extend]
  simp only [appendCoefficient_last, appendCoefficient_castSucc]
  have rewritten := SignedRatio.le_congr
    (SignedRatio.add_congr (SignedRatio.neg_scaleInt row.bound.num scale)
      (dot_scale_coefficients variables (row.bound.den : Int) row.coefficients values))
    (SignedRatio.equiv_refl SignedRatio.zero)
  refine rewritten.trans ((SignedRatio.neg_add_le_zero_iff _ _).trans ?_)
  exact (SignedRatio.le_congr (SignedRatio.equiv_refl _)
    (SignedRatio.equiv_symm (clear_bound row.bound scale))).trans
      (SignedRatio.scaleInt_le_iff _ (by have h := row.bound.den_pos; omega) _ _)

/-- Scaling an actual feasible assignment preserves, and reflects, every
row. Strict positivity is used only to cancel the common rational scale. -/
theorem Inequality.homogenize_scaled_iff (row : Inequality variables)
    (values : Fin variables → SignedRatio) (scale : SignedRatio) (positive : 0 < scale.num) :
    row.homogenize.Holds (extend (fun i => SignedRatio.mul scale (values i)) scale) ↔
      row.Holds values :=
  (row.homogenize_holds_iff _ scale).trans
    ((SignedRatio.le_congr (dot_mul_values variables row.coefficients values scale)
      (SignedRatio.mul_comm row.bound scale)).trans (mul_le_mul_positive_iff scale _ _ positive))

/-- An explicit inverse for a strictly positive signed-rational scale.
Its numerator is natural, and its denominator comes from the supplied
positive numerator; no quotient representative or witness is selected. -/
def positiveInverse (scale : SignedRatio) (positive : 0 < scale.num) : SignedRatio :=
  ⟨(scale.den : Int), scale.num.toNat, by omega⟩

theorem mul_positiveInverse (scale : SignedRatio) (positive : 0 < scale.num) :
    SignedRatio.Equiv (SignedRatio.mul scale (positiveInverse scale positive)) SignedRatio.one := by
  have recovered : (scale.num.toNat : Int) = scale.num := by omega
  simp only [SignedRatio.Equiv, SignedRatio.mul, positiveInverse, SignedRatio.one,
    Int.natCast_one, Int.mul_one, Int.one_mul, Int.natCast_mul]
  rw [recovered]
  ac_rfl

theorem rescale_unscale (scale : SignedRatio) (positive : 0 < scale.num) (value : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.mul scale (SignedRatio.mul (positiveInverse scale positive) value)) value :=
  SignedRatio.equiv_trans (SignedRatio.equiv_symm (SignedRatio.mul_assoc _ _ _))
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (mul_positiveInverse scale positive) (SignedRatio.equiv_refl value))
      (SignedRatio.one_mul value))

/-- Every positively scaled solution gives an actual original assignment,
obtained by multiplying each coordinate by the displayed inverse scale. -/
theorem Inequality.homogenize_unscaled_iff (row : Inequality variables)
    (values : Fin variables → SignedRatio) (scale : SignedRatio) (positive : 0 < scale.num) :
    row.homogenize.Holds (extend values scale) ↔
      row.Holds (fun i => SignedRatio.mul (positiveInverse scale positive) (values i)) := by
  let original := fun i => SignedRatio.mul (positiveInverse scale positive) (values i)
  have same := dot_congr variables row.coefficients values
    (fun i => SignedRatio.mul scale (original i))
    (fun i => SignedRatio.equiv_symm (rescale_unscale scale positive (values i)))
  exact (row.homogenize_holds_iff values scale).trans
    ((SignedRatio.le_congr same (SignedRatio.equiv_refl _)).trans
      ((row.homogenize_holds_iff _ scale).symm.trans (row.homogenize_scaled_iff original scale positive)))

def homogenizeRows (rows : List (Inequality variables)) : List (Inequality (variables + 1)) :=
  rows.map Inequality.homogenize

/-- The forward map preserves the entire supplied system, including mass
normalization and observed-law equalities when expressed as pairs of rows. -/
theorem homogenizeRows_scaled_iff (rows : List (Inequality variables))
    (values : Fin variables → SignedRatio) (scale : SignedRatio) (positive : 0 < scale.num) :
    Satisfies (homogenizeRows rows) (extend (fun i => SignedRatio.mul scale (values i)) scale) ↔
      Satisfies rows values := by
  constructor
  · intro valid row member
    exact (row.homogenize_scaled_iff values scale positive).mp
      (valid row.homogenize (List.mem_map.mpr ⟨row, member, rfl⟩))
  · intro valid row member
    rcases List.mem_map.mp member with ⟨original, listed, rfl⟩
    exact (original.homogenize_scaled_iff values scale positive).mpr (valid original listed)

/-- The reverse map applies to every solution with a positive scale, not
only to assignments originally produced by the forward constructor. -/
theorem homogenizeRows_unscaled_iff (rows : List (Inequality variables))
    (values : Fin variables → SignedRatio) (scale : SignedRatio) (positive : 0 < scale.num) :
    Satisfies (homogenizeRows rows) (extend values scale) ↔
      Satisfies rows (fun i => SignedRatio.mul (positiveInverse scale positive) (values i)) := by
  constructor
  · intro valid row member
    exact (row.homogenize_unscaled_iff values scale positive).mp
      (valid row.homogenize (List.mem_map.mpr ⟨row, member, rfl⟩))
  · intro valid row member
    rcases List.mem_map.mp member with ⟨original, listed, rfl⟩
    exact (original.homogenize_unscaled_iff values scale positive).mpr (valid original listed)

end Thesis.Probability.Distros.RationalLinear
