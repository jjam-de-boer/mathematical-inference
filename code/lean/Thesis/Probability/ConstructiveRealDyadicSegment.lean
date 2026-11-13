import Thesis.Probability.ConstructiveRealEntropyStrongConcavityClosed
import Thesis.Probability.ConstructiveRealDistanceScaling

namespace Thesis.Probability.ConstructiveReal

/-- Explicit dyadic sampling radii. Their recursion and convergence involve
only positive rational arithmetic. -/
def dyadicPrecision : Nat → PositiveRatio
  | 0 => PositiveRatio.one
  | n + 1 => (dyadicPrecision n).half

theorem dyadicPrecision_num (n : Nat) : (dyadicPrecision n).num = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem dyadicPrecision_den (n : Nat) : (dyadicPrecision n).den = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dyadicPrecision, PositiveRatio.half, Nat.pow_succ, ih]

private theorem index_le_two_pow (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      have doubled := Nat.mul_le_mul_right 2 ih
      omega

/-- A sample index below any requested rational radius is computed directly
from its denominator; no unbounded search or analytic comparison is used. -/
theorem dyadicPrecision_small (precision : PositiveRatio) :
    PositiveRatio.LE (dyadicPrecision precision.den) precision := by
  change (dyadicPrecision precision.den).num * precision.den ≤ precision.num * (dyadicPrecision precision.den).den
  rw [dyadicPrecision_num, dyadicPrecision_den, Nat.one_mul]
  have first : precision.den ≤ 2 ^ precision.den := by have bound := index_le_two_pow precision.den; omega
  have second := Nat.mul_le_mul_right (2 ^ precision.den) (Nat.succ_le_of_lt precision.num_pos)
  exact Nat.le_trans first (by simpa only [Nat.one_mul] using second)

theorem dyadicPrecision_half (n : Nat) :
    Equiv (ofSignedRatio (dyadicPrecision (n + 1)).toSignedRatio)
      (mul (ofSignedRatio (dyadicPrecision n).toSignedRatio) (ofSignedRatio ⟨1, 2, by decide⟩)) := by
  apply equiv_trans ((ofSignedRatio_equiv_iff _ _).mpr ?_) (equiv_symm (ofSignedRatio_mul _ _))
  simp only [dyadicPrecision, PositiveRatio.half, PositiveRatio.toSignedRatio, PositiveRatio.toQProb,
    QProb.toSignedRatio, SignedRatio.Equiv, SignedRatio.mul, Int.natCast_mul, Int.mul_one]

theorem affine_one (base target : ConstructiveReal) :
    Equiv (add base (mul one (sub target base))) target :=
  equiv_trans (add_congr (equiv_refl _) (one_mul _))
    (equiv_trans (equiv_symm (add_assoc base target (neg base))) (add_sub_cancel base target))

private abbrev Expr := RationalPolynomial.Expression 3
private def baseVar : Expr := .coordinate 0
private def targetVar : Expr := .coordinate 1
private def coefficientVar : Expr := .coordinate 2
private def halfVar : Expr := .constant ⟨1, 2, by decide⟩
private def affineVar : Expr := .add baseVar (.mul coefficientVar (.sub targetVar baseVar))
private def midpointAffine : Expr := .mul (.add baseVar affineVar) halfVar
private def halfAffine : Expr := .add baseVar (.mul (.mul coefficientVar halfVar) (.sub targetVar baseVar))

/-- The midpoint step halves the affine displacement exactly. -/
theorem midpoint_affine (base target coefficient : ConstructiveReal) :
    Equiv (midpoint base (add base (mul coefficient (sub target base))))
      (add base (mul (mul coefficient (ofSignedRatio ⟨1, 2, by decide⟩)) (sub target base))) :=
  RationalPolynomial.Expression.equalityCheck_sound_real midpointAffine halfAffine (by decide +kernel)
    (fun i => if i.val = 0 then base else if i.val = 1 then target else coefficient)

namespace UnitIntervalValue

/-- Start at the possibly zero endpoint and repeatedly take its midpoint
with the reference. The entire construction stays in the closed unit cube. -/
def towards (reference target : UnitIntervalValue) : Nat → UnitIntervalValue
  | 0 => target
  | n + 1 => reference.midpoint (towards reference target n)

theorem towards_affine (reference target : UnitIntervalValue) (n : Nat) :
    Equiv (reference.towards target n).value
      (add reference.value (mul (ofSignedRatio (dyadicPrecision n).toSignedRatio) (sub target.value reference.value))) := by
  induction n with
  | zero => exact equiv_symm (affine_one reference.value target.value)
  | succ n ih =>
      have substituted := mul_congr (add_congr (equiv_refl reference.value) ih) (equiv_refl (ofSignedRatio ⟨1, 2, by decide⟩))
      exact equiv_trans substituted (equiv_trans (midpoint_affine reference.value target.value _)
        (add_congr (equiv_refl _) (mul_congr (equiv_symm (dyadicPrecision_half n)) (equiv_refl _))))

/-- Every noninitial sample retains half the reference's supplied positive
floor, even when the target is zero. -/
theorem towards_positive (reference target : UnitIntervalValue) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) reference.value) (n : Nat) (later : 0 < n) :
    LE (ofSignedRatio lower.half.toSignedRatio) (reference.towards target n).value := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ later)
  | succ n =>
      have halfPositive : LE zero (ofSignedRatio (⟨1, 2, by decide⟩ : SignedRatio)) := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
      have bound := mul_le_mul_nonnegative_right halfPositive (add_le_add positive (reference.towards target n).nonnegative)
      have represented : Equiv (mul (add (ofSignedRatio lower.toSignedRatio) zero) (ofSignedRatio ⟨1, 2, by decide⟩))
          (ofSignedRatio lower.half.toSignedRatio) := by
        apply equiv_trans (mul_congr (add_zero _) (equiv_refl _))
          (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr ?_))
        simp only [PositiveRatio.half, PositiveRatio.toSignedRatio, PositiveRatio.toQProb, QProb.toSignedRatio,
          SignedRatio.Equiv, SignedRatio.mul, Int.natCast_mul, Int.mul_one]
      exact (le_congr represented (equiv_refl _)).mp bound

private theorem within_one (first second : UnitIntervalValue) : Within QProb.one first.value second.value := by
  have increased (value : UnitIntervalValue) : LE one (add value.value one) :=
    (le_congr (zero_add one) (equiv_refl _)).mp (add_le_add value.nonnegative (le_refl one))
  exact ⟨le_trans first.bounded (increased second), le_trans second.bounded (increased first)⟩

/-- An explicit distance certificate for every dyadic sample. The bound is
independent of endpoint ordering and includes both boundary values. -/
theorem towards_within (reference target : UnitIntervalValue) (n : Nat) :
    Within (dyadicPrecision n).toQProb reference.value (reference.towards target n).value := by
  let precision := dyadicPrecision n
  have difference := within_increment (within_one reference target)
  have scaled := (within_mul_positive_iff precision QProb.one (sub target.value reference.value) zero).mpr difference
  have smaller := within_mono scaled (QProb.le_congr (QProb.equiv_refl _) (QProb.mul_one precision.toQProb) (QProb.le_refl _))
  have centered := (within_congr (equiv_refl _) (mul_zero _)).mp smaller
  have translated := (within_add_left_iff precision.toQProb reference.value zero _).mpr (within_symm centered)
  exact (within_congr (add_zero _) (equiv_symm (reference.towards_affine target n))).mp translated

end UnitIntervalValue
end Thesis.Probability.ConstructiveReal
