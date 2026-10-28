import Thesis.Probability.ConstructiveRealNormalCone

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal
open Distros.RationalLinear
open IntegerLinearAlgebra

/-- The dual inequality enforcing a nonnegative multiplier at one original
row position. Repeated primal constraints retain separate positions. -/
def DualSignature.signConstraint (r : Fin rows) : DualSignature rows columns :=
  ⟨fun _ => 0, 0, fun s => if s = r then 1 else 0⟩

/-- One coordinate of the affine gradient representation. -/
def DualSignature.columnConstraint (i : Fin columns) : DualSignature rows columns :=
  ⟨fun j => if j = i then 1 else 0, 0, fun _ => 0⟩

/-- The attained-value equation; its rational coefficients are the original
row bounds and the normalization coefficient. -/
def DualSignature.valueConstraint : DualSignature rows columns :=
  ⟨fun _ => 0, 1, fun _ => 0⟩

/-- Reverse a free equality row. Cone coefficients are zero; this is used
only for stationarity and attained value, never multiplier sign rows. -/
def DualSignature.reverse (signature : DualSignature rows columns) : DualSignature rows columns :=
  ⟨fun i => -signature.direction i, -signature.total, fun _ => 0⟩

theorem DualSignature.reverse_coefficients (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (signature : DualSignature rows columns) (free : ∀ r, signature.cone r = 0) (column : Fin (rows + 1)) :
    (signature.reverse.row matrix bounds gradient target).coefficients column =
      -(signature.row matrix bounds gradient target).coefficients column := by
  have negDirection (vector : Fin columns → Int) : dot (fun i => -signature.direction i) vector = -dot signature.direction vector := by
    simpa only [Int.neg_one_mul] using dot_scale_left (-1) signature.direction vector
  refine Fin.lastCases ?_ (fun r => ?_) column
  · simp only [DualSignature.row, FiniteDenominatorClearing.extendNumerator_last, DualSignature.reverse,
      negDirection, Int.neg_add]
  · simp only [DualSignature.row, FiniteDenominatorClearing.extendNumerator_castSucc, DualSignature.reverse,
      negDirection, free, Int.natCast_zero, Int.sub_zero, Int.neg_mul, Int.neg_add]

theorem DualSignature.reverse_bound (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (signature : DualSignature rows columns) :
    Equiv (signature.reverse.row matrix bounds gradient target).bound (neg (signature.row matrix bounds gradient target).bound) :=
  equiv_trans (add_congr (realDot_negated_coefficients columns signature.direction gradient)
    (equiv_trans (mul_congr (realInteger_neg _) (equiv_refl target)) (neg_mul _ _))) (equiv_symm (neg_add _ _))

theorem DualSignature.reverse_holds_iff (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (signature : DualSignature rows columns) (free : ∀ r, signature.cone r = 0)
    (values : Fin (rows + 1) → ConstructiveReal) :
    (signature.reverse.row matrix bounds gradient target).Holds values ↔
      LE (signature.row matrix bounds gradient target).bound (realDot (rows + 1) (signature.row matrix bounds gradient target).coefficients values) := by
  have coefficients : (signature.reverse.row matrix bounds gradient target).coefficients =
      (fun column => -(signature.row matrix bounds gradient target).coefficients column) :=
    funext (signature.reverse_coefficients matrix bounds gradient target free)
  unfold Inequality.Holds
  rw [coefficients]
  exact (le_congr (realDot_negated_coefficients (rows + 1) _ values)
    (signature.reverse_bound matrix bounds gradient target)).trans (neg_le_neg_iff _ _)

theorem column_evaluation (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal) (i : Fin columns)
    (values : Fin (rows + 1) → ConstructiveReal) :
    Equiv (realDot (rows + 1) ((DualSignature.columnConstraint i).row matrix bounds gradient target).coefficients values)
      (add (values (Fin.last rows)) (realDot rows (fun r => matrix r i) (fun r => values r.castSucc))) := by
  have coefficients : ((DualSignature.columnConstraint i).row matrix bounds gradient target).coefficients =
      FiniteDenominatorClearing.extendNumerator (fun r => matrix r i) 1 := by
    funext column
    refine Fin.lastCases ?_ (fun r => ?_) column
    · simp only [DualSignature.row, DualSignature.columnConstraint, FiniteDenominatorClearing.extendNumerator_last,
        integerDot_unit, Int.add_zero]
    · simp only [DualSignature.row, DualSignature.columnConstraint, FiniteDenominatorClearing.extendNumerator_castSucc,
        integerDot_unit, Int.zero_mul, Int.add_zero, Int.natCast_zero, Int.sub_zero]
  rw [coefficients]
  rw [realDot]
  simp only [FiniteDenominatorClearing.extendNumerator_last, FiniteDenominatorClearing.extendNumerator_castSucc]
  exact add_congr (one_mul _) (equiv_refl _)

theorem column_bound (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal) (i : Fin columns) :
    Equiv ((DualSignature.columnConstraint i).row matrix bounds gradient target).bound (gradient i) :=
  equiv_trans (add_congr (realDot_unit columns i gradient) (zero_mul target)) (add_zero _)

theorem value_evaluation (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (values : Fin (rows + 1) → ConstructiveReal) :
    Equiv (realDot (rows + 1) ((DualSignature.valueConstraint : DualSignature rows columns).row matrix bounds gradient target).coefficients values)
      (add (values (Fin.last rows)) (realDot rows bounds (fun r => values r.castSucc))) := by
  have coefficients : ((DualSignature.valueConstraint : DualSignature rows columns).row matrix bounds gradient target).coefficients =
      FiniteDenominatorClearing.extendNumerator bounds 1 := by
    funext column
    refine Fin.lastCases ?_ (fun r => ?_) column
    · simp only [DualSignature.row, DualSignature.valueConstraint, FiniteDenominatorClearing.extendNumerator_last, dot_zero_left, Int.zero_add]
    · simp only [DualSignature.row, DualSignature.valueConstraint, FiniteDenominatorClearing.extendNumerator_castSucc,
        dot_zero_left, Int.one_mul, Int.zero_add, Int.natCast_zero, Int.sub_zero]
  rw [coefficients]
  rw [realDot]
  simp only [FiniteDenominatorClearing.extendNumerator_last, FiniteDenominatorClearing.extendNumerator_castSucc]
  exact add_congr (one_mul _) (equiv_refl _)

theorem value_bound (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal) :
    Equiv ((DualSignature.valueConstraint : DualSignature rows columns).row matrix bounds gradient target).bound target :=
  equiv_trans (add_congr (realDot_zero columns gradient) (one_mul target)) (zero_add _)

theorem sign_evaluation (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal) (r : Fin rows)
    (values : Fin (rows + 1) → ConstructiveReal) :
    Equiv (realDot (rows + 1) ((DualSignature.signConstraint r).row matrix bounds gradient target).coefficients values)
      (neg (values r.castSucc)) := by
  have coefficients : ((DualSignature.signConstraint r).row matrix bounds gradient target).coefficients =
      FiniteDenominatorClearing.extendNumerator (fun s => if s = r then -1 else 0) 0 := by
    funext column
    refine Fin.lastCases ?_ (fun s => ?_) column
    · simp only [DualSignature.row, DualSignature.signConstraint, FiniteDenominatorClearing.extendNumerator_last, dot_zero_left, Int.add_zero]
    · simp only [DualSignature.row, DualSignature.signConstraint, FiniteDenominatorClearing.extendNumerator_castSucc,
        dot_zero_left, Int.zero_mul, Int.zero_add]
      split <;> simp
  rw [coefficients]
  rw [realDot]
  simp only [FiniteDenominatorClearing.extendNumerator_last, FiniteDenominatorClearing.extendNumerator_castSucc]
  exact equiv_trans (add_congr (zero_mul _) (realDot_negative_unit rows r (fun s => values s.castSucc))) (zero_add _)

theorem sign_bound (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal) (r : Fin rows) :
    Equiv ((DualSignature.signConstraint r).row matrix bounds gradient target).bound zero :=
  equiv_trans (add_congr (realDot_zero columns gradient) (zero_mul target)) (zero_add _)

end Thesis.Probability.AnalyticLinear
