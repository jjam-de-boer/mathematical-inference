import Thesis.Causality.SupportAwareSemantics

namespace Thesis.Causality.ProbabilityResult

open Probability

/-!
# Exact zero/support abstraction of partial nonnegative arithmetic

Expression availability needs less information than its numerical value.
For the present nonnegative rational language, the three possibilities are
undefined, a defined zero, and a defined positive number. Every operation
below is an exact abstraction of the corresponding partial operation, not
an approximation that silently identifies undefined with zero.

Strict multiplication still rejects an undefined operand even beside zero.
Only the separately justified weighted multiplication may skip a factor
under a defined zero weight. Division requires a positive denominator.
There is no subtraction or signed cancellation here: those operations
would need a richer abstraction and are deliberately outside this result.

These elementary facts depend on no structural model or identification
theorem. They supply the arithmetic induction for observational support
analysis, but do not themselves assert completeness of formula discovery.
-/

inductive Status where
  | undefined
  | zero
  | positive
  deriving DecidableEq, Repr

namespace Status

def add : Status → Status → Status
  | .undefined, _ => .undefined
  | _, .undefined => .undefined
  | .zero, .zero => .zero
  | _, _ => .positive

def multiply : Status → Status → Status
  | .undefined, _ => .undefined
  | _, .undefined => .undefined
  | .zero, _ => .zero
  | _, .zero => .zero
  | .positive, .positive => .positive

def weightedMultiply : Status → Status → Status
  | .undefined, _ => .undefined
  | .zero, _ => .zero
  | .positive, factor => factor

def divide : Status → Status → Status
  | numerator, .positive => numerator
  | _, _ => .undefined

def sum : List Status → Status
  | [] => .zero
  | value :: rest => add value (sum rest)

def isDefined : Status → Bool
  | .undefined => false
  | .zero => true
  | .positive => true

theorem multiply_positive_left (factor : Status) :
    multiply .positive factor = factor := by
  cases factor <;> rfl

end Status

/-- A positive denominator is part of `QProb`; the numerator alone decides
whether its nonnegative value is zero. Fractions need not be reduced. -/
def valueStatus (value : QProb) : Status :=
  if value.num = 0 then .zero else .positive

def status : Result → Status
  | none => .undefined
  | some value => valueStatus value

theorem valueStatus_equiv {left right : QProb} (same : QProb.Equiv left right) :
    valueStatus left = valueStatus right := by
  unfold valueStatus
  rw [QProb.equiv_num_zero_iff same]

theorem valueStatus_add (left right : QProb) :
    valueStatus (QProb.add left right) = Status.add (valueStatus left) (valueStatus right) := by
  by_cases leftZero : left.num = 0 <;> by_cases rightZero : right.num = 0 <;>
    simp [valueStatus, QProb.add, Status.add, leftZero, rightZero,
      Nat.add_eq_zero, Nat.mul_eq_zero, Nat.ne_of_gt left.den_pos, Nat.ne_of_gt right.den_pos]

theorem valueStatus_mul (left right : QProb) :
    valueStatus (QProb.mul left right) = Status.multiply (valueStatus left) (valueStatus right) := by
  by_cases leftZero : left.num = 0 <;> by_cases rightZero : right.num = 0 <;>
    simp [valueStatus, QProb.mul, Status.multiply, leftZero, rightZero, Nat.mul_eq_zero]

theorem valueStatus_div (left right : QProb) (positive : 0 < right.num) :
    valueStatus (QProb.div left right positive) = valueStatus left := by
  simp [valueStatus, QProb.div, Nat.mul_eq_zero, Nat.ne_of_gt right.den_pos]

/-- Exact agreement with strict partial addition. -/
theorem status_add (left right : Result) :
    status (add left right) = Status.add (status left) (status right) := by
  cases left with
  | none => rfl
  | some left =>
      cases right with
      | none =>
          change .undefined = Status.add (valueStatus left) .undefined
          cases valueStatus left <;> rfl
      | some right => exact valueStatus_add left right

theorem status_multiply (left right : Result) :
    status (multiply left right) = Status.multiply (status left) (status right) := by
  cases left with
  | none => rfl
  | some left =>
      cases right with
      | none =>
          change .undefined = Status.multiply (valueStatus left) .undefined
          cases valueStatus left <;> rfl
      | some right => exact valueStatus_mul left right

/-- The asymmetric zero-weight rule is retained exactly, even when the
factor has no value. It is not a new strict-multiplication convention. -/
theorem status_weightedMultiply (weight factor : Result) :
    status (weightedMultiply weight factor) = Status.weightedMultiply (status weight) (status factor) := by
  cases weight with
  | none => rfl
  | some weight =>
      by_cases zero : weight.num = 0
      · simp [weightedMultiply, status, valueStatus, zero, Status.weightedMultiply, QProb.zero]
      · simp only [weightedMultiply, if_neg zero, status_multiply]
        simp only [status, valueStatus, if_neg zero, Status.weightedMultiply]
        exact Status.multiply_positive_left _

theorem status_divide (numerator denominator : Result) :
    status (divide numerator denominator) = Status.divide (status numerator) (status denominator) := by
  cases numerator with
  | none =>
      cases denominator with
      | none => rfl
      | some value =>
          change .undefined = Status.divide .undefined (valueStatus value)
          cases valueStatus value <;> rfl
  | some numerator =>
      cases denominator with
      | none => rfl
      | some denominator =>
          by_cases positive : 0 < denominator.num
          · simp only [divide, dif_pos positive, status, valueStatus_div]
            simp [valueStatus, Nat.ne_of_gt positive, Status.divide]
          · have zero : denominator.num = 0 := by omega
            simp [divide, positive, status, valueStatus, zero, Status.divide]

/-- Marginalization remains strict in every listed branch; this includes
an undefined summand next to arbitrarily many defined zeros. -/
theorem status_sum (values : List Result) :
    status (sum values) = Status.sum (values.map status) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [sum, status_add, ih, List.map_cons, Status.sum]

theorem status_isDefined (result : Result) :
    (status result).isDefined = result.isSome := by
  cases result with
  | none => rfl
  | some value =>
      by_cases zero : value.num = 0 <;>
        simp [status, valueStatus, zero, Status.isDefined]

end Thesis.Causality.ProbabilityResult
