import Thesis.Probability.RationalValues
import Thesis.Probability.Reindexing

namespace Thesis
namespace Probability

/-!
# Fraction-free integer elimination for rational compression

This is constructive auxiliary linear algebra, not a new probability space.
After clearing finitely many positive denominators, rational constraints can
be handled by integer matrices.  The denominator-clearing bridge is a separate
obligation; this module proves the exact integer row-operation identities.
Vectors and matrices have explicit finite dimensions and integer entries.
Finite sums reuse the development's additive-carrier fold and its
constructive permutation theorem rather than introducing unordered sums.

The elimination operation is fraction-free: multiply a row by the supplied
pivot and subtract the corresponding multiple of the pivot row.  Its pivot
entry becomes zero, and when the pivot is nonzero the whole matrix has exactly
the same kernel.  No pivot is chosen from an existential proposition and no
real-field theorem or general excluded-middle instance is requested.

These are load-bearing elimination identities.  Constructing a nonzero kernel
vector for an underdetermined matrix, reducing positive support, and replacing
independent causal sources are subsequent obligations, not constructor fields
or consequences silently assumed by this module.
-/

def AdditiveCarrier.int : AdditiveCarrier Int where
  Equiv := Eq
  equiv_refl := fun _ => rfl
  equiv_symm := fun same => same.symm
  equiv_trans := fun first second => first.trans second
  add := (· + ·)
  zero := 0
  add_congr := by intro _ _ _ _ first second; rw [first, second]
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_zero := Int.add_zero

namespace IntegerLinearAlgebra

abbrev Vector (size : Nat) := Fin size → Int
abbrev Matrix (rows columns : Nat) := Fin rows → Vector columns

def sum (values : List Int) : Int := AdditiveCarrier.int.listSum values

theorem sum_map_add (values : List α) (left right : α → Int) :
    sum (values.map (fun value => left value + right value)) =
      sum (values.map left) + sum (values.map right) := by
  induction values with
  | nil => exact (Int.zero_add 0).symm
  | cons head tail inductionHypothesis =>
      change (left head + right head) + sum (tail.map (fun value => left value + right value)) =
        (left head + sum (tail.map left)) + (right head + sum (tail.map right))
      rw [inductionHypothesis]
      simp only [Int.add_assoc, Int.add_left_comm]

theorem sum_map_sub (values : List α) (left right : α → Int) :
    sum (values.map (fun value => left value - right value)) =
      sum (values.map left) - sum (values.map right) := by
  induction values with
  | nil => exact (Int.sub_self 0).symm
  | cons head tail inductionHypothesis =>
      change (left head - right head) + sum (tail.map (fun value => left value - right value)) =
        (left head + sum (tail.map left)) - (right head + sum (tail.map right))
      rw [inductionHypothesis]
      simp only [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_left_comm]

theorem sum_map_mul_left (values : List α) (factor : Int) (entry : α → Int) :
    sum (values.map (fun value => factor * entry value)) = factor * sum (values.map entry) := by
  induction values with
  | nil => exact (Int.mul_zero factor).symm
  | cons head tail inductionHypothesis =>
      change factor * entry head + sum (tail.map (fun value => factor * entry value)) =
        factor * (entry head + sum (tail.map entry))
      rw [inductionHypothesis, Int.mul_add]

def dot {size : Nat} (left right : Vector size) : Int :=
  sum ((List.finRange size).map (fun index => left index * right index))

theorem dot_add_left {size : Nat} (first second vector : Vector size) :
    dot (fun index => first index + second index) vector = dot first vector + dot second vector := by
  simp only [dot, Int.add_mul]
  exact sum_map_add _ _ _

theorem dot_sub_left {size : Nat} (first second vector : Vector size) :
    dot (fun index => first index - second index) vector = dot first vector - dot second vector := by
  simp only [dot, Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul]
  simpa only [Int.sub_eq_add_neg] using
    (sum_map_sub (List.finRange size) (fun index => first index * vector index) (fun index => second index * vector index))

theorem dot_scale_left {size : Nat} (factor : Int) (row vector : Vector size) :
    dot (fun index => factor * row index) vector = factor * dot row vector := by
  simp only [dot, Int.mul_assoc]
  exact sum_map_mul_left _ _ _

def eliminateRow {size : Nat} (pivotRow row : Vector size) (pivot : Fin size) : Vector size :=
  fun index => pivotRow pivot * row index - row pivot * pivotRow index

/-- The selected coordinate vanishes even if the pivot is zero; only the
later kernel-equivalence theorem needs a nonzero pivot. -/
theorem eliminateRow_pivot {size : Nat} (pivotRow row : Vector size) (pivot : Fin size) :
    eliminateRow pivotRow row pivot pivot = 0 := by
  unfold eliminateRow
  rw [Int.mul_comm (pivotRow pivot) (row pivot)]
  exact Int.sub_self _

theorem eliminateRow_dot {size : Nat} (pivotRow row vector : Vector size) (pivot : Fin size) :
    dot (eliminateRow pivotRow row pivot) vector =
      pivotRow pivot * dot row vector - row pivot * dot pivotRow vector := by
  unfold eliminateRow
  rw [dot_sub_left, dot_scale_left, dot_scale_left]

/-- With the pivot equation already imposed, elimination preserves this
row's zero equation in both directions.  The nonzero premise is essential. -/
theorem eliminateRow_kernel_iff {size : Nat} (pivotRow row vector : Vector size) (pivot : Fin size)
    (nonzero : pivotRow pivot ≠ 0) (pivotKernel : dot pivotRow vector = 0) :
    dot (eliminateRow pivotRow row pivot) vector = 0 ↔ dot row vector = 0 := by
  rw [eliminateRow_dot, pivotKernel, Int.mul_zero]
  simp only [Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]
  constructor
  · intro vanished
    rcases Int.mul_eq_zero.mp vanished with impossible | wanted
    · exact False.elim (nonzero impossible)
    · exact wanted
  · intro vanished
    rw [vanished, Int.mul_zero]

def Kernel {rows columns : Nat} (matrix : Matrix rows columns) (vector : Vector columns) : Prop :=
  forall row, dot (matrix row) vector = 0

/-- Retain the actual pivot row and eliminate its column in every other
row.  This does not change either dimension or the supplied column labels. -/
def eliminateMatrix {rows columns : Nat} (matrix : Matrix rows columns)
    (pivotRow : Fin rows) (pivotColumn : Fin columns) : Matrix rows columns :=
  fun row => if row = pivotRow then matrix row else eliminateRow (matrix pivotRow) (matrix row) pivotColumn

theorem kernel_eliminateMatrix_iff {rows columns : Nat} (matrix : Matrix rows columns)
    (pivotRow : Fin rows) (pivotColumn : Fin columns) (nonzero : matrix pivotRow pivotColumn ≠ 0)
    (vector : Vector columns) :
    Kernel (eliminateMatrix matrix pivotRow pivotColumn) vector ↔ Kernel matrix vector := by
  constructor
  · intro transformed
    have pivotKernel : dot (matrix pivotRow) vector = 0 := by
      simpa only [eliminateMatrix, if_pos rfl] using transformed pivotRow
    intro row
    by_cases selected : row = pivotRow
    · subst row; exact pivotKernel
    · have transformedRow : dot (eliminateRow (matrix pivotRow) (matrix row) pivotColumn) vector = 0 := by
        simpa only [eliminateMatrix, if_neg selected] using transformed row
      exact (eliminateRow_kernel_iff _ _ _ pivotColumn nonzero pivotKernel).mp transformedRow
  · intro original row
    by_cases selected : row = pivotRow
    · simpa only [eliminateMatrix, if_pos selected] using original row
    · simpa only [eliminateMatrix, if_neg selected] using
        (eliminateRow_kernel_iff _ _ _ pivotColumn nonzero (original pivotRow)).mpr (original row)

end IntegerLinearAlgebra
end Probability
end Thesis
