import Thesis.Probability.IntegerLinearAlgebra

namespace Thesis
namespace Probability
namespace IntegerLinearAlgebra

/-!
# Constructive nonzero null vectors for underdetermined integer matrices

The returned object contains a vector and an explicit nonzero coordinate,
not an assumed linear-dependence oracle.  Search for a pivot inspects only
the supplied finite last row.  A nonzero pivot is swapped into the last
column, fraction-free elimination removes that column from the other rows,
and recursion solves a strictly smaller row problem.  The recursive vector
is scaled and extended to satisfy the pivot equation before the column swap
is undone.  An entirely zero last row is simply discarded.

All coefficients are integers.  Clearing the positive denominators of finite
rational constraints is a separate bridge; neither field normalization nor
rational choice is used here.  This constructor is the dependence step
needed by support reduction, not yet the probability compression algorithm.
-/

theorem sum_append (left right : List Int) : sum (left ++ right) = sum left + sum right := by
  induction left with
  | nil => exact (Int.zero_add _).symm
  | cons head tail inductionHypothesis =>
      change head + sum (tail ++ right) = (head + sum tail) + sum right
      rw [inductionHypothesis, Int.add_assoc]

theorem sum_singleton (value : Int) : sum [value] = value := Int.add_zero value

theorem sum_map_zero (values : List α) : sum (values.map (fun _ => (0 : Int))) = 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change 0 + sum (tail.map (fun _ => (0 : Int))) = 0
      rw [inductionHypothesis, Int.zero_add]

theorem dot_zero_left {size : Nat} (vector : Vector size) : dot (fun _ => 0) vector = 0 := by
  simpa only [dot, Int.zero_mul] using sum_map_zero (List.finRange size)

theorem dot_comm {size : Nat} (left right : Vector size) : dot left right = dot right left := by
  unfold dot
  congr 1
  apply List.map_congr_left
  intro index _
  exact Int.mul_comm _ _

theorem dot_scale_right {size : Nat} (factor : Int) (row vector : Vector size) :
    dot row (fun index => factor * vector index) = factor * dot row vector := by
  rw [dot_comm row, dot_scale_left, dot_comm vector row]

theorem dot_succ {size : Nat} (left right : Vector (size + 1)) :
    dot left right = dot (fun index => left index.castSucc) (fun index => right index.castSucc) +
      left (Fin.last size) * right (Fin.last size) := by
  simp only [dot, List.finRange_succ_last, List.map_append, List.map_map,
    List.map_cons, List.map_nil, sum_append, sum_singleton, Function.comp_def]

def extendVector {size : Nat} (initial : Vector size) (last : Int) : Vector (size + 1) :=
  Fin.lastCases last initial

theorem extendVector_castSucc {size : Nat} (initial : Vector size) (last : Int) (index : Fin size) :
    extendVector initial last index.castSucc = initial index := Fin.lastCases_castSucc index

theorem extendVector_last {size : Nat} (initial : Vector size) (last : Int) :
    extendVector initial last (Fin.last size) = last := Fin.lastCases_last

theorem dot_extendVector {size : Nat} (row : Vector (size + 1)) (initial : Vector size) (last : Int) :
    dot row (extendVector initial last) = dot (fun index => row index.castSucc) initial + row (Fin.last size) * last := by
  rw [dot_succ]
  simp only [extendVector_castSucc, extendVector_last]

/-- A literal finite transposition, with its inverse proved below. -/
def swapIndex {size : Nat} (first second index : Fin size) : Fin size :=
  if index = first then second else if index = second then first else index

theorem swapIndex_first {size : Nat} (first second : Fin size) : swapIndex first second first = second := by
  simp [swapIndex]

theorem swapIndex_second {size : Nat} (first second : Fin size) : swapIndex first second second = first := by
  by_cases same : second = first
  · subst second; exact swapIndex_first _ _
  · simp [swapIndex, same]

theorem swapIndex_involutive {size : Nat} (first second index : Fin size) :
    swapIndex first second (swapIndex first second index) = index := by
  by_cases atFirst : index = first
  · subst index; rw [swapIndex_first, swapIndex_second]
  · by_cases atSecond : index = second
    · subst index; rw [swapIndex_second, swapIndex_first]
    · simp only [swapIndex, if_neg atFirst, if_neg atSecond]

def swapVector {size : Nat} (vector : Vector size) (first second : Fin size) : Vector size :=
  fun index => vector (swapIndex first second index)

theorem swapVector_twice {size : Nat} (vector : Vector size) (first second : Fin size) :
    swapVector (swapVector vector first second) first second = vector := by
  funext index
  exact congrArg vector (swapIndex_involutive first second index)

theorem dot_swap {size : Nat} (row vector : Vector size) (first second : Fin size) :
    dot (swapVector row first second) (swapVector vector first second) = dot row vector := by
  exact AdditiveCarrier.int.finSum_reindex size (fun index => row index * vector index)
    (swapIndex first second) (swapIndex first second)
    (swapIndex_involutive first second) (swapIndex_involutive first second)

/-- Inspectable data, including the coordinate witnessing nonzeroness. -/
structure KernelVector {rows columns : Nat} (matrix : Matrix rows columns) where
  vector : Vector columns
  witness : Fin columns
  nonzero : vector witness ≠ 0
  vanishes : Kernel matrix vector

def unswapKernelVector {rows columns : Nat} (matrix : Matrix rows columns) (first second : Fin columns)
    (found : KernelVector (fun row => swapVector (matrix row) first second)) : KernelVector matrix where
  vector := swapVector found.vector first second
  witness := swapIndex first second found.witness
  nonzero := by
    change found.vector (swapIndex first second (swapIndex first second found.witness)) ≠ 0
    rw [swapIndex_involutive]
    exact found.nonzero
  vanishes := by
    intro row
    have same := dot_swap (matrix row) (swapVector found.vector first second) first second
    rw [swapVector_twice] at same
    exact same.symm.trans (found.vanishes row)

def reducedMatrix {rows columns : Nat} (matrix : Matrix (rows + 1) (columns + 1)) : Matrix rows columns :=
  fun row column => eliminateRow (matrix (Fin.last rows)) (matrix row.castSucc) (Fin.last columns) column.castSucc

/-- Recover the omitted pivot equation without division.  The initial is
scaled by the nonzero pivot; the last coefficient cancels its original dot
product.  Nonzeroness survives at the recursive witness coordinate. -/
def liftKernelVector {rows columns : Nat} (matrix : Matrix (rows + 1) (columns + 1))
    (pivotNonzero : matrix (Fin.last rows) (Fin.last columns) ≠ 0)
    (found : KernelVector (reducedMatrix matrix)) : KernelVector matrix := by
  let pivot := matrix (Fin.last rows) (Fin.last columns)
  let pivotDot := dot (fun index => matrix (Fin.last rows) index.castSucc) found.vector
  let lifted := extendVector (fun index => pivot * found.vector index) (-pivotDot)
  refine ⟨lifted, found.witness.castSucc, ?_, ?_⟩
  · change extendVector _ _ found.witness.castSucc ≠ 0
    rw [extendVector_castSucc]
    intro zero
    rcases Int.mul_eq_zero.mp zero with impossible | impossible
    · exact pivotNonzero impossible
    · exact found.nonzero impossible
  · apply (kernel_eliminateMatrix_iff matrix (Fin.last rows) (Fin.last columns) pivotNonzero lifted).mp
    intro row
    refine Fin.lastCases ?_ (fun index => ?_) row
    · simp only [eliminateMatrix]
      change dot _ (extendVector _ _) = 0
      rw [dot_extendVector, dot_scale_right]
      change pivot * pivotDot + pivot * (-pivotDot) = 0
      rw [Int.mul_neg]
      omega
    · have away : index.castSucc ≠ Fin.last rows := by
        intro same
        have impossible : index.val = rows := congrArg Fin.val same
        have bounded := index.isLt
        omega
      simp only [eliminateMatrix, if_neg away]
      change dot _ (extendVector _ _) = 0
      rw [dot_extendVector, dot_scale_right]
      change pivot * dot (reducedMatrix matrix index) found.vector +
        eliminateRow (matrix (Fin.last rows)) (matrix index.castSucc) (Fin.last columns) (Fin.last columns) * (-pivotDot) = 0
      rw [found.vanishes index, eliminateRow_pivot, Int.mul_zero, Int.zero_mul, Int.add_zero]

def findNonzero {columns : Nat} (row : Vector columns) : Option (Fin columns) :=
  (List.finRange columns).find? (fun column => decide (row column ≠ 0))

theorem findNonzero_some {columns : Nat} (row : Vector columns) (column : Fin columns)
    (found : findNonzero row = some column) : row column ≠ 0 :=
  of_decide_eq_true (List.find?_some (p := fun candidate => decide (row candidate ≠ 0)) found)

theorem findNonzero_none {columns : Nat} (row : Vector columns)
    (missing : findNonzero row = none) : forall column, row column = 0 := by
  intro column
  have absent := (List.find?_eq_none.mp missing) column (List.mem_finRange column)
  by_cases zero : row column = 0
  · exact zero
  · exact False.elim (absent (decide_eq_true zero))

/-- Construct an actual nonzero integral null vector whenever columns
outnumber rows.  Structural recursion is on the number of rows, not a search
bound on coefficient sizes, denominators, or possible hidden-state counts. -/
def nonzeroKernel (rows columns : Nat) (matrix : Matrix rows columns) (larger : rows < columns) : KernelVector matrix := by
  induction rows generalizing columns with
  | zero =>
      exact ⟨fun _ => 1, ⟨0, larger⟩, by change (1 : Int) ≠ 0; decide +kernel, fun row => Fin.elim0 row⟩
  | succ rows inductionHypothesis =>
      cases columns with
      | zero => exact False.elim (Nat.not_lt_zero _ larger)
      | succ columns =>
          cases searched : findNonzero (matrix (Fin.last rows)) with
          | none =>
              let found := inductionHypothesis (columns + 1) (fun row => matrix row.castSucc) (by omega)
              refine ⟨found.vector, found.witness, found.nonzero, ?_⟩
              intro row
              refine Fin.lastCases ?_ (fun index => found.vanishes index) row
              have zeroRow : matrix (Fin.last rows) = (fun _ => 0) := funext (findNonzero_none _ searched)
              rw [zeroRow]
              exact dot_zero_left found.vector
          | some column =>
              let swapped : Matrix (rows + 1) (columns + 1) := fun row => swapVector (matrix row) column (Fin.last columns)
              have pivotNonzero : swapped (Fin.last rows) (Fin.last columns) ≠ 0 := by
                simpa only [swapped, swapVector, swapIndex_second] using findNonzero_some _ column searched
              let found := inductionHypothesis columns (reducedMatrix swapped) (by omega)
              exact unswapKernelVector matrix column (Fin.last columns) (liftKernelVector swapped pivotNonzero found)

end IntegerLinearAlgebra
end Probability
end Thesis
