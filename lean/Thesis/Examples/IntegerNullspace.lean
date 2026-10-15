import Thesis.Probability.IntegerNullspace

namespace Thesis
namespace Probability
namespace Examples
namespace IntegerNullspace

open Probability.IntegerLinearAlgebra

/-!
# Actual constructed null vectors, including zero rows and moved pivots

The dense two-row fixture has a one-dimensional kernel.  Another fixture
forces a pivot-column transposition, and a zero matrix exercises the branch
that discards a row without a pivot.  The empty-row system retains an actual
nonzero coordinate.  Closed kernel decisions evaluate the constructor's data;
the reusable field theorems separately certify every supplied matrix with
more columns than rows, not just these fixtures.
-/

def dense : Matrix 2 3 := fun row column =>
  if row.val = 0 then (if column.val = 2 then 0 else 1)
  else (if column.val = 0 then 0 else 1)

def denseVector := nonzeroKernel 2 3 dense (by decide)

theorem dense_vanishes : Kernel dense denseVector.vector := denseVector.vanishes
theorem dense_witness : denseVector.vector denseVector.witness ≠ 0 := denseVector.nonzero
theorem dense_computed : forall column, denseVector.vector column =
    (if column.val = 1 then -1 else 1) := by decide +kernel

def movedPivot : Matrix 1 2 := fun _ column => if column.val = 0 then 1 else 0
def movedVector := nonzeroKernel 1 2 movedPivot (by decide)
theorem moved_computed : movedVector.vector 0 = 0 ∧ movedVector.vector 1 = 1 := by decide +kernel

def zeroMatrix : Matrix 2 3 := fun _ _ => 0
def zeroVector := nonzeroKernel 2 3 zeroMatrix (by decide)
theorem zero_computed : forall column, zeroVector.vector column = 1 := by decide +kernel

def emptyMatrix : Matrix 0 1 := fun row => Fin.elim0 row
def emptyVector := nonzeroKernel 0 1 emptyMatrix (by decide)
theorem empty_witness : emptyVector.vector 0 = 1 := by decide +kernel

end IntegerNullspace
end Examples
end Probability
end Thesis
