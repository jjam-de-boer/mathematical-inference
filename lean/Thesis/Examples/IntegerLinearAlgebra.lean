import Thesis.Probability.IntegerLinearAlgebra

namespace Thesis
namespace Probability
namespace Examples
namespace IntegerLinearAlgebra

open Probability.IntegerLinearAlgebra

/-!
# A dependent-row matrix and its actual nonzero kernel vector

The second row is twice the first.  Fraction-free elimination annihilates
it, and the explicit vector `(-2,1,0)` is in the original and transformed
kernels.  The universal row-operation theorem supplies preservation, while
small kernel-only decisions independently check this concrete arithmetic.
This fixture does not assume a general nullspace-existence theorem.
-/

def matrix : Matrix 2 3 := fun row column => (((row.val + 1) * (column.val + 1) : Nat) : Int)
def vector : Vector 3 := fun column => if column.val = 0 then -2 else if column.val = 1 then 1 else 0

theorem pivot_nonzero : matrix 0 0 ≠ 0 := by decide +kernel
theorem vector_nonzero : vector 0 ≠ 0 := by decide +kernel

theorem original_kernel : Kernel matrix vector := by
  unfold Kernel
  decide +kernel

theorem transformed_kernel : Kernel (eliminateMatrix matrix 0 0) vector :=
  (kernel_eliminateMatrix_iff matrix 0 0 pivot_nonzero vector).mpr original_kernel

theorem second_row_vanishes : forall column, eliminateMatrix matrix 0 0 1 column = 0 := by decide +kernel

theorem eliminated_pivot_coordinate : eliminateRow (matrix 0) (matrix 1) 0 0 = 0 :=
  eliminateRow_pivot _ _ _

end IntegerLinearAlgebra
end Examples
end Probability
end Thesis
