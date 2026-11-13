import Thesis.Probability.ConstructiveRealFiniteLinear
import Thesis.Probability.ConstructiveRealSimplexResponseBounds

namespace Thesis.Probability.ConstructiveReal.IntegerRowSpace
open ConstructiveReal
open FiniteLinear
open Distros.RationalLinear

abbrev Matrix := IntegerLinearAlgebra.Matrix

def Kernel (matrix : Matrix rows columns) (values : Fin columns → ConstructiveReal) : Prop :=
  ∀ row, Equiv (realDot columns (matrix row) values) zero

def AnnihilatesKernel (matrix : Matrix rows columns) (gradient : Fin columns → ConstructiveReal) : Prop :=
  ∀ values, Kernel matrix values → Equiv (pair columns gradient values) zero

/-- Actual analytic coefficients of original integer rows. Redundancy is
allowed; this type claims neither independence nor unique coefficients. -/
structure Multipliers (matrix : Matrix rows columns) (gradient : Fin columns → ConstructiveReal) where
  value : Fin rows → ConstructiveReal
  represents : ∀ column, Equiv (gradient column) (realDot rows (fun row => matrix row column) value)

theorem realDot_scale_values (size : Nat) (coefficients : Fin size → Int) (values : Fin size → ConstructiveReal) (factor : ConstructiveReal) :
    Equiv (realDot size coefficients (fun i => mul factor (values i))) (mul factor (realDot size coefficients values)) :=
  equiv_trans (realDot_pair _ _ _) (equiv_trans (pair_scale_second _ _ _ _)
    (mul_congr (equiv_refl _) (equiv_symm (realDot_pair _ _ _))))

theorem realDot_sub_coefficients (size : Nat) (first second : Fin size → Int) (values : Fin size → ConstructiveReal) :
    Equiv (realDot size (fun i => first i - second i) values) (sub (realDot size first values) (realDot size second values)) := by
  simpa only [Int.sub_eq_add_neg] using equiv_trans (realDot_add_coefficients size first (fun i => -second i) values)
    (add_congr (equiv_refl _) (realDot_negated_coefficients size second values))

theorem realDot_extend (size : Nat) (coefficients : Fin (size + 1) → Int) (values : Fin size → ConstructiveReal) (last : ConstructiveReal) :
    Equiv (realDot (size + 1) coefficients (FiniteLinear.extend values last))
      (add (mul (realInteger (coefficients (Fin.last size))) last) (realDot size (fun i => coefficients i.castSucc) values)) := by
  change Equiv (add (mul _ (FiniteLinear.extend values last (Fin.last size)))
    (realDot size _ (fun i => FiniteLinear.extend values last i.castSucc))) _
  simp only [FiniteLinear.extend_castSucc, FiniteLinear.extend_last]
  exact equiv_refl _

def reduced (matrix : Matrix (rows + 1) (columns + 1)) : Matrix rows columns :=
  IntegerLinearAlgebra.reducedMatrix matrix

theorem reduced_dot (matrix : Matrix (rows + 1) (columns + 1)) (row : Fin rows) (values : Fin columns → ConstructiveReal) :
    Equiv (realDot columns (reduced matrix row) values)
      (sub (mul (realInteger (matrix (Fin.last rows) (Fin.last columns))) (realDot columns (fun i => matrix row.castSucc i.castSucc) values))
        (mul (realInteger (matrix row.castSucc (Fin.last columns))) (realDot columns (fun i => matrix (Fin.last rows) i.castSucc) values))) :=
  equiv_trans (realDot_sub_coefficients columns _ _ values)
    (add_congr (realDot_scale_coefficients columns _ _ values) (neg_congr (realDot_scale_coefficients columns _ _ values)))

def liftValues (matrix : Matrix (rows + 1) (columns + 1)) (values : Fin columns → ConstructiveReal) : Fin (columns + 1) → ConstructiveReal :=
  FiniteLinear.extend (fun i => mul (realInteger (matrix (Fin.last rows) (Fin.last columns))) (values i))
    (neg (realDot columns (fun i => matrix (Fin.last rows) i.castSucc) values))

/-- The original kernel direction is explicitly recovered from a reduced
one by fraction-free operations. No analytic pivot test or division occurs. -/
theorem liftValues_kernel (matrix : Matrix (rows + 1) (columns + 1)) (values : Fin columns → ConstructiveReal)
    (valid : Kernel (reduced matrix) values) : Kernel matrix (liftValues matrix values) := by
  intro row
  have evaluation (row : Fin (rows + 1)) :
      Equiv (realDot (columns + 1) (matrix row) (liftValues matrix values))
        (sub (mul (realInteger (matrix (Fin.last rows) (Fin.last columns))) (realDot columns (fun i => matrix row i.castSucc) values))
          (mul (realInteger (matrix row (Fin.last columns))) (realDot columns (fun i => matrix (Fin.last rows) i.castSucc) values))) :=
    equiv_trans (realDot_extend columns (matrix row) _ _)
      (equiv_trans (add_congr (mul_neg _ _) (realDot_scale_values columns _ values _)) (add_comm _ _))
  refine Fin.lastCases ?_ (fun earlier => ?_) row
  · exact equiv_trans (evaluation (Fin.last rows)) ((sub_equiv_zero_iff _ _).mpr (equiv_refl _))
  · exact equiv_trans (evaluation earlier.castSucc) (equiv_trans (equiv_symm (reduced_dot matrix earlier values)) (valid earlier))

def reducedGradient (matrix : Matrix (rows + 1) (columns + 1)) (gradient : Fin (columns + 1) → ConstructiveReal) : Fin columns → ConstructiveReal :=
  fun i => sub (mul (realInteger (matrix (Fin.last rows) (Fin.last columns))) (gradient i.castSucc))
    (mul (gradient (Fin.last columns)) (realInteger (matrix (Fin.last rows) i.castSucc)))

theorem reducedGradient_pair (matrix : Matrix (rows + 1) (columns + 1)) (gradient : Fin (columns + 1) → ConstructiveReal)
    (values : Fin columns → ConstructiveReal) :
    Equiv (pair columns (reducedGradient matrix gradient) values) (pair (columns + 1) gradient (liftValues matrix values)) := by
  let common := sub
    (mul (realInteger (matrix (Fin.last rows) (Fin.last columns))) (pair columns (fun i => gradient i.castSucc) values))
    (mul (gradient (Fin.last columns)) (realDot columns (fun i => matrix (Fin.last rows) i.castSucc) values))
  have reducedPair : Equiv (pair columns (reducedGradient matrix gradient) values) common := equiv_trans (pair_sub_first columns _ _ values)
    (add_congr (pair_scale_first columns _ _ values)
      (neg_congr (equiv_trans (pair_scale_first columns _ _ values)
        (mul_congr (equiv_refl _) (equiv_symm (realDot_pair columns _ values))))))
  have liftedPair : Equiv (pair (columns + 1) gradient (liftValues matrix values)) common := equiv_trans (pair_extend columns gradient _ _)
    (add_congr (pair_scale_second columns _ _ values) (mul_neg _ _))
  exact equiv_trans reducedPair (equiv_symm liftedPair)

theorem annihilates_reduced (matrix : Matrix (rows + 1) (columns + 1)) (gradient : Fin (columns + 1) → ConstructiveReal)
    (annihilates : AnnihilatesKernel matrix gradient) : AnnihilatesKernel (reduced matrix) (reducedGradient matrix gradient) :=
  fun values valid => equiv_trans (reducedGradient_pair matrix gradient values) (annihilates _ (liftValues_kernel matrix values valid))

theorem annihilates_swapped (matrix : Matrix rows columns) (gradient : Fin columns → ConstructiveReal)
    (annihilates : AnnihilatesKernel matrix gradient) (a b : Fin columns) :
    AnnihilatesKernel (fun row => IntegerLinearAlgebra.swapVector (matrix row) a b) (swap gradient a b) := by
  intro values valid
  have original : Kernel matrix (swap values a b) := by
    intro row
    have same := realDot_swap columns (matrix row) (swap values a b) a b
    rw [swap_twice] at same
    exact equiv_trans (equiv_symm same) (valid row)
  have same := pair_swap columns gradient (swap values a b) a b
  rw [swap_twice] at same
  exact equiv_trans same (annihilates _ original)

def unswapMultipliers (matrix : Matrix rows columns) (gradient : Fin columns → ConstructiveReal) (a b : Fin columns)
    (found : Multipliers (fun row => IntegerLinearAlgebra.swapVector (matrix row) a b) (swap gradient a b)) : Multipliers matrix gradient where
  value := found.value
  represents column := by
    have same := found.represents (IntegerLinearAlgebra.swapIndex a b column)
    simpa only [swap, IntegerLinearAlgebra.swapVector, IntegerLinearAlgebra.swapIndex_involutive] using same

end Thesis.Probability.ConstructiveReal.IntegerRowSpace
