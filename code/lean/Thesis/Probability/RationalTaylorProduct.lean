import Thesis.Probability.RationalTaylorConvolution
import Thesis.Probability.RationalTaylorGeometric
import Thesis.Probability.RationalDoubleSum
import Thesis.Probability.RationalPolynomialGeometric

namespace Thesis.Probability.RationalTaylorExponential
open SignedRatio RationalGeometricSeries RationalDoubleSum

/-- The finite triangle contains exactly the Taylor prefix at a+b. -/
theorem triangle_value (a b : SignedRatio) (n : Nat) :
    Equiv (triangle (fun i j => mul (term a i) (term b j)) n) (partialSum (term (add a b)) n) := by
  have coefficients := rangeSum_congr (term (add a b)) (convolution a b) n (fun k _ => term_add a b k)
  have grouped := diagonals (fun i j => mul (term a i) (term b j)) n
  exact equiv_trans (equiv_symm (equiv_trans coefficients grouped)) (rangeSum_block _ _)

/-- The discrepancy between multiplying two finite Taylor prefixes and
truncating their convolution is the omitted finite corner. Its error bound
is explicit, uniform in the truncation count, and valid for signed inputs. -/
theorem partial_product_error (a b : SignedRatio) (boundA boundB n : Nat)
    (boundedA : QProb.LE a.magnitude (QProb.ofNat boundA)) (boundedB : QProb.LE b.magnitude (QProb.ofNat boundB)) :
    QProb.LE (sub (mul (partialSum (term a) n) (partialSum (term b) n)) (partialSum (term (add a b)) n)).magnitude
      (QProb.scale (n * n) (envelope (geometricCoefficient boundA * geometricCoefficient boundB) n)) := by
  let kernel := fun i j => mul (term a i) (term b j)
  have squareValue : Equiv (square kernel n) (mul (partialSum (term a) n) (partialSum (term b) n)) :=
    equiv_trans (square_product (term a) (term b) n) (mul_congr (rangeSum_block _ _) (rangeSum_block _ _))
  have triangleValue := triangle_value a b n
  have difference : Equiv
      (sub (mul (partialSum (term a) n) (partialSum (term b) n)) (partialSum (term (add a b)) n)) (corner kernel n) :=
    equiv_trans (add_congr (equiv_trans (equiv_symm squareValue) (square_split kernel n)) (neg_congr (equiv_symm triangleValue)))
      (add_sub_cancel_left (triangle kernel n) (corner kernel n))
  have entries : ∀ i j, QProb.LE (kernel i j).magnitude
      (envelope (geometricCoefficient boundA * geometricCoefficient boundB) (i + j)) := by
    intro i j
    have estimate := QProb.mul_le_mul (term_global_bound a boundA boundedA i) (term_global_bound b boundB boundedB j)
    have collect : QProb.Equiv
        (QProb.mul (envelope (geometricCoefficient boundA) i) (envelope (geometricCoefficient boundB) j))
        (envelope (geometricCoefficient boundA * geometricCoefficient boundB) (i + j)) := by
      simp only [QProb.Equiv, QProb.mul, envelope, Nat.pow_add]
    exact QProb.le_congr (QProb.equiv_symm (magnitude_mul _ _)) collect estimate
  exact QProb.le_congr (QProb.equiv_symm (magnitude_congr difference)) (QProb.equiv_refl _)
    (corner_bound kernel _ n entries)

end Thesis.Probability.RationalTaylorExponential
