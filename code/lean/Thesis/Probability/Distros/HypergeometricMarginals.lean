import Thesis.Probability.Distros.HypergeometricFactorialMoments

namespace Thesis.Probability.Distros
open Combinatorics

/-!
# Every finite-population colour count has a hypergeometric law

A coordinate observable reads one entry of the full occupancy vector.
Single-coordinate factorial orders reduce the mixed moment formula to that
colour's falling factorial and the population total. Fixed shape of listed
atoms justifies that coordinate reduction on the original record.

Both coordinate laws are bounded by the finite population. Constructive
factorial-moment reconstruction therefore upgrades the moment calculation
to equality of every event probability. Zero stock and zero draws remain
covered; the coordinate index must still belong to the declared colour list.
-/

/-- Keep the full count-law sample space while reading one natural count;
an out-of-range lookup is defined as zero, but the marginal theorem below
requires an actual declared colour. -/
def multivariateHypergeometricCoordinate (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (index : Nat) : NatDistro (List Nat) :=
  ⟨multivariateHypergeometricDistro n stocks positive, fun counts => counts.getD index 0⟩

theorem multivariateHypergeometric_coordinate_factorialMoment (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (index order : Nat) (within : index < stocks.length)
    (orderWithin : order ≤ stocks.sum) :
    QProb.Equiv (factorialMoment (multivariateHypergeometricCoordinate n stocks positive index) order)
      ⟨fallingFactorial n order * fallingFactorial (stocks.getD index 0) order,
        fallingFactorial stocks.sum order, fallingFactorial_pos _ _ orderWithin⟩ := by
  let orders := singleOrders stocks.length index order
  have joint := multivariateHypergeometric_jointFactorialMoment n stocks orders positive
    (singleOrders_length _ _ _) (by rw [singleOrders_sum _ _ _ within]; exact orderWithin)
  have factors : jointFalling orders stocks = fallingFactorial (stocks.getD index 0) order := by
    rw [jointFalling_product]
    exact coordinateProduct_single fallingFactorial (fun _ => rfl) stocks index order within
  have orderSum : orders.sum = order := singleOrders_sum _ _ _ within
  let μ := multivariateHypergeometricDistro n stocks positive
  have observable := μ.expectNat_congr_on_support
    (fun counts => fallingFactorial (counts.getD index 0) order) (jointFalling orders) (by
      intro atom member
      have dimension := (multivariateHypergeometric_support n stocks atom member).1
      rw [jointFalling_product]
      have equality := coordinateProduct_single fallingFactorial (fun _ => rfl) atom.1 index order (by omega)
      simpa only [dimension] using equality.symm)
  change QProb.Equiv (μ.expectNat (fun counts => fallingFactorial (counts.getD index 0) order)) _
  rw [observable]
  simpa only [jointFactorialMoment, factors, orderSum] using joint

/-- Every colour count is hypergeometric. The full event law follows from
factorial-moment reconstruction, including zero stocks and zero draws. -/
theorem multivariateHypergeometric_coordinate_hypergeometric (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (index : Nat) (within : index < stocks.length) :
    (multivariateHypergeometricCoordinate n stocks positive index).SameLaw
      (hypergeometricNatDistro (stocks.getD index 0) stocks.sum n (list_getD_le_sum stocks index) positive) := by
  have sampleBound := hypergeometric_draws_le_total stocks.sum n positive
  -- A finite support bound is essential here: it is what turns matching
  -- factorial moments into complete equality of the two marginal laws.
  apply NatDistro.sameLaw_of_factorialMoments _ _ stocks.sum
  · intro atom member
    exact Nat.le_trans (multivariateHypergeometric_coordinate_bound n stocks atom member index) sampleBound
  · intro atom _
    change atom.1.val ≤ stocks.sum
    have bound := atom.1.isLt
    omega
  · intro order orderWithin
    exact QProb.equiv_trans
      (multivariateHypergeometric_coordinate_factorialMoment n stocks positive index order within orderWithin)
      (QProb.equiv_symm (hypergeometric_factorialMoment_ratio (stocks.getD index 0) stocks.sum n order
        (list_getD_le_sum stocks index) positive orderWithin))

end Thesis.Probability.Distros
