import Thesis.Probability.Distros.Degenerate
import Thesis.Probability.Distros.FinCap
import Thesis.Probability.Distros.WaitingTime

namespace Thesis.Probability.Distros
open Combinatorics

/-!
Truncated geometric and NB laws are consistent under conditioning on smaller
windows.  Their right-censored siblings are consistent under further
clipping, including zero success weight for positive-total constructors.
All equalities hold on every Boolean event of the smaller finite outcome.
-/

theorem negativeBinomialWeight_cap_scale (r small large a b : Nat) (bound : small ≤ large)
    (k : Fin (small + 1)) :
    negativeBinomialWeight r large a b (liftFinCap bound k) =
      (a + b) ^ (large - small) * negativeBinomialWeight r small a b k := by
  have hk := k.isLt
  have exponent : large - k.val = (large - small) + (small - k.val) := by omega
  simp only [negativeBinomialWeight, liftFinCap]
  rw [exponent, Nat.pow_add]
  ac_rfl

theorem negativeBinomialWeight_sum_pos (r cap a b : Nat) (positive : 0 < a) :
    0 < natSum (cap + 1) (finWeight (negativeBinomialWeight r cap a b)) := by
  rw [negativeBinomialWeight_sum]
  exact Nat.mul_pos (Nat.pow_pos positive)
    (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left positive b))

theorem negativeBinomial_cap_positive (r small large a b : Nat) (bound : small ≤ large)
    (shape : 0 < r) (positive : 0 < a) :
    (negativeBinomialDistro r large a b shape positive).record.EventPositive
      (fun x => decide (x.val ≤ small)) :=
  ofFinWeights_prefix_positive small large bound
    (negativeBinomialWeight r large a b) (negativeBinomialWeight r small a b)
    (negativeBinomialWeight_sum_pos r large a b positive)
    (negativeBinomialWeight_sum_pos r small a b positive)
    ((a + b) ^ (large - small)) (Nat.pow_pos (Nat.add_pos_left positive b))
    (negativeBinomialWeight_cap_scale r small large a b bound)

/-- Conditioning a larger truncated waiting time on the smaller window
recovers the smaller truncated negative-binomial law. -/
theorem negativeBinomial_condition_cap (r small large a b : Nat) (bound : small ≤ large)
    (shape : 0 < r) (positive : 0 < a) :
    (conditionFinCap (negativeBinomialDistro r large a b shape positive) small
      (negativeBinomial_cap_positive r small large a b bound shape positive)).SameLaw
      (negativeBinomialDistro r small a b shape positive) :=
  ofFinWeights_conditionCap small large bound
    (negativeBinomialWeight r large a b) (negativeBinomialWeight r small a b)
    (negativeBinomialWeight_sum_pos r large a b positive)
    (negativeBinomialWeight_sum_pos r small a b positive)
    ((a + b) ^ (large - small)) (negativeBinomialWeight_cap_scale r small large a b bound) _

theorem negativeBinomialCensoredWeight_sum_pos (r cap a b : Nat) (shape : 0 < r)
    (positive : 0 < a + b) :
    0 < natSum (cap + 1) (finWeight (negativeBinomialCensoredWeight r cap a b)) := by
  rw [negativeBinomialCensoredWeight_sum, negativeBinomialCensored_exhaustion a b r cap shape]
  exact Nat.pow_pos positive

/-- Further right censoring commutes with the finite NB construction,
including the zero-success-weight endpoint. -/
theorem negativeBinomialCensoredOfTotal_censor_cap (r small large a b : Nat)
    (bound : small ≤ large) (shape : 0 < r) (positive : 0 < a + b) :
    (censorFinCap (negativeBinomialCensoredDistroOfTotal r large a b shape positive) small).SameLaw
      (negativeBinomialCensoredDistroOfTotal r small a b shape positive) := by
  apply ofFinWeights_censorCap small large bound
    (negativeBinomialCensoredWeight r large a b) (negativeBinomialCensoredWeight r small a b)
    (negativeBinomialCensoredWeight_sum_pos r large a b shape positive)
    (negativeBinomialCensoredWeight_sum_pos r small a b shape positive)
    ((a + b) ^ (large - small))
  · intro k inside
    have largeInside : (liftFinCap bound k).val < large := by
      change k.val < large
      omega
    simp only [negativeBinomialCensoredWeight, if_pos inside, if_pos largeInside]
    exact negativeBinomialWeight_cap_scale r small large a b bound k
  · rw [negativeBinomialCensoredWeight_sum, negativeBinomialCensoredWeight_sum,
      negativeBinomialCensored_exhaustion a b r large shape,
      negativeBinomialCensored_exhaustion a b r small shape, ← Nat.pow_add]
    congr 1
    omega

theorem negativeBinomialCensored_censor_cap (r small large a b : Nat)
    (bound : small ≤ large) (shape : 0 < r) (positive : 0 < a) :
    (censorFinCap (negativeBinomialCensoredDistro r large a b shape positive) small).SameLaw
      (negativeBinomialCensoredDistro r small a b shape positive) :=
  negativeBinomialCensoredOfTotal_censor_cap r small large a b bound shape (Nat.add_pos_left positive b)

theorem geometric_cap_positive (small large a b : Nat) (bound : small ≤ large) (positive : 0 < a) :
    (geometricDistro large a b positive).record.EventPositive (fun x => decide (x.val ≤ small)) := by
  simpa only [negativeBinomial_one_eq_geometric] using
    negativeBinomial_cap_positive 1 small large a b bound (Nat.succ_pos 0) positive

theorem geometric_condition_cap (small large a b : Nat) (bound : small ≤ large) (positive : 0 < a) :
    (conditionFinCap (geometricDistro large a b positive) small
      (geometric_cap_positive small large a b bound positive)).SameLaw (geometricDistro small a b positive) := by
  simpa only [negativeBinomial_one_eq_geometric] using
    negativeBinomial_condition_cap 1 small large a b bound (Nat.succ_pos 0) positive

theorem negativeBinomialCensoredOfTotal_one_eq_geometric (cap a b : Nat) (positive : 0 < a + b) :
    negativeBinomialCensoredDistroOfTotal 1 cap a b (Nat.succ_pos 0) positive =
      geometricCensoredDistroOfTotal cap a b positive := by
  simp only [negativeBinomialCensoredDistroOfTotal, geometricCensoredDistroOfTotal,
    negativeBinomialCensoredWeight_one]

theorem geometricCensoredOfTotal_censor_cap (small large a b : Nat)
    (bound : small ≤ large) (positive : 0 < a + b) :
    (censorFinCap (geometricCensoredDistroOfTotal large a b positive) small).SameLaw
      (geometricCensoredDistroOfTotal small a b positive) := by
  simpa only [negativeBinomialCensoredOfTotal_one_eq_geometric] using
    negativeBinomialCensoredOfTotal_censor_cap 1 small large a b bound (Nat.succ_pos 0) positive

theorem geometricCensored_censor_cap (small large a b : Nat)
    (bound : small ≤ large) (positive : 0 < a) :
    (censorFinCap (geometricCensoredDistro large a b positive) small).SameLaw
      (geometricCensoredDistro small a b positive) :=
  geometricCensoredOfTotal_censor_cap small large a b bound (Nat.add_pos_left positive b)

end Thesis.Probability.Distros
