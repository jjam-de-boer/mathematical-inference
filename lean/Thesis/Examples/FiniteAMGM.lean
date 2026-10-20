import Thesis.Probability.FiniteAMGM

namespace Thesis.Examples.FiniteAMGM
open Probability

/-- The general theorem checks arbitrary list lengths, not only powers of two. -/
example (values : List Nat) : values.length ^ values.length * FiniteAMGM.product values ≤ values.sum ^ values.length :=
  FiniteAMGM.inequality values
example : 27 * FiniteAMGM.product [1, 2, 3] ≤ 6 ^ 3 := FiniteAMGM.inequality [1, 2, 3]
example : FiniteAMGM.weightedProduct [(0, 0), (2, 3), (4, 1)] ≤ 3 ^ 4 :=
  FiniteAMGM.weighted_product_le_pow [(0, 0), (2, 3), (4, 1)] 3 (by decide) (by decide)
example : FiniteAMGM.weightedProduct [(0, 0), (2, 3), (4, 1)] < 4 ^ 4 :=
  FiniteAMGM.weighted_product_lt_pow [(0, 0), (2, 3), (4, 1)] 4 (by decide) (by decide)
example : FiniteAMGM.weightedProduct [(0, 0), (0, 0)] = 1 := rfl
example : FiniteAMGM.product [] = 1 := rfl

end Thesis.Examples.FiniteAMGM
