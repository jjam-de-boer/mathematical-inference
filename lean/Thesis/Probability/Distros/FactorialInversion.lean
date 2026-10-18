import Thesis.Probability.Distros.BinomialInversion
import Thesis.Probability.Distros.PositiveSupport
import Thesis.Probability.Distros.RationalChebyshev

namespace Thesis.Probability.Distros
open Combinatorics

/-- Integer auxiliary coefficients embed into a finite rational sum exactly. -/
theorem signedRatio_intRangeSum (n : Nat) (f : Nat → Int) :
    SignedRatio.Equiv (SignedRatio.listSum ((List.range n).map (fun k => (⟨f k, 1, Nat.zero_lt_one⟩ : SignedRatio))))
      ⟨intRangeSum n f, 1, Nat.zero_lt_one⟩ := by
  induction n with
  | zero => exact SignedRatio.equiv_refl _
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      refine SignedRatio.equiv_trans (SignedRatio.listSum_append _ _) ?_
      refine SignedRatio.equiv_trans (SignedRatio.add_congr ih (SignedRatio.add_zero _)) ?_
      simp only [SignedRatio.Equiv, SignedRatio.add, intRangeSum, Int.natCast_one, Int.mul_one]

/-- Natural observables agree with their nonnegative signed-rational embedding. -/
theorem Distro.rationalExpectation_ofNat (μ : Distro Ω) (f : Ω → Nat) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => (QProb.ofNat (f x)).toSignedRatio))
      (μ.expectNat f).toSignedRatio :=
  SignedRatio.equiv_trans (μ.rationalExpectation_toSignedRatio (fun x => QProb.ofNat (f x)))
    (QProb.toSignedRatio_congr (μ.expectation_nat f))

/-- The inverse Pascal row isolates a singleton even when its target is
outside the bound. The signed terms are auxiliary, not probability weights. -/
theorem inverseBinomial_ratio_kernel (n value bound : Nat) (within : n ≤ bound) :
    SignedRatio.Equiv (SignedRatio.listSum ((List.range (bound + 1)).map (fun order =>
      SignedRatio.mul ⟨inverseBinomial order value, 1, Nat.zero_lt_one⟩
        (QProb.ofNat (binom n order)).toSignedRatio)))
      (if n = value then SignedRatio.one else SignedRatio.zero) := by
  have terms := SignedRatio.listSum_map_congr (List.range (bound + 1))
    (fun order => SignedRatio.mul ⟨inverseBinomial order value, 1, Nat.zero_lt_one⟩
      (QProb.ofNat (binom n order)).toSignedRatio)
    (fun order => (⟨inverseBinomial order value * (binom n order : Int), 1, Nat.zero_lt_one⟩ : SignedRatio))
    (fun order => by
      simp only [SignedRatio.Equiv, SignedRatio.mul, QProb.ofNat, QProb.toSignedRatio,
        Int.natCast_one, Int.mul_one, Nat.mul_one])
  have result := SignedRatio.equiv_trans terms (signedRatio_intRangeSum (bound + 1)
    (fun order => inverseBinomial order value * (binom n order : Int)))
  rw [inverseBinomial_kernel_bounded n value bound within] at result
  by_cases same : n = value
  · simpa only [if_pos same] using result
  · simpa only [if_neg same] using result

/-- Explicit finite alternating-sum inversion. The order coefficient is
(-1)^(order-value) * binom order value, and the moment coefficient is
E[(X)_order]/order!, so this is the usual factorial-moment PMF formula. -/
def inverseFactorialPMF (μ : NatDistro Ω) (bound value : Nat) : SignedRatio :=
  SignedRatio.listSum ((List.range (bound + 1)).map (fun order =>
    SignedRatio.mul ⟨inverseBinomial order value, 1, Nat.zero_lt_one⟩
      (factorialPGFCoefficient μ order).toSignedRatio))

/-- Every bounded numeric PMF is its finite alternating sum of factorial
moments. Bounds hold only almost surely and null outliers remain recorded. -/
theorem NatDistro.pmf_factorial_inversion (μ : NatDistro Ω) (bound value : Nat)
    (support : μ.distro.AlmostSurely (fun x => μ.embed x ≤ bound)) :
    SignedRatio.Equiv (μ.distro.record.probVal (fun x => decide (μ.embed x = value))).toSignedRatio
      (inverseFactorialPMF μ bound value) := by
  let terms := fun order x => SignedRatio.mul ⟨inverseBinomial order value, 1, Nat.zero_lt_one⟩
    (QProb.ofNat (binom (μ.embed x) order)).toSignedRatio
  let kernel := fun x => SignedRatio.listSum ((List.range (bound + 1)).map (fun order => terms order x))
  let event : Event Ω := fun x => decide (μ.embed x = value)
  have indicator : SignedRatio.Equiv (μ.distro.rationalExpectation (fun x =>
      if μ.embed x = value then SignedRatio.one else SignedRatio.zero))
      (μ.distro.record.probVal event).toSignedRatio := by
    refine SignedRatio.equiv_trans (μ.distro.rationalExpectation_congr _
      (fun x => (QProb.ofNat (if event x then 1 else 0)).toSignedRatio) ?_) ?_
    · intro x
      by_cases same : μ.embed x = value
      · simp only [event, same, if_true, decide_true]
        exact SignedRatio.equiv_refl _
      · simp only [event, same, if_false, decide_false, Bool.false_eq_true]
        exact SignedRatio.equiv_refl _
    · have result := μ.distro.rationalExpectation_ofNat (fun x => if event x then 1 else 0)
      simpa only [Distro.expectNat, natIntegral_indicator, FiniteProbRecord.probVal] using result
  have singleton : SignedRatio.Equiv (μ.distro.rationalExpectation kernel)
      (μ.distro.record.probVal event).toSignedRatio :=
    SignedRatio.equiv_trans (μ.distro.rationalExpectation_congr_positive kernel _
      (fun atom member weight => inverseBinomial_ratio_kernel (μ.embed atom.1) value bound (support atom member weight))) indicator
  have expansion := μ.distro.rationalExpectation_listSum (List.range (bound + 1)) terms
  have moments := SignedRatio.listSum_map_congr (List.range (bound + 1))
    (fun order => μ.distro.rationalExpectation (terms order))
    (fun order => SignedRatio.mul ⟨inverseBinomial order value, 1, Nat.zero_lt_one⟩
      (factorialPGFCoefficient μ order).toSignedRatio)
    (fun order => SignedRatio.equiv_trans (μ.distro.rationalExpectation_mul_left _ _)
      (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (SignedRatio.equiv_trans (μ.distro.rationalExpectation_ofNat _)
          (QProb.toSignedRatio_congr (QProb.equiv_symm (factorialPGFCoefficient_binom μ order))))))
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm singleton) (SignedRatio.equiv_trans expansion moments)

end Thesis.Probability.Distros
