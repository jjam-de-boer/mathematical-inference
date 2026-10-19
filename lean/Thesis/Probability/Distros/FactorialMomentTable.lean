import Thesis.Probability.Distros.FinitePmfExpectation
import Thesis.Probability.Distros.ProbabilityGrid

namespace Thesis.Probability.Distros
open Combinatorics

/-- Candidate factorial moments divided by the corresponding factorial. -/
def factorialTableCoefficient (moments : Nat → QProb) (order : Nat) : SignedRatio :=
  (QProb.div (moments order) (QProb.ofNat (fallingFactorial order order))
    (fallingFactorial_pos order order (Nat.le_refl _))).toSignedRatio

/-- Inversion is defined on a supplied moment table, independently of any law. -/
def inverseFactorialTable (moments : Nat → QProb) (bound value : Nat) : SignedRatio :=
  SignedRatio.listSum ((List.range (bound + 1)).map (fun order =>
    SignedRatio.mul ⟨inverseBinomial order value, 1, Nat.zero_lt_one⟩ (factorialTableCoefficient moments order)))

/-- Necessary finite probability constraints, using signed masses only as
auxiliary arithmetic. Realized record weights will be natural. -/
def FactorialMomentTableValid (moments : Nat → QProb) (bound : Nat) : Prop :=
  (∀ value, value ≤ bound → SignedRatio.Nonnegative (inverseFactorialTable moments bound value)) ∧
  SignedRatio.Equiv (SignedRatio.listSum ((List.range (bound + 1)).map (inverseFactorialTable moments bound))) SignedRatio.one

/-- Inverting a table and taking its binomial moments returns each supplied
normalized moment. No positivity assumption is used in this algebraic step. -/
theorem inverseFactorialTable_choose (moments : Nat → QProb) (bound order : Nat) (within : order ≤ bound) :
    SignedRatio.Equiv (SignedRatio.listSum ((List.range (bound + 1)).map (fun value =>
      SignedRatio.mul (inverseFactorialTable moments bound value) (QProb.ofNat (binom value order)).toSignedRatio)))
      (factorialTableCoefficient moments order) := by
  let values := List.range (bound + 1)
  let kernel := fun value r => SignedRatio.mul (factorialTableCoefficient moments r)
    (SignedRatio.mul ⟨inverseBinomial r value, 1, Nat.zero_lt_one⟩ (QProb.ofNat (binom value order)).toSignedRatio)
  have rows (value : Nat) : SignedRatio.Equiv
      (SignedRatio.mul (inverseFactorialTable moments bound value) (QProb.ofNat (binom value order)).toSignedRatio)
      (SignedRatio.listSum (values.map (kernel value))) := by
    refine SignedRatio.equiv_trans (SignedRatio.listSum_mul
      (values.map (fun r => SignedRatio.mul ⟨inverseBinomial r value, 1, Nat.zero_lt_one⟩ (factorialTableCoefficient moments r)))
      (QProb.ofNat (binom value order)).toSignedRatio) ?_
    simpa only [List.map_map, Function.comp_def, kernel] using
      (SignedRatio.listSum_map_congr values _ _ (fun r => by
        simp only [SignedRatio.Equiv, SignedRatio.mul, Int.natCast_mul]
        ac_rfl))
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr values _ _ rows) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_swap values values kernel) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem values _
    (fun r => if r = order then factorialTableCoefficient moments order else SignedRatio.zero) ?_) ?_
  · intro r member
    have rWithin : r ≤ bound := by have upper := List.mem_range.mp member; omega
    refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (by
      simpa only [List.map_map, Function.comp_def, kernel] using
        (SignedRatio.mul_listSum (factorialTableCoefficient moments r)
          (values.map (fun value => SignedRatio.mul ⟨inverseBinomial r value, 1, Nat.zero_lt_one⟩
            (QProb.ofNat (binom value order)).toSignedRatio))))) ?_
    refine SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
      (inverseBinomial_reverse_ratio_kernel r order bound rWithin)) ?_
    by_cases same : r = order
    · subst r
      simp only [if_true]
      exact SignedRatio.mul_one _
    · simp only [if_neg same]
      exact SignedRatio.mul_zero _
  · exact SignedRatio.listSum_range_select (bound + 1) order (factorialTableCoefficient moments) (Nat.lt_succ_of_le within)

/-- A table agreeing with actual bounded moments inverts to the actual PMF. -/
theorem inverseFactorialTable_of_moments (μ : NatDistro Ω) (moments : Nat → QProb) (bound value : Nat)
    (support : μ.distro.AlmostSurely (fun x => μ.embed x ≤ bound))
    (momentsAgree : ∀ order, order ≤ bound → QProb.Equiv (factorialMoment μ order) (moments order)) :
    SignedRatio.Equiv (μ.distro.record.probVal (fun x => decide (μ.embed x = value))).toSignedRatio
      (inverseFactorialTable moments bound value) := by
  refine SignedRatio.equiv_trans (μ.pmf_factorial_inversion bound value support) ?_
  apply SignedRatio.listSum_map_congr_on_mem
  intro order member
  have within : order ≤ bound := by have upper := List.mem_range.mp member; omega
  exact SignedRatio.mul_congr (SignedRatio.equiv_refl _)
    (QProb.toSignedRatio_congr (QProb.div_congr (momentsAgree order within) (QProb.equiv_refl _) _ _))

end Thesis.Probability.Distros
