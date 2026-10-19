import Thesis.Probability.Distros.FactorialInversion
import Thesis.Probability.Distros.MultivariateFactorialPGF

namespace Thesis.Probability.Distros
open Combinatorics

/-- Product of the coordinate inverse Pascal coefficients. Each factor is
(-1)^(order-target) * binom order target when target ≤ order, and zero otherwise. -/
def jointInverseBinomial : List Nat → List Nat → Int
  | [], [] => 1
  | order :: orders, target :: targets => inverseBinomial order target * jointInverseBinomial orders targets
  | _, _ => 0

/-- Tensoring the finite scalar inversion identity isolates one joint atom. -/
theorem jointInverseBinomial_ratio_kernel (counts target : List Nat) (bound : Nat)
    (dimension : target.length = counts.length) (bounded : ∀ count ∈ counts, count ≤ bound) :
    SignedRatio.Equiv (SignedRatio.listSum ((factorialBox counts.length bound).map (fun orders =>
      SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
        (QProb.ofNat (jointChoose orders counts)).toSignedRatio)))
      (if counts = target then SignedRatio.one else SignedRatio.zero) := by
  induction counts generalizing target with
  | nil => cases target with
      | nil => rfl
      | cons value target => simp only [List.length_cons, List.length_nil] at dimension; omega
  | cons count counts ih => cases target with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons value target =>
          let head := fun order => SignedRatio.mul ⟨inverseBinomial order value, 1, Nat.zero_lt_one⟩
            (QProb.ofNat (binom count order)).toSignedRatio
          let tail := fun orders => SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
            (QProb.ofNat (jointChoose orders counts)).toSignedRatio
          let term := fun order orders => SignedRatio.mul
            ⟨jointInverseBinomial (order :: orders) (value :: target), 1, Nat.zero_lt_one⟩
            (QProb.ofNat (jointChoose (order :: orders) (count :: counts))).toSignedRatio
          have separated (order : Nat) (orders : List Nat) :
              SignedRatio.Equiv (term order orders) (SignedRatio.mul (head order) (tail orders)) := by
            simp only [term, head, tail, jointInverseBinomial, jointChoose, SignedRatio.Equiv,
              SignedRatio.mul, QProb.ofNat, QProb.toSignedRatio, Nat.mul_one,
              Int.natCast_one, Int.natCast_mul, Int.mul_one]
            ac_rfl
          have tailKernel := ih target (Nat.succ.inj dimension)
            (fun other member => bounded other (List.mem_cons_of_mem _ member))
          have rows (order : Nat) : SignedRatio.Equiv
              (SignedRatio.listSum ((factorialBox counts.length bound).map (term order)))
              (SignedRatio.mul (head order) (if counts = target then SignedRatio.one else SignedRatio.zero)) := by
            refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr _ _ _ (separated order)) ?_
            refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (by
              simpa only [List.map_map, Function.comp_def] using
                (SignedRatio.mul_listSum (head order) ((factorialBox counts.length bound).map tail)))) ?_
            exact SignedRatio.mul_congr (SignedRatio.equiv_refl _) tailKernel
          have grouped := SignedRatio.listSum_flatMap (List.range (bound + 1))
            (fun order => (factorialBox counts.length bound).map (term order))
          refine SignedRatio.equiv_trans (by
            simpa only [List.length_cons, factorialBox, List.map_flatMap, List.map_map, Function.comp_def, term] using grouped) ?_
          refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr _ _ _ rows) ?_
          refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (by
            simpa only [List.map_map, Function.comp_def] using
              (SignedRatio.listSum_mul ((List.range (bound + 1)).map head)
                (if counts = target then SignedRatio.one else SignedRatio.zero)))) ?_
          refine SignedRatio.equiv_trans (SignedRatio.mul_congr
            (inverseBinomial_ratio_kernel count value bound (bounded count (List.mem_cons_self ..)))
            (SignedRatio.equiv_refl _)) ?_
          by_cases first : count = value <;> by_cases rest : counts = target
          · simp only [first, rest, if_true]
            exact SignedRatio.one_mul _
          · simp only [List.cons.injEq, first, rest, true_and, false_and, if_false, if_true]
            exact SignedRatio.mul_zero _
          · simp only [List.cons.injEq, first, rest, false_and, if_false, if_true]
            exact SignedRatio.zero_mul _
          · simp only [List.cons.injEq, first, rest, false_and, if_false]
            exact SignedRatio.zero_mul _

/-- Explicit joint factorial-moment inversion over a finite rectangle.
The auxiliary integer coefficient supplies every alternating sign. -/
def inverseJointFactorialPMF (μ : Distro (List Nat)) (bound : Nat) (target : List Nat) : SignedRatio :=
  SignedRatio.listSum ((factorialBox target.length bound).map (fun orders =>
    SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
      (multivariateFactorialCoefficient μ orders).toSignedRatio))

/-- Multivariate PMFs are explicit alternating sums of mixed factorial
moments, even with varying totals and retained wrong-shaped null atoms. -/
theorem Distro.pmf_jointFactorial_inversion (μ : Distro (List Nat)) (bound : Nat) (target : List Nat)
    (support : μ.AlmostSurely (fun counts => counts.length = target.length ∧ ∀ count ∈ counts, count ≤ bound)) :
    SignedRatio.Equiv (μ.pmf target).toSignedRatio (inverseJointFactorialPMF μ bound target) := by
  let terms := fun orders counts => SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
    (QProb.ofNat (jointChoose orders counts)).toSignedRatio
  let kernel := fun counts => SignedRatio.listSum ((factorialBox target.length bound).map (fun orders => terms orders counts))
  let event := FiniteProbRecord.singletonEvent target
  have indicator : SignedRatio.Equiv (μ.rationalExpectation (fun counts =>
      if counts = target then SignedRatio.one else SignedRatio.zero)) (μ.pmf target).toSignedRatio := by
    refine SignedRatio.equiv_trans (μ.rationalExpectation_congr _
      (fun counts => (QProb.ofNat (if event counts then 1 else 0)).toSignedRatio) ?_) ?_
    · intro counts
      by_cases same : counts = target
      · simp only [event, FiniteProbRecord.singletonEvent, same, if_true, decide_true]
        exact SignedRatio.equiv_refl _
      · simp only [event, FiniteProbRecord.singletonEvent, same, if_false, decide_false, Bool.false_eq_true]
        exact SignedRatio.equiv_refl _
    · have result := μ.rationalExpectation_ofNat (fun counts => if event counts then 1 else 0)
      simpa only [Distro.expectNat, natIntegral_indicator, Distro.pmf, FiniteProbRecord.probVal] using result
  have singleton : SignedRatio.Equiv (μ.rationalExpectation kernel) (μ.pmf target).toSignedRatio := by
    refine SignedRatio.equiv_trans (μ.rationalExpectation_congr_positive kernel _ ?_) indicator
    intro atom member weight
    have data := support atom member weight
    have result := jointInverseBinomial_ratio_kernel atom.1 target bound data.1.symm data.2
    simpa only [data.1] using result
  have expansion := μ.rationalExpectation_listSum (factorialBox target.length bound) terms
  have moments := SignedRatio.listSum_map_congr (factorialBox target.length bound)
    (fun orders => μ.rationalExpectation (terms orders))
    (fun orders => SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
      (multivariateFactorialCoefficient μ orders).toSignedRatio)
    (fun orders => SignedRatio.equiv_trans (μ.rationalExpectation_mul_left _ _)
      (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (SignedRatio.equiv_trans (μ.rationalExpectation_ofNat _)
          (QProb.toSignedRatio_congr (QProb.equiv_symm (multivariateFactorialCoefficient_choose μ orders))))))
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm singleton) (SignedRatio.equiv_trans expansion moments)

end Thesis.Probability.Distros
