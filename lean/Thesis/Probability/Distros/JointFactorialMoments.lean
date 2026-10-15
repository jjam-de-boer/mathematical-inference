import Thesis.Probability.Distros.FactorialConvolution
import Thesis.Probability.Distros.RationalPolya
namespace Thesis.Probability.Distros
open Combinatorics

/-- Product of the coordinate falling factorials, with explicit dimension. -/
def jointFalling : List Nat → List Nat → Nat
  | [], [] => 1
  | order :: orders, count :: counts => fallingFactorial count order * jointFalling orders counts
  | _, _ => 0

def jointFactorialMoment (μ : Distro (List Nat)) (orders : List Nat) : QProb := μ.expectNat (jointFalling orders)

theorem natIntegral_flatMap (values : List α) (atoms : α → List (Ω × Nat)) (f : Ω → Nat) :
    natIntegral (values.flatMap atoms) f = (values.map (fun x => natIntegral (atoms x) f)).sum := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.flatMap_cons, natIntegral_append, List.map_cons, List.sum_cons, ih]

theorem natIntegral_map_weight (atoms : List (Ω × Nat)) (encode : Ω → X) (factor : Nat) (f : X → Nat) :
    natIntegral (atoms.map (fun atom => (encode atom.1, factor * atom.2))) f =
      factor * natIntegral atoms (fun x => f (encode x)) := by
  induction atoms with
  | nil => simp only [List.map_nil, natIntegral, Nat.mul_zero]
  | cons atom atoms ih => simp only [List.map_cons, natIntegral, ih, Nat.mul_add]; ac_rfl

theorem natIntegral_scale_left (atoms : List (Ω × Nat)) (factor : Nat) (f : Ω → Nat) :
    natIntegral atoms (fun x => factor * f x) = factor * natIntegral atoms f := by
  rw [natIntegral_congr _ _ (fun x => f x * factor) (fun x => Nat.mul_comm _ _), natIntegral_mul]
  ac_rfl

theorem reinforcedCountAtoms_cons (n alpha increment : Nat) (alphas : List Nat) :
    reinforcedCountAtoms n (alpha :: alphas) increment =
      (List.range (n + 1)).flatMap (fun used =>
        (reinforcedCountAtoms (n - used) alphas increment).map
          (fun atom => (used :: atom.1, binom n used * stepRising alpha increment used * atom.2))) := by
  simp only [reinforcedCountAtoms, List.length_cons, List.replicate_succ, multinomialAtoms,
    List.map_flatMap, List.map_map, Function.comp_def, stepKernel, Nat.one_pow, Nat.mul_one]
  apply congrArg (fun f => (List.range (n + 1)).flatMap f)
  funext used
  apply List.map_congr_left
  intro atom _
  ac_rfl

/-- The unnormalised joint factorial integral, valid even for zero total
parameters and orders above the finite trial count. -/
theorem reinforcedCount_joint_integral (n increment : Nat) (alphas orders : List Nat)
    (dimension : orders.length = alphas.length) :
    natIntegral (reinforcedCountAtoms n alphas increment) (jointFalling orders) =
      fallingFactorial n orders.sum * stepKernel increment alphas orders *
        stepRising (alphas.sum + increment * orders.sum) increment (n - orders.sum) := by
  induction alphas generalizing orders n with
  | nil =>
      cases orders with
      | nil =>
          cases n with
          | zero => rfl
          | succ n =>
              simp only [reinforcedCountAtoms, List.length_nil, List.replicate_zero, multinomialAtoms,
                if_neg (Nat.ne_of_gt (Nat.succ_pos n)), List.map_nil, natIntegral, List.sum_nil,
                fallingFactorial, stepKernel, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
                Nat.sub_zero, stepRising, Nat.zero_mul]
      | cons order orders => simp only [List.length_cons, List.length_nil] at dimension; omega
  | cons alpha alphas ih =>
      cases orders with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons order orders =>
          rw [reinforcedCountAtoms_cons, natIntegral_flatMap, sum_map_range_natSum]
          have rows : natSum (n + 1) (fun used =>
              natIntegral ((reinforcedCountAtoms (n - used) alphas increment).map
                (fun atom => (used :: atom.1, binom n used * stepRising alpha increment used * atom.2)))
                (jointFalling (order :: orders))) =
            stepKernel increment alphas orders * natSum (n + 1) (fun used =>
              fallingFactorial (n - used) orders.sum * binom n used *
                (fallingFactorial used order * stepRising alpha increment used *
                  stepRising (alphas.sum + increment * orders.sum) increment (n - used - orders.sum))) := by
            rw [← natSum_mul_left]
            apply natSum_congr
            intro used _
            rw [natIntegral_map_weight]
            change binom n used * stepRising alpha increment used *
              natIntegral (reinforcedCountAtoms (n - used) alphas increment)
                (fun counts => fallingFactorial used order * jointFalling orders counts) = _
            rw [natIntegral_scale_left, ih (n - used) orders (Nat.succ.inj dimension)]
            ac_rfl
          rw [rows, binomial_complement_factorial_sum n orders.sum (fun used rest =>
            fallingFactorial used order * stepRising alpha increment used *
              stepRising (alphas.sum + increment * orders.sum) increment rest)]
          have terms : natSum (n - orders.sum + 1) (fun used => binom (n - orders.sum) used *
              (fallingFactorial used order * stepRising alpha increment used *
                stepRising (alphas.sum + increment * orders.sum) increment (n - orders.sum - used))) =
            natSum (n - orders.sum + 1) (fun used => fallingFactorial used order *
              stepBetaTerm increment (n - orders.sum) alpha (alphas.sum + increment * orders.sum) used) := by
            apply natSum_congr; intro used _; simp only [stepBetaTerm]; ac_rfl
          rw [terms, stepBetaTerm_factorial_moment]
          have parameter : alpha + (alphas.sum + increment * orders.sum) + increment * order =
              (alpha :: alphas).sum + increment * (order :: orders).sum := by
            simp only [List.sum_cons, Nat.mul_add]
            omega
          have exponent : n - orders.sum - order = n - (order :: orders).sum := by simp only [List.sum_cons]; omega
          rw [parameter, exponent]
          calc
            _ = (fallingFactorial n orders.sum * fallingFactorial (n - orders.sum) order) *
                (stepRising alpha increment order * stepKernel increment alphas orders) *
                  stepRising ((alpha :: alphas).sum + increment * (order :: orders).sum) increment (n - (order :: orders).sum) := by ac_rfl
            _ = _ := by rw [← fallingFactorial_add, Nat.add_comm orders.sum order]; rfl

theorem Distro.SameLaw.jointFactorialMoment {μ ν : Distro (List Nat)} (same : μ.SameLaw ν) (orders : List Nat) :
    QProb.Equiv (jointFactorialMoment μ orders) (jointFactorialMoment ν orders) := same.expectNat _

/-- All joint factorial moments of the reinforced count law, including
orders above the trial count and zero individual colour parameters. -/
theorem reinforcedCount_jointFactorialMoment (n increment : Nat) (alphas orders : List Nat)
    (positive : 0 < alphas.sum) (dimension : orders.length = alphas.length) :
    QProb.Equiv (jointFactorialMoment (reinforcedCountDistro n alphas increment positive) orders)
      ⟨fallingFactorial n orders.sum * stepKernel increment alphas orders,
        stepRising alphas.sum increment orders.sum, stepRising_pos _ _ _ positive⟩ := by
  change natIntegral (reinforcedCountAtoms n alphas increment) (jointFalling orders) *
      stepRising alphas.sum increment orders.sum =
    (fallingFactorial n orders.sum * stepKernel increment alphas orders) *
      (reinforcedCountDistro n alphas increment positive).record.den
  rw [reinforcedCount_joint_integral n increment alphas orders dimension, reinforcedCount_den]
  by_cases within : orders.sum ≤ n
  · have split : stepRising alphas.sum increment n = stepRising alphas.sum increment orders.sum *
        stepRising (alphas.sum + increment * orders.sum) increment (n - orders.sum) := by
      simpa only [Nat.add_sub_of_le within] using stepRising_add alphas.sum increment orders.sum (n - orders.sum)
    rw [split]
    ac_rfl
  · rw [fallingFactorial_eq_zero n orders.sum (by omega)]
    simp only [Nat.zero_mul]

/-- Multinomial mixed falling factorials: total falling order times the
product of weight powers, over the total weight to that order. -/
theorem multinomial_jointFactorialMoment (n : Nat) (weights orders : List Nat)
    (positive : 0 < weights.sum) (dimension : orders.length = weights.length) :
    QProb.Equiv (jointFactorialMoment (multinomialDistro n weights positive) orders)
      ⟨fallingFactorial n orders.sum * natMonomial weights orders, weights.sum ^ orders.sum, Nat.pow_pos positive⟩ := by
  refine QProb.equiv_trans (QProb.equiv_symm ((reinforcedCount_zero n weights positive).jointFactorialMoment orders)) ?_
  simpa only [stepKernel_zero, stepRising_zero] using
    reinforcedCount_jointFactorialMoment n 0 weights orders positive dimension

/-- Dirichlet-multinomial mixed falling factorials: total falling order
multiplied by the coordinate rising factors, over the rising total. -/
theorem dirichletMultinomial_jointFactorialMoment (n : Nat) (alphas orders : List Nat)
    (positive : 0 < alphas.sum) (dimension : orders.length = alphas.length) :
    QProb.Equiv (jointFactorialMoment (dirichletMultinomialDistro n alphas positive) orders)
      ⟨fallingFactorial n orders.sum * risingKernel alphas orders,
        risingFactorial alphas.sum orders.sum, risingFactorial_pos _ _ positive⟩ := by
  have h := reinforcedCount_jointFactorialMoment n 1 alphas orders positive dimension
  simpa only [reinforcedCount_one, stepKernel_one, stepRising_one] using h

theorem rationalDirichletMultinomial_jointFactorialMoment (n : Nat) (alphas : List QProb) (orders : List Nat)
    (positive : 0 < (QProb.listSum alphas).num) (dimension : orders.length = alphas.length) :
    QProb.Equiv (jointFactorialMoment (rationalDirichletMultinomialDistro n alphas positive) orders)
      ⟨fallingFactorial n orders.sum * stepKernel (QProb.listSum alphas).den (rationalUrnWeights alphas) orders,
        stepRising (QProb.listSum alphas).num (QProb.listSum alphas).den orders.sum,
        stepRising_pos _ _ _ positive⟩ := by
  have h := reinforcedCount_jointFactorialMoment n (QProb.listSum alphas).den (rationalUrnWeights alphas) orders
    (by rw [rationalUrnWeights_sum]; exact positive) (dimension.trans (rationalUrnWeights_length alphas).symm)
  simpa only [rationalUrnWeights_sum] using h

end Thesis.Probability.Distros
