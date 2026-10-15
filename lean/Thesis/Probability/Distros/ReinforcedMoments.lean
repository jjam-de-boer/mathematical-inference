import Thesis.Probability.Distros.JointFactorialMoments
import Thesis.Probability.Distros.SignedCovariance
namespace Thesis.Probability.Distros
open Combinatorics

def coordinateProduct (factor : Nat → Nat → Nat) : List Nat → List Nat → Nat
  | [], [] => 1
  | value :: values, order :: orders => factor value order * coordinateProduct factor values orders
  | _, _ => 0

def singleOrders (length index order : Nat) : List Nat :=
  (List.replicate length 0).modify index (fun old => old + order)

def pairOrders (length i j : Nat) : List Nat :=
  ((List.replicate length 0).modify i (fun old => old + 1)).modify j (fun old => old + 1)

theorem coordinateProduct_zero (factor : Nat → Nat → Nat) (zero : ∀ value, factor value 0 = 1) (values : List Nat) :
    coordinateProduct factor values (List.replicate values.length 0) = 1 := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.length_cons, List.replicate_succ, coordinateProduct, zero, Nat.one_mul, ih]

theorem coordinateProduct_single (factor : Nat → Nat → Nat) (zero : ∀ value, factor value 0 = 1)
    (values : List Nat) (index order : Nat) (within : index < values.length) :
    coordinateProduct factor values (singleOrders values.length index order) = factor (values.getD index 0) order := by
  induction values generalizing index with
  | nil => simp only [List.length_nil] at within; omega
  | cons value values ih => cases index with
      | zero =>
          simp only [singleOrders, List.length_cons, List.replicate_succ, List.modify_zero_cons,
            Nat.zero_add, coordinateProduct, coordinateProduct_zero factor zero, Nat.mul_one, List.getD_cons_zero]
      | succ index =>
          simp only [singleOrders, List.length_cons, List.replicate_succ, List.modify_succ_cons,
            coordinateProduct, zero, Nat.one_mul, List.getD_cons_succ]
          exact ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)

theorem coordinateProduct_pair (factor : Nat → Nat → Nat) (zero : ∀ value, factor value 0 = 1)
    (one : ∀ value, factor value 1 = value) (values : List Nat) (i j : Nat)
    (hi : i < values.length) (hj : j < values.length) (different : i ≠ j) :
    coordinateProduct factor values (pairOrders values.length i j) = values.getD i 0 * values.getD j 0 := by
  induction values generalizing i j with
  | nil => simp only [List.length_nil] at hi; omega
  | cons value values ih =>
      cases i <;> cases j
      · exact False.elim (different rfl)
      · simp only [pairOrders, List.length_cons, List.replicate_succ, List.modify_zero_cons,
          List.modify_succ_cons, Nat.zero_add, coordinateProduct, one, List.getD_cons_zero, List.getD_cons_succ]
        have single := coordinateProduct_single factor zero values _ 1 (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hj)
        simp only [singleOrders, one] at single
        rw [single]
      · simp only [pairOrders, List.length_cons, List.replicate_succ, List.modify_zero_cons,
          List.modify_succ_cons, Nat.zero_add, coordinateProduct, one, List.getD_cons_zero, List.getD_cons_succ]
        have single := coordinateProduct_single factor zero values _ 1 (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)
        simp only [singleOrders, one] at single
        rw [single]
        exact Nat.mul_comm _ _
      · simp only [pairOrders, List.length_cons, List.replicate_succ, List.modify_succ_cons,
          coordinateProduct, zero, Nat.one_mul, List.getD_cons_succ]
        exact ih _ _ (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)
          (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hj) (by omega)

theorem singleOrders_length (length index order : Nat) : (singleOrders length index order).length = length := by
  simp only [singleOrders, List.length_modify, List.length_replicate]

theorem singleOrders_sum (length index order : Nat) (within : index < length) : (singleOrders length index order).sum = order := by
  rw [singleOrders, sum_modify_add _ index order (by simpa only [List.length_replicate] using within)]
  simp only [List.sum_replicate_nat, Nat.mul_zero, Nat.zero_add]

theorem pairOrders_length (length i j : Nat) : (pairOrders length i j).length = length := by
  simp only [pairOrders, List.length_modify, List.length_replicate]

theorem pairOrders_sum (length i j : Nat) (hi : i < length) (hj : j < length) : (pairOrders length i j).sum = 2 := by
  rw [pairOrders, sum_modify_add _ j 1 (by simpa only [List.length_modify, List.length_replicate] using hj),
    sum_modify_add _ i 1 (by simpa only [List.length_replicate] using hi)]
  simp only [List.sum_replicate_nat, Nat.mul_zero, Nat.zero_add]

theorem jointFalling_product (counts orders : List Nat) : jointFalling orders counts = coordinateProduct fallingFactorial counts orders := by
  induction counts generalizing orders with
  | nil => cases orders <;> rfl
  | cons count counts ih => cases orders <;> simp only [jointFalling, coordinateProduct, ih]

theorem stepKernel_product (increment : Nat) (alphas orders : List Nat) :
    stepKernel increment alphas orders = coordinateProduct (fun alpha order => stepRising alpha increment order) alphas orders := by
  induction alphas generalizing orders with
  | nil => cases orders <;> rfl
  | cons alpha alphas ih => cases orders <;> simp only [stepKernel, coordinateProduct, ih]

theorem fallingFactorial_order_one (value : Nat) : fallingFactorial value 1 = value := by
  simp only [fallingFactorial, Nat.mul_one]

theorem stepRising_order_one (value increment : Nat) : stepRising value increment 1 = value := by
  simp only [stepRising, Nat.mul_one]

/-- The mixed second moment for any reinforcement increment. -/
theorem reinforcedCount_crossMoment (n increment : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (i j : Nat) (hi : i < alphas.length) (hj : j < alphas.length) (different : i ≠ j) :
    QProb.Equiv ((reinforcedCountDistro n alphas increment positive).expectNat
      (fun counts => counts.getD i 0 * counts.getD j 0))
      ⟨n * (n - 1) * alphas.getD i 0 * alphas.getD j 0, alphas.sum * (alphas.sum + increment),
        Nat.mul_pos positive (by omega)⟩ := by
  let orders := pairOrders alphas.length i j
  have joint := reinforcedCount_jointFactorialMoment n increment alphas orders positive (pairOrders_length _ _ _)
  have factors : stepKernel increment alphas orders = alphas.getD i 0 * alphas.getD j 0 := by
    rw [stepKernel_product]
    exact coordinateProduct_pair _ (fun _ => rfl) (fun a => stepRising_order_one a increment) alphas i j hi hj different
  have orderSum : orders.sum = 2 := pairOrders_sum _ _ _ hi hj
  have obs := (reinforcedCountDistro n alphas increment positive).expectNat_congr_on_support
    (fun counts => counts.getD i 0 * counts.getD j 0) (jointFalling orders) (by
      intro atom member
      have dimension := (reinforcedCount_support n alphas increment atom member).1
      rw [jointFalling_product]
      have h := coordinateProduct_pair fallingFactorial (fun _ => rfl) fallingFactorial_order_one
        atom.1 i j (by omega) (by omega) different
      simpa only [dimension] using h.symm)
  rw [obs]
  simpa only [jointFactorialMoment, orderSum, factors, fallingFactorial, stepRising, Nat.mul_one, Nat.mul_assoc] using joint

/-- Individual falling moments extracted from the mixed-order theorem. -/
theorem reinforcedCount_coordinate_factorialMoment (n increment : Nat) (alphas : List Nat)
    (positive : 0 < alphas.sum) (i order : Nat) (within : i < alphas.length) :
    QProb.Equiv ((reinforcedCountDistro n alphas increment positive).expectNat
      (fun counts => fallingFactorial (counts.getD i 0) order))
      ⟨fallingFactorial n order * stepRising (alphas.getD i 0) increment order,
        stepRising alphas.sum increment order, stepRising_pos _ _ _ positive⟩ := by
  let orders := singleOrders alphas.length i order
  have joint := reinforcedCount_jointFactorialMoment n increment alphas orders positive (singleOrders_length _ _ _)
  have factors : stepKernel increment alphas orders = stepRising (alphas.getD i 0) increment order := by
    rw [stepKernel_product]
    exact coordinateProduct_single _ (fun _ => rfl) alphas i order within
  have orderSum : orders.sum = order := singleOrders_sum _ _ _ within
  have obs := (reinforcedCountDistro n alphas increment positive).expectNat_congr_on_support
    (fun counts => fallingFactorial (counts.getD i 0) order) (jointFalling orders) (by
      intro atom member
      have dimension := (reinforcedCount_support n alphas increment atom member).1
      rw [jointFalling_product]
      have h := coordinateProduct_single fallingFactorial (fun _ => rfl) atom.1 i order (by omega)
      simpa only [dimension] using h.symm)
  rw [obs]
  simpa only [jointFactorialMoment, orderSum, factors] using joint

theorem reinforcedCount_coordinate_mean (n increment : Nat) (alphas : List Nat)
    (positive : 0 < alphas.sum) (i : Nat) (within : i < alphas.length) :
    QProb.Equiv ((reinforcedCountDistro n alphas increment positive).expectNat (fun counts => counts.getD i 0))
      ⟨n * alphas.getD i 0, alphas.sum, positive⟩ := by
  simpa only [fallingFactorial_order_one, stepRising_order_one] using
    reinforcedCount_coordinate_factorialMoment n increment alphas positive i 1 within

/-- Off-diagonal covariance for arbitrary reinforcement. It is nonpositive;
zero trials or a zero selected parameter give zero covariance. -/
theorem reinforcedCount_covariance (n increment : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (i j : Nat) (hi : i < alphas.length) (hj : j < alphas.length) (different : i ≠ j) :
    SignedMoment.Equiv ((reinforcedCountDistro n alphas increment positive).covariance
      (fun counts => counts.getD i 0) (fun counts => counts.getD j 0))
      ⟨-((n * alphas.getD i 0 * alphas.getD j 0 * (alphas.sum + increment * n) : Nat) : Int),
        alphas.sum * alphas.sum * (alphas.sum + increment),
        Nat.mul_pos (Nat.mul_pos positive positive) (by omega)⟩ := by
  let μ := reinforcedCountDistro n alphas increment positive
  let D : Int := μ.record.den
  let S : Int := alphas.sum
  let A : Int := alphas.getD i 0
  let B : Int := alphas.getD j 0
  let F : Int := natIntegral μ.record.atoms (fun counts => counts.getD i 0)
  let G : Int := natIntegral μ.record.atoms (fun counts => counts.getD j 0)
  let H : Int := natIntegral μ.record.atoms (fun counts => counts.getD i 0 * counts.getD j 0)
  have fm := reinforcedCount_coordinate_mean n increment alphas positive i hi
  have gm := reinforcedCount_coordinate_mean n increment alphas positive j hj
  have hm := reinforcedCount_crossMoment n increment alphas positive i j hi hj different
  change _ * alphas.sum = n * alphas.getD i 0 * μ.record.den at fm
  change _ * alphas.sum = n * alphas.getD j 0 * μ.record.den at gm
  change _ * (alphas.sum * (alphas.sum + increment)) = n * (n - 1) * alphas.getD i 0 * alphas.getD j 0 * μ.record.den at hm
  have f : F * S = (n : Int) * A * D := by
    have h := congrArg (fun x : Nat => (x : Int)) fm
    simpa only [Int.natCast_mul] using h
  have g : G * S = (n : Int) * B * D := by
    have h := congrArg (fun x : Nat => (x : Int)) gm
    simpa only [Int.natCast_mul] using h
  have h : H * (S * (S + increment)) = ((n * (n - 1) : Nat) : Int) * A * B * D := by
    have h := congrArg (fun x : Nat => (x : Int)) hm
    simpa only [Int.natCast_mul, Int.natCast_add] using h
  change (D * H - F * G) * ((alphas.sum * alphas.sum * (alphas.sum + increment) : Nat) : Int) =
    -((n * alphas.getD i 0 * alphas.getD j 0 * (alphas.sum + increment * n) : Nat) : Int) *
      ((μ.record.den * μ.record.den : Nat) : Int)
  simp only [Int.natCast_mul, Int.natCast_add]
  change (D * H - F * G) * (S * S * (S + increment)) =
    -((n : Int) * A * B * (S + increment * n)) * (D * D)
  calc
    _ = D * S * (H * (S * (S + increment))) - (F * S) * (G * S) * (S + increment) := by
      rw [Int.sub_mul]
      congr 1 <;> ac_rfl
    _ = (((n * (n - 1) : Nat) : Int) * S - (n : Int) * n * (S + increment)) * A * B * (D * D) := by
      rw [f, g, h]
      simp only [Int.sub_mul]
      congr 1 <;> ac_rfl
    _ = _ := by
      have balance := congrArg (fun x : Nat => (x : Int)) (nat_falling_square n)
      simp only [Int.natCast_add, Int.natCast_mul] at balance
      have count : ((n * (n - 1) : Nat) : Int) - (n : Int) * n = -(n : Int) := by
        simp only [Int.natCast_mul]; omega
      have coefficient : ((n * (n - 1) : Nat) : Int) * S - (n : Int) * n * (S + increment) =
          -(n : Int) * (S + increment * n) := by
        calc
          _ = (((n * (n - 1) : Nat) : Int) - (n : Int) * n) * S - (n : Int) * n * increment := by
            simp only [Int.sub_mul, Int.mul_add]; omega
          _ = _ := by
            rw [count]
            simp only [Int.mul_add, Int.neg_mul, Int.sub_eq_add_neg]
            congr 1
            congr 1
            ac_rfl
      rw [coefficient]
      simp only [Int.neg_mul]
      congr 1
      ac_rfl

/-- Distinct Dirichlet-multinomial coordinates have negative covariance
when the trial count and both selected parameters are positive. -/
theorem dirichletMultinomial_crossMoment (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (i j : Nat) (hi : i < alphas.length) (hj : j < alphas.length) (different : i ≠ j) :
    QProb.Equiv ((dirichletMultinomialDistro n alphas positive).expectNat
      (fun counts => counts.getD i 0 * counts.getD j 0))
      ⟨n * (n - 1) * alphas.getD i 0 * alphas.getD j 0, alphas.sum * (alphas.sum + 1),
        Nat.mul_pos positive (Nat.succ_pos _)⟩ := by
  simpa only [reinforcedCount_one] using reinforcedCount_crossMoment n 1 alphas positive i j hi hj different

theorem dirichletMultinomial_covariance (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (i j : Nat) (hi : i < alphas.length) (hj : j < alphas.length) (different : i ≠ j) :
    SignedMoment.Equiv ((dirichletMultinomialDistro n alphas positive).covariance
      (fun counts => counts.getD i 0) (fun counts => counts.getD j 0))
      ⟨-((n * alphas.getD i 0 * alphas.getD j 0 * (alphas.sum + n) : Nat) : Int),
        alphas.sum * alphas.sum * (alphas.sum + 1),
        Nat.mul_pos (Nat.mul_pos positive positive) (Nat.succ_pos _)⟩ := by
  simpa only [reinforcedCount_one, Nat.one_mul] using reinforcedCount_covariance n 1 alphas positive i j hi hj different

end Thesis.Probability.Distros
