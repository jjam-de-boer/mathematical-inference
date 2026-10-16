import Thesis.Probability.Distros.FactorialPGF
import Thesis.Probability.Distros.JointFactorialMoments

namespace Thesis.Probability.Distros
open Combinatorics

/-- Rectangular finite set of mixed orders, including the unique empty order. -/
def factorialBox : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | length + 1, bound => (List.range (bound + 1)).flatMap (fun order =>
      (factorialBox length bound).map (fun orders => order :: orders))

theorem factorialBox_mem (length bound : Nat) (orders : List Nat) (member : orders ∈ factorialBox length bound) :
    orders.length = length ∧ ∀ order ∈ orders, order ≤ bound := by
  induction length generalizing orders with
  | zero =>
      have same := List.mem_singleton.mp member
      cases same
      exact ⟨rfl, fun _ impossible => nomatch impossible⟩
  | succ length ih =>
      rcases List.mem_flatMap.mp member with ⟨order, within, tail⟩
      rcases List.mem_map.mp tail with ⟨orders, horders, same⟩
      cases same
      have shape := ih orders horders
      refine ⟨by simp only [List.length_cons, shape.1], fun other member => ?_⟩
      rcases List.mem_cons.mp member with same | member
      · subst other; have upper := List.mem_range.mp within; omega
      · exact shape.2 other member

/-- Product of the coordinate factorial denominators. -/
def orderFactorial : List Nat → Nat
  | [] => 1
  | order :: orders => fallingFactorial order order * orderFactorial orders

theorem orderFactorial_pos (orders : List Nat) : 0 < orderFactorial orders := by
  induction orders with
  | nil => exact Nat.zero_lt_one
  | cons order orders ih => exact Nat.mul_pos (fallingFactorial_pos order order (Nat.le_refl _)) ih

def jointChoose : List Nat → List Nat → Nat
  | [], [] => 1
  | order :: orders, count :: counts => binom count order * jointChoose orders counts
  | _, _ => 0

theorem jointFalling_choose (orders counts : List Nat) :
    jointFalling orders counts = jointChoose orders counts * orderFactorial orders := by
  induction orders generalizing counts with
  | nil => cases counts <;> rfl
  | cons order orders ih => cases counts with
      | nil => simp only [jointFalling, jointChoose, Nat.zero_mul]
      | cons count counts =>
          simp only [jointFalling, jointChoose, orderFactorial, fallingFactorial_binom, ih]
          ac_rfl

/-- The mixed factorial moment divided by the product of order factorials. -/
def multivariateFactorialCoefficient (μ : Distro (List Nat)) (orders : List Nat) : QProb :=
  QProb.div (jointFactorialMoment μ orders) (QProb.ofNat (orderFactorial orders)) (orderFactorial_pos orders)

theorem multivariateFactorialCoefficient_choose (μ : Distro (List Nat)) (orders : List Nat) :
    QProb.Equiv (multivariateFactorialCoefficient μ orders) (μ.expectNat (jointChoose orders)) := by
  have falling : jointFactorialMoment μ orders = μ.expectNat (fun counts => jointChoose orders counts * orderFactorial orders) := by
    apply μ.expectNat_congr_on_support
    intro atom _
    exact jointFalling_choose orders atom.1
  unfold multivariateFactorialCoefficient
  rw [falling]
  refine QProb.equiv_trans (QProb.div_congr (μ.expectNat_scale _ _)
    (QProb.equiv_refl _) (orderFactorial_pos orders) (orderFactorial_pos orders)) ?_
  simp only [QProb.Equiv, QProb.div, QProb.scale, QProb.ofNat]
  ac_rfl

theorem factorialBox_listSum (length bound : Nat) (f : List Nat → QProb) :
    QProb.Equiv (QProb.listSum ((factorialBox (length + 1) bound).map f))
      (QProb.listSum ((List.range (bound + 1)).map (fun order =>
        QProb.listSum ((factorialBox length bound).map (fun orders => f (order :: orders)))))) := by
  rw [factorialBox, List.map_flatMap]
  simpa only [List.map_map, Function.comp_def] using
    QProb.listSum_flatMap (List.range (bound + 1))
      (fun order => (factorialBox length bound).map (fun orders => f (order :: orders)))

private theorem scale_mul_scale (a b : Nat) (p q : QProb) :
    QProb.Equiv (QProb.mul (QProb.scale a p) (QProb.scale b q)) (QProb.scale (a * b) (QProb.mul p q)) := by
  simp only [QProb.Equiv, QProb.mul, QProb.scale]
  ac_rfl

/-- The finite product of bounded binomial expansions, with rectangular
padding only by coefficients which actually vanish above each coordinate. -/
theorem multivariateMonomial_add_one (args : List QProb) (counts : List Nat) (bound : Nat)
    (dimension : counts.length = args.length) (bounded : ∀ count ∈ counts, count ≤ bound) :
    QProb.Equiv (multivariateMonomial (args.map (fun t => QProb.add t QProb.one)) counts)
      (QProb.listSum ((factorialBox args.length bound).map (fun orders =>
        QProb.scale (jointChoose orders counts) (multivariateMonomial args orders)))) := by
  induction args generalizing counts with
  | nil => cases counts with
      | nil => exact QProb.equiv_refl _
      | cons count counts => simp only [List.length_cons, List.length_nil] at dimension; exact False.elim (by omega)
  | cons arg args ih => cases counts with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; exact False.elim (by omega)
      | cons count counts =>
          simp only [List.map_cons, multivariateMonomial, List.length_cons]
          refine QProb.equiv_trans (QProb.mul_congr
            (qpow_add_one_bounded count bound (bounded count (List.mem_cons_self ..)) arg)
            (ih counts (Nat.succ.inj dimension) (fun other member => bounded other (List.mem_cons_of_mem _ member)))) ?_
          have product := QProb.listSum_mul_listSum
            ((List.range (bound + 1)).map (fun order => QProb.scale (binom count order) (qpow arg order)))
            ((factorialBox args.length bound).map (fun orders => QProb.scale (jointChoose orders counts) (multivariateMonomial args orders)))
          simp only [List.map_map, Function.comp_def] at product
          refine QProb.equiv_trans product ?_
          refine QProb.equiv_trans (QProb.listSum_map_congr (List.range (bound + 1)) _ _ (fun order =>
            QProb.listSum_map_congr (factorialBox args.length bound) _ _ (fun orders => scale_mul_scale _ _ _ _))) ?_
          exact QProb.equiv_symm (factorialBox_listSum args.length bound
            (fun orders => QProb.scale (jointChoose orders (count :: counts)) (multivariateMonomial (arg :: args) orders)))

/-- Exact finite mixed-factorial expansion
G(1+t_1,...,1+t_k) = sum_r E[product_i (X_i)_(r_i)] product_i t_i^(r_i) / product_i r_i!.
All offsets are arbitrary nonnegative rational values. -/
theorem multivariatePGF_factorial_expansion (μ : Distro (List Nat)) (args : List QProb) (bound : Nat)
    (support : ∀ atom ∈ μ.record.atoms, atom.1.length = args.length ∧ ∀ count ∈ atom.1, count ≤ bound) :
    QProb.Equiv (multivariatePGF μ (args.map (fun t => QProb.add t QProb.one)))
      (QProb.listSum ((factorialBox args.length bound).map (fun orders =>
        QProb.mul (multivariateFactorialCoefficient μ orders) (multivariateMonomial args orders)))) := by
  refine QProb.equiv_trans (μ.expectation_congr_on_support _ _ (fun atom member =>
    multivariateMonomial_add_one args atom.1 bound (support atom member).1 (support atom member).2)) ?_
  refine QProb.equiv_trans (μ.expectation_listSum (factorialBox args.length bound)
    (fun orders counts => QProb.scale (jointChoose orders counts) (multivariateMonomial args orders))) ?_
  apply QProb.listSum_map_congr
  intro orders
  refine QProb.equiv_trans (μ.expectation_congr _
    (fun counts => QProb.mul (multivariateMonomial args orders) (QProb.ofNat (jointChoose orders counts))) (fun counts => ?_)) ?_
  · simp only [QProb.Equiv, QProb.scale, QProb.mul, QProb.ofNat, Nat.mul_one]
    ac_rfl
  · exact QProb.equiv_trans (μ.expectation_scale _ _)
      (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) (μ.expectation_nat _))
        (QProb.equiv_trans (QProb.mul_comm _ _)
          (QProb.mul_congr (QProb.equiv_symm (multivariateFactorialCoefficient_choose μ orders)) (QProb.equiv_refl _))))

end Thesis.Probability.Distros
