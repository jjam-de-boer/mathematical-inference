import Thesis.Probability.Distros.MultivariateHypergeometric
import Thesis.Probability.Distros.FallingConvolution
import Thesis.Probability.Distros.ReinforcedMoments
import Thesis.Probability.Distros.FactorialPGF

namespace Thesis.Probability.Distros
open Combinatorics

/-- Ordered-draw multiplicity version of the same occupancy law. -/
def multicolourDepletingCountAtoms (n : Nat) (stocks : List Nat) : List (List Nat × Nat) :=
  (multinomialAtoms n (List.replicate stocks.length 1)).map
    (fun atom => (atom.1, atom.2 * jointFalling atom.1 stocks))

theorem multicolourDepletingCountAtoms_cons (n stock : Nat) (stocks : List Nat) :
    multicolourDepletingCountAtoms n (stock :: stocks) =
      (List.range (n + 1)).flatMap (fun used =>
        (multicolourDepletingCountAtoms (n - used) stocks).map
          (fun atom => (used :: atom.1, binom n used * fallingFactorial stock used * atom.2))) := by
  simp only [multicolourDepletingCountAtoms, List.length_cons, List.replicate_succ, multinomialAtoms,
    List.map_flatMap, List.map_map, Function.comp_def, jointFalling, Nat.one_pow, Nat.mul_one]
  apply congrArg (fun f => (List.range (n + 1)).flatMap f)
  funext used
  apply List.map_congr_left
  intro atom _
  ac_rfl

private theorem flatMap_congr_mem (values : List α) (f g : α → List β)
    (same : ∀ x ∈ values, f x = g x) : values.flatMap f = values.flatMap g := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [List.flatMap_cons, List.flatMap_cons, same value (List.mem_cons_self ..),
        ih (fun x member => same x (List.mem_cons_of_mem _ member))]

/-- Every unordered selection is represented by exactly `n!` ordered draws. -/
theorem multicolourDepletingCountAtoms_selection (n : Nat) (stocks : List Nat) :
    multicolourDepletingCountAtoms n stocks =
      (multivariateHypergeometricAtoms n stocks).map (fun atom => (atom.1, fallingFactorial n n * atom.2)) := by
  induction stocks generalizing n with
  | nil => cases n with
      | zero => rfl
      | succ n =>
          simp only [multicolourDepletingCountAtoms, List.length_nil, List.replicate_zero,
            multinomialAtoms, multivariateHypergeometricAtoms, if_neg (Nat.ne_of_gt (Nat.succ_pos n)), List.map_nil]
  | cons stock stocks ih =>
      rw [multicolourDepletingCountAtoms_cons, multivariateHypergeometricAtoms, List.map_flatMap]
      apply flatMap_congr_mem
      intro used member
      rw [ih]
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro atom _
      apply Prod.ext
      · rfl
      · change binom n used * fallingFactorial stock used * (fallingFactorial (n - used) (n - used) * atom.2) =
          fallingFactorial n n * (binom stock used * atom.2)
        rw [fallingFactorial_binom stock used]
        calc
          _ = (binom n used * fallingFactorial used used * fallingFactorial (n - used) (n - used)) *
              binom stock used * atom.2 := by ac_rfl
          _ = _ := by rw [binom_factorial_split n used (by have h := List.mem_range.mp member; omega)]; ac_rfl

private theorem multicolourDepletingCount_totalMass (n : Nat) (stocks : List Nat) :
    FiniteProbRecord.totalMass (multicolourDepletingCountAtoms n stocks) = fallingFactorial stocks.sum n := by
  rw [multicolourDepletingCountAtoms_selection, FiniteProbRecord.totalMass_map_weight, multivariateHypergeometric_totalMass]
  exact (fallingFactorial_binom stocks.sum n).symm

def multicolourDepletingCountDistro (n : Nat) (stocks : List Nat) (positive : 0 < binom stocks.sum n) : Distro (List Nat) :=
  ⟨⟨multicolourDepletingCountAtoms n stocks, fallingFactorial stocks.sum n,
    (by rw [fallingFactorial_binom]; exact Nat.mul_pos (fallingFactorial_pos n n (Nat.le_refl _)) positive),
    multicolourDepletingCount_totalMass n stocks⟩⟩

theorem multicolourDepletingCount_sameLaw (n : Nat) (stocks : List Nat) (positive : 0 < binom stocks.sum n) :
    (multicolourDepletingCountDistro n stocks positive).SameLaw (multivariateHypergeometricDistro n stocks positive) := by
  have same : multicolourDepletingCountDistro n stocks positive =
      (multivariateHypergeometricDistro n stocks positive).rescaleWeights (fallingFactorial n n)
        (fallingFactorial_pos n n (Nat.le_refl _)) := by
    apply Distro.eq_of_atoms
    exact multicolourDepletingCountAtoms_selection n stocks
  rw [same]
  exact Distro.rescaleWeights_sameLaw _ _ _

/-- Unnormalized mixed factorial moments, including all orders above the
sample size or any colour stock. No vanishing factor is cancelled. -/
theorem multicolourDepletingCount_joint_integral (n : Nat) (stocks orders : List Nat)
    (dimension : orders.length = stocks.length) :
    natIntegral (multicolourDepletingCountAtoms n stocks) (jointFalling orders) =
      fallingFactorial n orders.sum * jointFalling orders stocks *
        fallingFactorial (stocks.sum - orders.sum) (n - orders.sum) := by
  induction stocks generalizing orders n with
  | nil => cases orders with
      | nil => cases n with
          | zero => rfl
          | succ n =>
              simp only [multicolourDepletingCountAtoms, List.length_nil, List.replicate_zero, multinomialAtoms,
                if_neg (Nat.ne_of_gt (Nat.succ_pos n)), List.map_nil, natIntegral, List.sum_nil,
                fallingFactorial, jointFalling, Nat.mul_one, Nat.sub_zero, Nat.zero_mul]
      | cons order orders => have dim := dimension; simp only [List.length_cons, List.length_nil] at dim; exact False.elim (by omega)
  | cons stock stocks ih => cases orders with
      | nil => have dim := dimension; simp only [List.length_cons, List.length_nil] at dim; exact False.elim (by omega)
      | cons order orders =>
          rw [multicolourDepletingCountAtoms_cons, natIntegral_flatMap, sum_map_range_natSum]
          have rows : natSum (n + 1) (fun used =>
              natIntegral ((multicolourDepletingCountAtoms (n - used) stocks).map
                (fun atom => (used :: atom.1, binom n used * fallingFactorial stock used * atom.2)))
                (jointFalling (order :: orders))) =
            jointFalling orders stocks * natSum (n + 1) (fun used =>
              fallingFactorial (n - used) orders.sum * binom n used *
                (fallingFactorial used order * fallingFactorial stock used *
                  fallingFactorial (stocks.sum - orders.sum) (n - used - orders.sum))) := by
            rw [← natSum_mul_left]
            apply natSum_congr
            intro used _
            rw [natIntegral_map_weight]
            change binom n used * fallingFactorial stock used *
              natIntegral (multicolourDepletingCountAtoms (n - used) stocks)
                (fun counts => fallingFactorial used order * jointFalling orders counts) = _
            rw [natIntegral_scale_left, ih (n - used) orders (Nat.succ.inj dimension)]
            ac_rfl
          rw [rows, binomial_complement_factorial_sum n orders.sum (fun used rest =>
            fallingFactorial used order * fallingFactorial stock used * fallingFactorial (stocks.sum - orders.sum) rest)]
          have terms : natSum (n - orders.sum + 1) (fun used => binom (n - orders.sum) used *
              (fallingFactorial used order * fallingFactorial stock used * fallingFactorial (stocks.sum - orders.sum) (n - orders.sum - used))) =
            natSum (n - orders.sum + 1) (fun used => fallingFactorial used order *
              (binom (n - orders.sum) used * fallingFactorial stock used * fallingFactorial (stocks.sum - orders.sum) (n - orders.sum - used))) := by
            apply natSum_congr
            intro used _
            ac_rfl
          rw [terms, fallingBeta_factorial_moment]
          by_cases supportedOrders : orders.sum ≤ stocks.sum
          · have parameter : stock + (stocks.sum - orders.sum) - order = (stock :: stocks).sum - (order :: orders).sum := by
              simp only [List.sum_cons]
              omega
            have exponent : n - orders.sum - order = n - (order :: orders).sum := by simp only [List.sum_cons]; omega
            rw [parameter, exponent]
            calc
              _ = (fallingFactorial n orders.sum * fallingFactorial (n - orders.sum) order) *
                  (fallingFactorial stock order * jointFalling orders stocks) *
                    fallingFactorial ((stock :: stocks).sum - (order :: orders).sum) (n - (order :: orders).sum) := by ac_rfl
              _ = _ := by rw [← fallingFactorial_add, Nat.add_comm orders.sum order]; rfl
          · have zero := jointFalling_above_sum orders stocks (by omega)
            simp only [zero, jointFalling, Nat.zero_mul, Nat.mul_zero]

/-- All joint factorial moments in a form valid even when the population
falling factorial vanishes. -/
theorem multivariateHypergeometric_jointFactorialMoment_scaled (n : Nat) (stocks orders : List Nat)
    (positive : 0 < binom stocks.sum n) (dimension : orders.length = stocks.length) :
    QProb.Equiv (QProb.scale (fallingFactorial stocks.sum orders.sum)
      (jointFactorialMoment (multivariateHypergeometricDistro n stocks positive) orders))
      (QProb.ofNat (fallingFactorial n orders.sum * jointFalling orders stocks)) := by
  refine QProb.equiv_trans (QProb.scale_congr _
    (QProb.equiv_symm ((multicolourDepletingCount_sameLaw n stocks positive).jointFactorialMoment orders))) ?_
  change (fallingFactorial stocks.sum orders.sum *
      natIntegral (multicolourDepletingCountAtoms n stocks) (jointFalling orders)) * 1 =
    (fallingFactorial n orders.sum * jointFalling orders stocks) * fallingFactorial stocks.sum n
  rw [multicolourDepletingCount_joint_integral n stocks orders dimension, Nat.mul_one]
  by_cases within : orders.sum ≤ n
  · have split : fallingFactorial stocks.sum n = fallingFactorial stocks.sum orders.sum *
        fallingFactorial (stocks.sum - orders.sum) (n - orders.sum) := by
      simpa only [Nat.add_sub_of_le within] using fallingFactorial_add stocks.sum orders.sum (n - orders.sum)
    rw [split]
    ac_rfl
  · rw [fallingFactorial_eq_zero n orders.sum (by omega)]
    simp only [Nat.zero_mul, Nat.mul_zero]

/-- The familiar closed ratio whenever its population denominator is positive. -/
theorem multivariateHypergeometric_jointFactorialMoment (n : Nat) (stocks orders : List Nat)
    (positive : 0 < binom stocks.sum n) (dimension : orders.length = stocks.length) (within : orders.sum ≤ stocks.sum) :
    QProb.Equiv (jointFactorialMoment (multivariateHypergeometricDistro n stocks positive) orders)
      ⟨fallingFactorial n orders.sum * jointFalling orders stocks, fallingFactorial stocks.sum orders.sum,
        fallingFactorial_pos _ _ within⟩ := by
  have scaled := multivariateHypergeometric_jointFactorialMoment_scaled n stocks orders positive dimension
  simpa only [QProb.Equiv, QProb.scale, QProb.ofNat, Nat.mul_one, Nat.mul_comm] using scaled

end Thesis.Probability.Distros
