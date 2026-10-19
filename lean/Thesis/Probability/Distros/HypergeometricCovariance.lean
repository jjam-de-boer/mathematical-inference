import Thesis.Probability.Distros.OccupancyCovariance
import Thesis.Probability.Distros.DepletingSupport

namespace Thesis.Probability.Distros
open Combinatorics

/-- Rational covariance agrees with the original natural-observable API. -/
theorem Distro.rationalCovariance_ofNat (μ : Distro Ω) (f g : Ω → Nat) :
    SignedRatio.Equiv (μ.rationalCovariance (fun x => (QProb.ofNat (f x)).toSignedRatio)
      (fun x => (QProb.ofNat (g x)).toSignedRatio)) (μ.covariance f g).toRatio := by
  have result := μ.rationalCovariance_int (fun x => (f x : Int)) (fun x => (g x : Int))
  rw [μ.signedCovariance_nat f g] at result
  exact result

theorem multivariateHypergeometric_coordinate_mean (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (population : 0 < stocks.sum)
    (i : Nat) (within : i < stocks.length) :
    QProb.Equiv ((multivariateHypergeometricDistro n stocks positive).expectNat (fun counts => counts.getD i 0))
      ⟨n * stocks.getD i 0, stocks.sum, population⟩ := by
  have result := QProb.equiv_trans (multivariateHypergeometric_coordinate_hypergeometric n stocks positive i within).mean
    (hypergeometric_mean (stocks.getD i 0) stocks.sum n (list_getD_le_sum _ _) positive population)
  rw [mean_expectNat] at result
  exact result

/-- The distinct-coordinate second moment, extracted from mixed order two. -/
theorem multivariateHypergeometric_crossMoment (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (population : 1 < stocks.sum)
    (i j : Nat) (hi : i < stocks.length) (hj : j < stocks.length) (different : i ≠ j) :
    QProb.Equiv ((multivariateHypergeometricDistro n stocks positive).expectNat
      (fun counts => counts.getD i 0 * counts.getD j 0))
      ⟨n * (n - 1) * stocks.getD i 0 * stocks.getD j 0, stocks.sum * (stocks.sum - 1),
        Nat.mul_pos (by omega) (by omega)⟩ := by
  let orders := pairOrders stocks.length i j
  have orderSum : orders.sum = 2 := pairOrders_sum _ _ _ hi hj
  have joint := multivariateHypergeometric_jointFactorialMoment n stocks orders positive
    (pairOrders_length _ _ _) (by rw [orderSum]; omega)
  have factors : jointFalling orders stocks = stocks.getD i 0 * stocks.getD j 0 := by
    rw [jointFalling_product]
    exact coordinateProduct_pair _ (fun _ => rfl) fallingFactorial_order_one stocks i j hi hj different
  have obs := (multivariateHypergeometricDistro n stocks positive).expectNat_congr_on_support
    (fun counts => counts.getD i 0 * counts.getD j 0) (jointFalling orders) (by
      intro atom member
      have dimension := (multivariateHypergeometric_support n stocks atom member).1
      rw [jointFalling_product]
      have result := coordinateProduct_pair fallingFactorial (fun _ => rfl) fallingFactorial_order_one
        atom.1 i j (by omega) (by omega) different
      simpa only [dimension] using result.symm)
  rw [obs]
  simpa only [jointFactorialMoment, orderSum, factors, fallingFactorial, Nat.mul_one, Nat.mul_assoc] using joint

/-- Cov(Kᵢ,Kⱼ) = -n(S-n)sᵢsⱼ/(S²(S-1)) for distinct colours.
Zero samples, zero stocks and a full-population sample are included. -/
theorem multivariateHypergeometric_covariance (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (population : 1 < stocks.sum)
    (i j : Nat) (hi : i < stocks.length) (hj : j < stocks.length) (different : i ≠ j) :
    SignedMoment.Equiv ((multivariateHypergeometricDistro n stocks positive).covariance
      (fun counts => counts.getD i 0) (fun counts => counts.getD j 0))
      ⟨-((n * stocks.getD i 0 * stocks.getD j 0 * (stocks.sum - n) : Nat) : Int),
        stocks.sum * stocks.sum * (stocks.sum - 1),
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)⟩ := by
  let μ := multivariateHypergeometricDistro n stocks positive
  let D : Int := μ.record.den
  let S : Int := stocks.sum
  let A : Int := stocks.getD i 0
  let B : Int := stocks.getD j 0
  let F : Int := natIntegral μ.record.atoms (fun counts => counts.getD i 0)
  let G : Int := natIntegral μ.record.atoms (fun counts => counts.getD j 0)
  let H : Int := natIntegral μ.record.atoms (fun counts => counts.getD i 0 * counts.getD j 0)
  have fm := multivariateHypergeometric_coordinate_mean n stocks positive (by omega) i hi
  have gm := multivariateHypergeometric_coordinate_mean n stocks positive (by omega) j hj
  have hm := multivariateHypergeometric_crossMoment n stocks positive population i j hi hj different
  change _ * stocks.sum = n * stocks.getD i 0 * μ.record.den at fm
  change _ * stocks.sum = n * stocks.getD j 0 * μ.record.den at gm
  change _ * (stocks.sum * (stocks.sum - 1)) = n * (n - 1) * stocks.getD i 0 * stocks.getD j 0 * μ.record.den at hm
  have f : F * S = (n : Int) * A * D := by
    have cast := congrArg (fun x : Nat => (x : Int)) fm
    simpa only [Int.natCast_mul] using cast
  have g : G * S = (n : Int) * B * D := by
    have cast := congrArg (fun x : Nat => (x : Int)) gm
    simpa only [Int.natCast_mul] using cast
  have h : H * (S * ((stocks.sum - 1 : Nat) : Int)) = ((n * (n - 1) : Nat) : Int) * A * B * D := by
    have cast := congrArg (fun x : Nat => (x : Int)) hm
    simpa only [Int.natCast_mul] using cast
  change (D * H - F * G) * ((stocks.sum * stocks.sum * (stocks.sum - 1) : Nat) : Int) =
    -((n * stocks.getD i 0 * stocks.getD j 0 * (stocks.sum - n) : Nat) : Int) * ((μ.record.den * μ.record.den : Nat) : Int)
  simp only [Int.natCast_mul]
  change (D * H - F * G) * (S * S * ((stocks.sum - 1 : Nat) : Int)) =
    -((n : Int) * A * B * ((stocks.sum - n : Nat) : Int)) * (D * D)
  calc
    _ = D * S * (H * (S * ((stocks.sum - 1 : Nat) : Int))) -
        (F * S) * (G * S) * ((stocks.sum - 1 : Nat) : Int) := by
      rw [Int.sub_mul]
      congr 1 <;> ac_rfl
    _ = (((n * (n - 1) : Nat) : Int) * S - (n : Int) * n * ((stocks.sum - 1 : Nat) : Int)) * A * B * (D * D) := by
      rw [f, g, h]
      simp only [Int.sub_mul]
      congr 1 <;> ac_rfl
    _ = _ := by
      have balance := congrArg (fun x : Nat => (x : Int)) (nat_falling_square n)
      simp only [Int.natCast_add, Int.natCast_mul] at balance
      have count : ((n * (n - 1) : Nat) : Int) = (n : Int) * n - n := by omega
      have previous : ((stocks.sum - 1 : Nat) : Int) = S - 1 := by
        have cast := congrArg (fun x : Nat => (x : Int)) (Nat.sub_add_cancel (show 1 ≤ stocks.sum by omega))
        simp only [Int.natCast_add, Int.natCast_one] at cast
        omega
      have remaining : ((stocks.sum - n : Nat) : Int) = S - n := by
        have cast := congrArg (fun x : Nat => (x : Int))
          (Nat.sub_add_cancel (hypergeometric_draws_le_total stocks.sum n positive))
        simp only [Int.natCast_add] at cast
        omega
      have coefficient : ((n * (n - 1) : Nat) : Int) * S - (n : Int) * n * ((stocks.sum - 1 : Nat) : Int) =
          -((n : Int) * ((stocks.sum - n : Nat) : Int)) := by
        rw [count, previous, remaining]
        simp only [Int.sub_mul, Int.mul_sub, Int.mul_one]
        omega
      rw [coefficient]
      simp only [Int.neg_mul]
      congr 1
      ac_rfl

theorem multivariateHypergeometric_rationalCovariance (n : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum n) (population : 1 < stocks.sum)
    (i j : Nat) (hi : i < stocks.length) (hj : j < stocks.length) (different : i ≠ j) :
    SignedRatio.Equiv ((multivariateHypergeometricDistro n stocks positive).rationalCovariance (countResponse i) (countResponse j))
      ⟨-((n * stocks.getD i 0 * stocks.getD j 0 * (stocks.sum - n) : Nat) : Int),
        stocks.sum * stocks.sum * (stocks.sum - 1),
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)⟩ :=
  SignedRatio.equiv_trans (Distro.rationalCovariance_ofNat _ _ _)
    (SignedMoment.toRatio_congr (multivariateHypergeometric_covariance n stocks positive population i j hi hj different))

end Thesis.Probability.Distros
