import Thesis.Probability.Distros.BinomialMoments
import Thesis.Probability.Distros.LawEquivalence
import Thesis.Probability.Distros.BetaBinomial
import Thesis.Probability.Distros.HypergeometricMoments

namespace Thesis.Probability.Distros
open Combinatorics

/-!
All-order falling-factorial moments.  Binomial and beta-binomial formulas
include orders above the trial count.  Hypergeometric moments have an
all-order cleared identity, a ratio when its falling denominator is
positive, and a zero result above the population size.
-/

/-- Falling factorial, including zero above its natural argument. -/
def fallingFactorial (n : Nat) : Nat → Nat
  | 0 => 1
  | r + 1 => n * fallingFactorial (n - 1) r

theorem fallingFactorial_succ (n r : Nat) :
    fallingFactorial (n + 1) (r + 1) = (n + 1) * fallingFactorial n r := by
  simp only [fallingFactorial, Nat.add_sub_cancel]

theorem fallingFactorial_eq_zero (n r : Nat) (above : n < r) : fallingFactorial n r = 0 := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
      cases n with
      | zero => exact Nat.zero_mul _
      | succ n => rw [fallingFactorial_succ, ih n (by omega), Nat.mul_zero]

theorem fallingFactorial_pos (n r : Nat) (within : r ≤ n) : 0 < fallingFactorial n r := by
  induction r generalizing n with
  | zero => exact Nat.zero_lt_one
  | succ r ih =>
      cases n with
      | zero => omega
      | succ n => rw [fallingFactorial_succ]; exact Nat.mul_pos (Nat.succ_pos _) (ih n (by omega))

def factorialMoment (μ : NatDistro Ω) (order : Nat) : QProb :=
  μ.distro.expectNat (fun x => fallingFactorial (μ.embed x) order)

theorem NatDistro.SameLaw.factorialMoment {μ : NatDistro Ω} {ν : NatDistro X}
    (h : μ.SameLaw ν) (order : Nat) :
    QProb.Equiv (factorialMoment μ order) (factorialMoment ν order) := by
  simpa only [factorialMoment, Distro.expectNat_map] using
    Distro.SameLaw.expectNat h (fun n => fallingFactorial n order)

theorem factorialMoment_zero (μ : NatDistro Ω) :
    QProb.Equiv (factorialMoment μ 0) QProb.one :=
  μ.distro.expectNat_constant 1

theorem factorialMoment_one (μ : NatDistro Ω) : factorialMoment μ 1 = mean μ := by
  simp only [factorialMoment, fallingFactorial, Nat.mul_one, mean_expectNat]

theorem binomTerm_factorial_moment (order n a b : Nat) :
    natSum (n + 1) (fun k => fallingFactorial k order * binomTerm n a b k) =
      fallingFactorial n order * a ^ order * (a + b) ^ (n - order) := by
  induction order generalizing n a b with
  | zero =>
      simp only [fallingFactorial, Nat.one_mul, Nat.pow_zero, Nat.sub_zero, Nat.mul_one]
      exact binomial_theorem n a b
  | succ order ih =>
      cases n with
      | zero => simp only [natSum, fallingFactorial, Nat.zero_mul, Nat.zero_add]
      | succ n =>
          rw [natSum_head]
          have tail : natSum (n + 1) (fun k =>
              fallingFactorial (k + 1) (order + 1) * binomTerm (n + 1) a b (k + 1)) =
              (n + 1) * a * natSum (n + 1) (fun k => fallingFactorial k order * binomTerm n a b k) := by
            rw [← natSum_mul_left]
            apply natSum_congr
            intro k _
            rw [fallingFactorial_succ]
            calc
              _ = fallingFactorial k order * ((k + 1) * binomTerm (n + 1) a b (k + 1)) := by ac_rfl
              _ = _ := by rw [binomTerm_succ_mul]; ac_rfl
          rw [tail, ih]
          simp only [fallingFactorial, Nat.zero_mul, Nat.zero_add,
            Nat.succ_sub_succ, Nat.pow_succ]
          ac_rfl

theorem risingFactorial_add (a m n : Nat) :
    risingFactorial a (m + n) = risingFactorial a m * risingFactorial (a + m) n := by
  induction n with
  | zero => simp only [Nat.add_zero, risingFactorial, Nat.mul_one]
  | succ n ih =>
      rw [Nat.add_succ, risingFactorial_succ, ih, risingFactorial_succ]
      simp only [Nat.add_assoc]
      ac_rfl

theorem betaBinomialTerm_factorial_moment (order n a b : Nat) :
    natSum (n + 1) (fun k => fallingFactorial k order * betaBinomialTerm n a b k) =
      fallingFactorial n order * risingFactorial a order *
        risingFactorial (a + b + order) (n - order) := by
  induction order generalizing n a b with
  | zero =>
      simp only [fallingFactorial, risingFactorial, Nat.one_mul, Nat.sub_zero,
        Nat.mul_one, Nat.add_zero]
      exact risingFactorial_vandermonde n a b
  | succ order ih =>
      cases n with
      | zero => simp only [natSum, fallingFactorial, Nat.zero_mul, Nat.zero_add]
      | succ n =>
          rw [natSum_head]
          have tail : natSum (n + 1) (fun k =>
              fallingFactorial (k + 1) (order + 1) * betaBinomialTerm (n + 1) a b (k + 1)) =
              (n + 1) * a * natSum (n + 1) (fun k => fallingFactorial k order * betaBinomialTerm n (a + 1) b k) := by
            rw [← natSum_mul_left]
            apply natSum_congr
            intro k _
            rw [fallingFactorial_succ]
            calc
              _ = fallingFactorial k order * ((k + 1) * betaBinomialTerm (n + 1) a b (k + 1)) := by ac_rfl
              _ = _ := by rw [betaBinomialTerm_succ_mul]; ac_rfl
          rw [tail, ih, fallingFactorial_succ, risingFactorial_head]
          simp only [fallingFactorial, Nat.zero_mul, Nat.zero_add, Nat.succ_sub_succ]
          have index : a + 1 + b + order = a + b + (order + 1) := by omega
          rw [index]
          ac_rfl

theorem binomial_factorialMoment (n a b order : Nat) (positive : 0 < b + a) :
    QProb.Equiv (factorialMoment (binomialNatDistro n a b positive) order)
      ⟨fallingFactorial n order * a ^ order, (b + a) ^ order, Nat.pow_pos positive⟩ := by
  have hn : (factorialMoment (binomialNatDistro n a b positive) order).num =
      natSum (n + 1) (fun k => fallingFactorial k order * binomTerm n a b k) := by
    change natIntegral (finWeighted (n + 1) (binomialWeight n a b))
      (fun k => fallingFactorial k.val order) = _
    rw [natIntegral_finWeighted (n + 1) (binomialWeight n a b) (fun k => fallingFactorial k order)]
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, binomialWeight]
    ac_rfl
  change (factorialMoment (binomialNatDistro n a b positive) order).num * (b + a) ^ order =
    (fallingFactorial n order * a ^ order) * (binomialDistro n a b positive).record.den
  rw [hn, binomTerm_factorial_moment, binomialDistro_den]
  rw [Nat.add_comm a b]
  by_cases within : order ≤ n
  · calc
      _ = (fallingFactorial n order * a ^ order) * ((b + a) ^ (n - order) * (b + a) ^ order) := by ac_rfl
      _ = _ := by rw [← Nat.pow_add, Nat.sub_add_cancel within]
  · rw [fallingFactorial_eq_zero n order (by omega)]
    simp only [Nat.zero_mul]

theorem betaBinomial_factorialMoment (n a b order : Nat) (ha : 0 < a) (hb : 0 < b) :
    QProb.Equiv (factorialMoment (betaBinomialNatDistro n a b ha hb) order)
      ⟨fallingFactorial n order * risingFactorial a order, risingFactorial (a + b) order,
        risingFactorial_pos _ _ (Nat.add_pos_left ha b)⟩ := by
  have hn : (factorialMoment (betaBinomialNatDistro n a b ha hb) order).num =
      natSum (n + 1) (fun k => fallingFactorial k order * betaBinomialTerm n a b k) := by
    change natIntegral (finWeighted (n + 1) (betaBinomialWeight n a b))
      (fun k => fallingFactorial k.val order) = _
    rw [natIntegral_finWeighted (n + 1) (betaBinomialWeight n a b) (fun k => fallingFactorial k order)]
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, betaBinomialWeight, betaBinomialTerm]
    ac_rfl
  change (factorialMoment (betaBinomialNatDistro n a b ha hb) order).num * risingFactorial (a + b) order =
    (fallingFactorial n order * risingFactorial a order) * (betaBinomialDistro n a b ha hb).record.den
  rw [hn, betaBinomialTerm_factorial_moment, betaBinomial_den]
  by_cases within : order ≤ n
  · have product : risingFactorial (a + b) n =
        risingFactorial (a + b) order * risingFactorial (a + b + order) (n - order) := by
      simpa only [Nat.add_sub_of_le within] using risingFactorial_add (a + b) order (n - order)
    rw [product]
    ac_rfl
  · rw [fallingFactorial_eq_zero n order (by omega)]
    simp only [Nat.zero_mul]

theorem hyperIntegral_factorial (order marked unmarked draws : Nat) (within : order ≤ draws) :
    hyperIntegral marked unmarked draws (fun k => fallingFactorial k order) =
      fallingFactorial marked order * binom (marked - order + unmarked) (draws - order) := by
  induction order generalizing marked unmarked draws with
  | zero =>
      simp only [hyperIntegral, fallingFactorial, Nat.one_mul, Nat.sub_zero]
      exact vandermonde marked unmarked draws
  | succ order ih =>
      cases marked with
      | zero =>
          rw [hyperIntegral_zero_marked unmarked draws (fun k => fallingFactorial k (order + 1))
            (by exact Nat.zero_mul _)]
          simp only [fallingFactorial, Nat.zero_mul]
      | succ marked =>
          cases draws with
          | zero => omega
          | succ draws =>
              unfold hyperIntegral
              rw [natSum_head]
              have tail : natSum (draws + 1) (fun k =>
                  fallingFactorial (k + 1) (order + 1) * binom (marked + 1) (k + 1) *
                    binom unmarked (draws + 1 - (k + 1))) =
                  (marked + 1) * hyperIntegral marked unmarked draws (fun k => fallingFactorial k order) := by
                unfold hyperIntegral
                rw [← natSum_mul_left]
                apply natSum_congr
                intro k _
                dsimp only
                rw [fallingFactorial_succ, Nat.succ_sub_succ]
                calc
                  _ = fallingFactorial k order * ((k + 1) * binom (marked + 1) (k + 1)) *
                      binom unmarked (draws - k) := by ac_rfl
                  _ = _ := by rw [binom_succ_mul]; ac_rfl
              rw [tail, ih marked unmarked draws (by omega), fallingFactorial_succ]
              simp only [fallingFactorial, Nat.zero_mul, Nat.zero_add, Nat.succ_sub_succ]
              ac_rfl

theorem hyperIntegral_factorial_above (order marked unmarked draws : Nat) (above : draws < order) :
    hyperIntegral marked unmarked draws (fun k => fallingFactorial k order) = 0 := by
  unfold hyperIntegral
  calc
    _ = natSum (draws + 1) (fun _ => 0) := by
      apply natSum_congr
      intro k hk
      dsimp only
      rw [fallingFactorial_eq_zero k order (by omega)]
      simp only [Nat.zero_mul]
    _ = 0 := natSum_zero_fun _

theorem binom_falling_absorb (total draws order : Nat) (within : order ≤ draws) :
    fallingFactorial draws order * binom total draws =
      fallingFactorial total order * binom (total - order) (draws - order) := by
  induction order generalizing total draws with
  | zero => simp only [fallingFactorial, Nat.one_mul, Nat.sub_zero]
  | succ order ih =>
      cases draws with
      | zero => omega
      | succ draws =>
          cases total with
          | zero =>
              rw [binom_eq_zero_of_lt (Nat.succ_pos draws)]
              simp only [fallingFactorial, Nat.mul_zero, Nat.zero_mul]
          | succ total =>
              rw [fallingFactorial_succ, fallingFactorial_succ, Nat.succ_sub_succ,
                Nat.succ_sub_succ]
              calc
                _ = fallingFactorial draws order * ((draws + 1) * binom (total + 1) (draws + 1)) := by ac_rfl
                _ = (total + 1) * (fallingFactorial draws order * binom total draws) := by
                  rw [binom_succ_mul]
                  ac_rfl
                _ = _ := by rw [ih total draws (by omega)]; ac_rfl

theorem hypergeometric_factorialMoment_num (marked total draws order : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) :
    (factorialMoment (hypergeometricNatDistro marked total draws hmarked positive) order).num =
      hyperIntegral marked (total - marked) draws (fun k => fallingFactorial k order) := by
  change natIntegral (finWeighted (draws + 1) (hypergeometricWeight marked total draws))
    (fun k => fallingFactorial k.val order) = _
  rw [natIntegral_finWeighted (draws + 1) (hypergeometricWeight marked total draws)
    (fun k => fallingFactorial k order)]
  unfold hyperIntegral
  apply natSum_congr
  intro k hk
  simp only [finWeight, dif_pos hk, hypergeometricWeight]
  ac_rfl

/-- The all-order hypergeometric factorial-moment identity avoids dividing
by a falling factorial that can vanish. -/
theorem hypergeometric_factorialMoment_scaled (marked total draws order : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) :
    QProb.Equiv
      (QProb.scale (fallingFactorial total order)
        (factorialMoment (hypergeometricNatDistro marked total draws hmarked positive) order))
      (QProb.ofNat (fallingFactorial draws order * fallingFactorial marked order)) := by
  change (fallingFactorial total order *
      (factorialMoment (hypergeometricNatDistro marked total draws hmarked positive) order).num) * 1 =
    (fallingFactorial draws order * fallingFactorial marked order) *
      (hypergeometricDistro marked total draws hmarked positive).record.den
  rw [hypergeometric_factorialMoment_num, hypergeometric_den, Nat.mul_one]
  by_cases within : order ≤ draws
  · rw [hyperIntegral_factorial order marked (total - marked) draws within]
    by_cases enough : order ≤ marked
    · have index : marked - order + (total - marked) = total - order := by omega
      rw [index]
      calc
        _ = fallingFactorial marked order *
            (fallingFactorial total order * binom (total - order) (draws - order)) := by ac_rfl
        _ = _ := by rw [← binom_falling_absorb total draws order within]; ac_rfl
    · rw [fallingFactorial_eq_zero marked order (by omega)]
      simp only [Nat.zero_mul, Nat.mul_zero]
  · rw [hyperIntegral_factorial_above order marked (total - marked) draws (by omega),
      fallingFactorial_eq_zero draws order (by omega)]
    simp only [Nat.zero_mul, Nat.mul_zero]

theorem hypergeometric_factorialMoment_ratio (marked total draws order : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) (within : order ≤ total) :
    QProb.Equiv (factorialMoment (hypergeometricNatDistro marked total draws hmarked positive) order)
      ⟨fallingFactorial draws order * fallingFactorial marked order, fallingFactorial total order,
        fallingFactorial_pos total order within⟩ := by
  have h := hypergeometric_factorialMoment_scaled marked total draws order hmarked positive
  simpa only [QProb.Equiv, QProb.scale, QProb.ofNat, Nat.mul_one, Nat.one_mul, Nat.mul_comm] using h

theorem hypergeometric_factorialMoment_above (marked total draws order : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) (above : total < order) :
    QProb.Equiv (factorialMoment (hypergeometricNatDistro marked total draws hmarked positive) order)
      QProb.zero := by
  have aboveDraws : draws < order := Nat.lt_of_le_of_lt
    (hypergeometric_draws_le_total total draws positive) above
  change (factorialMoment (hypergeometricNatDistro marked total draws hmarked positive) order).num * 1 =
    0 * (hypergeometricDistro marked total draws hmarked positive).record.den
  rw [hypergeometric_factorialMoment_num,
    hyperIntegral_factorial_above order marked (total - marked) draws aboveDraws]
  simp only [Nat.zero_mul]

end Thesis.Probability.Distros
