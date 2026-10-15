import Thesis.Probability.Distros.Degenerate

namespace Thesis.Probability.Distros
open Combinatorics

/-!
Exact moments for truncated and censored negative-binomial waiting times.
Each factorial integral is a single finite NB generating sum with shifted
shape and cap; orders above the cap are zero.  The censored law adds the
explicit terminal-tail contribution and includes zero success weight.
Means and second moments specialize orders one and two; variance retains
the witnessed subtraction supplied by the generic Cauchy theorem.
-/

/-- Adjacent negative-binomial coefficient absorption, without division. -/
theorem nbCoefficient_absorb (r k : Nat) :
    (k + 1) * binom (k + r) (k + 1) = r * binom (k + r) k := by
  apply Nat.add_left_cancel (n := (k + 1) * binom (k + r) k)
  calc
    _ = (k + 1) * (binom (k + r) k + binom (k + r) (k + 1)) := by rw [Nat.mul_add]
    _ = (k + r + 1) * binom (k + r) k := by rw [← binom_succ_succ, binom_succ_mul]
    _ = _ := by
      have index : k + r + 1 = k + 1 + r := by omega
      rw [index, Nat.add_mul]

def nbFactorialSum (r cap b d order : Nat) : Nat :=
  natSum (cap + 1) (fun k =>
    fallingFactorial k order * binom (k + r - 1) k * b ^ k * d ^ (cap - k))

theorem nbFactorialSum_step (r cap b d order : Nat) :
    nbFactorialSum r (cap + 1) b d (order + 1) =
      r * b * nbFactorialSum (r + 1) cap b d order := by
  unfold nbFactorialSum
  rw [natSum_head]
  have tail : natSum (cap + 1) (fun k =>
      fallingFactorial (k + 1) (order + 1) * binom (k + 1 + r - 1) (k + 1) *
        b ^ (k + 1) * d ^ (cap + 1 - (k + 1))) =
      r * b * natSum (cap + 1) (fun k =>
        fallingFactorial k order * binom (k + (r + 1) - 1) k * b ^ k * d ^ (cap - k)) := by
    rw [← natSum_mul_left]
    apply natSum_congr
    intro k _
    have first : k + 1 + r - 1 = k + r := by omega
    have second : k + (r + 1) - 1 = k + r := by omega
    rw [fallingFactorial_succ, first, second, Nat.succ_sub_succ, Nat.pow_succ]
    calc
      _ = fallingFactorial k order * ((k + 1) * binom (k + r) (k + 1)) *
          b * b ^ k * d ^ (cap - k) := by ac_rfl
      _ = _ := by rw [nbCoefficient_absorb]; ac_rfl
  rw [tail]
  simp only [fallingFactorial, Nat.zero_mul, Nat.zero_add]

/-- Every factorial integral reduces to one shifted finite NB generating
sum.  Orders beyond the cap vanish rather than underflowing the shift. -/
theorem nbFactorialSum_closed (r cap b d order : Nat) :
    nbFactorialSum r cap b d order =
      if order ≤ cap then risingFactorial r order * b ^ order *
        nbSumHomog (r + order) b d (cap - order) else 0 := by
  induction order generalizing r cap b d with
  | zero => simp only [nbFactorialSum, fallingFactorial, Nat.one_mul,
      Nat.zero_le, if_true, risingFactorial, Nat.pow_zero, Nat.mul_one,
      Nat.add_zero, Nat.sub_zero, nbSumHomog]
  | succ order ih =>
      cases cap with
      | zero =>
          have outside : ¬order + 1 ≤ 0 := by omega
          rw [if_neg outside]
          simp only [nbFactorialSum, natSum, fallingFactorial, Nat.zero_mul, Nat.zero_add]
      | succ cap =>
          rw [nbFactorialSum_step, ih]
          by_cases within : order ≤ cap
          · have within' : order + 1 ≤ cap + 1 := by omega
            rw [if_pos within, if_pos within', risingFactorial_head,
              Nat.pow_succ, Nat.succ_sub_succ]
            have index : r + 1 + order = r + (order + 1) := by omega
            rw [index]
            ac_rfl
          · have outside : ¬order + 1 ≤ cap + 1 := by omega
            rw [if_neg within, if_neg outside, Nat.mul_zero]

theorem negativeBinomialWeight_factorial_sum (r cap a b order : Nat) :
    natSum (cap + 1) (fun k =>
      finWeight (negativeBinomialWeight r cap a b) k * fallingFactorial k order) =
        a ^ r * nbFactorialSum r cap b (a + b) order := by
  unfold nbFactorialSum
  rw [← natSum_mul_left]
  apply natSum_congr
  intro k hk
  simp only [finWeight, dif_pos hk, negativeBinomialWeight]
  ac_rfl

def negativeBinomialFactorialClosed (r cap a b order : Nat) (positive : 0 < a) : QProb :=
  ⟨if order ≤ cap then risingFactorial r order * b ^ order *
      nbSumHomog (r + order) b (a + b) (cap - order) else 0,
    nbSumHomog r b (a + b) cap, nbSumHomog_pos _ _ _ _ (Nat.add_pos_left positive b)⟩

theorem negativeBinomial_factorialMoment (r cap a b order : Nat)
    (shape : 0 < r) (positive : 0 < a) :
    QProb.Equiv (factorialMoment (negativeBinomialNatDistro r cap a b shape positive) order)
      (negativeBinomialFactorialClosed r cap a b order positive) := by
  have hn : (factorialMoment (negativeBinomialNatDistro r cap a b shape positive) order).num =
      a ^ r * nbFactorialSum r cap b (a + b) order := by
    change natIntegral (finWeighted (cap + 1) (negativeBinomialWeight r cap a b))
      (fun k => fallingFactorial k.val order) = _
    rw [natIntegral_finWeighted (cap + 1) (negativeBinomialWeight r cap a b)
      (fun k => fallingFactorial k order), negativeBinomialWeight_factorial_sum]
  change (factorialMoment (negativeBinomialNatDistro r cap a b shape positive) order).num *
      nbSumHomog r b (a + b) cap =
    (negativeBinomialFactorialClosed r cap a b order positive).num *
      (negativeBinomialDistro r cap a b shape positive).record.den
  rw [hn, negativeBinomial_den, nbFactorialSum_closed]
  dsimp only [negativeBinomialFactorialClosed]
  ac_rfl

theorem negativeBinomialCensoredWeight_factorial_sum (r cap a b order : Nat) :
    natSum (cap + 1) (fun k =>
      finWeight (negativeBinomialCensoredWeight r cap a b) k * fallingFactorial k order) =
      a ^ r * nbFactorialSum r cap b (a + b) order +
        fallingFactorial cap order * negativeBinomialCensorTail r cap a b := by
  have raw : natSum (cap + 1) (fun k =>
        finWeight (negativeBinomialCensoredWeight r cap a b) k * fallingFactorial k order) =
      natSum (cap + 1) (fun k =>
        finWeight (negativeBinomialWeight r cap a b) k * fallingFactorial k order) +
        fallingFactorial cap order * negativeBinomialCensorTail r cap a b := by
    rw [natSum_succ, natSum_succ (n := cap)
      (fun k => finWeight (negativeBinomialWeight r cap a b) k * fallingFactorial k order)]
    have front : natSum cap (fun k =>
          finWeight (negativeBinomialCensoredWeight r cap a b) k * fallingFactorial k order) =
        natSum cap (fun k =>
          finWeight (negativeBinomialWeight r cap a b) k * fallingFactorial k order) := by
      apply natSum_congr
      intro k hk
      simp only [finWeight, dif_pos (Nat.lt_succ_of_lt hk), negativeBinomialCensoredWeight, if_pos hk]
    rw [front]
    simp only [finWeight, dif_pos (Nat.lt_succ_self cap),
      negativeBinomialCensoredWeight, Nat.lt_irrefl, if_false, Nat.add_mul]
    ac_rfl
  rw [raw, negativeBinomialWeight_factorial_sum]

def negativeBinomialCensoredFactorialClosed (r cap a b order : Nat)
    (positive : 0 < a + b) : QProb :=
  ⟨a ^ r * (if order ≤ cap then risingFactorial r order * b ^ order *
      nbSumHomog (r + order) b (a + b) (cap - order) else 0) +
        fallingFactorial cap order * negativeBinomialCensorTail r cap a b,
    (a + b) ^ (cap + r), Nat.pow_pos positive⟩

theorem negativeBinomialCensoredOfTotal_factorialMoment (r cap a b order : Nat)
    (shape : 0 < r) (positive : 0 < a + b) :
    QProb.Equiv
      (factorialMoment (negativeBinomialCensoredNatDistroOfTotal r cap a b shape positive) order)
      (negativeBinomialCensoredFactorialClosed r cap a b order positive) := by
  have hn : (factorialMoment (negativeBinomialCensoredNatDistroOfTotal r cap a b shape positive) order).num =
      a ^ r * nbFactorialSum r cap b (a + b) order +
        fallingFactorial cap order * negativeBinomialCensorTail r cap a b := by
    change natIntegral (finWeighted (cap + 1) (negativeBinomialCensoredWeight r cap a b))
      (fun k => fallingFactorial k.val order) = _
    rw [natIntegral_finWeighted (cap + 1) (negativeBinomialCensoredWeight r cap a b)
      (fun k => fallingFactorial k order), negativeBinomialCensoredWeight_factorial_sum]
  change (factorialMoment (negativeBinomialCensoredNatDistroOfTotal r cap a b shape positive) order).num *
      (a + b) ^ (cap + r) =
    (negativeBinomialCensoredFactorialClosed r cap a b order positive).num *
      (negativeBinomialCensoredDistroOfTotal r cap a b shape positive).record.den
  rw [hn, nbFactorialSum_closed, negativeBinomialCensoredOfTotal_den]
  rfl

theorem negativeBinomialCensored_factorialMoment (r cap a b order : Nat)
    (shape : 0 < r) (positive : 0 < a) :
    QProb.Equiv (factorialMoment (negativeBinomialCensoredNatDistro r cap a b shape positive) order)
      (negativeBinomialCensoredFactorialClosed r cap a b order (Nat.add_pos_left positive b)) :=
  negativeBinomialCensoredOfTotal_factorialMoment r cap a b order shape (Nat.add_pos_left positive b)

def negativeBinomialMeanClosed (r cap a b : Nat) (positive : 0 < a) : QProb :=
  negativeBinomialFactorialClosed r cap a b 1 positive

def negativeBinomialSecondMomentClosed (r cap a b : Nat) (positive : 0 < a) : QProb :=
  QProb.add (negativeBinomialFactorialClosed r cap a b 2 positive)
    (negativeBinomialMeanClosed r cap a b positive)

theorem negativeBinomial_mean (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a) :
    QProb.Equiv (mean (negativeBinomialNatDistro r cap a b shape positive))
      (negativeBinomialMeanClosed r cap a b positive) := by
  simpa only [factorialMoment_one] using negativeBinomial_factorialMoment r cap a b 1 shape positive

theorem negativeBinomial_secondMoment (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a) :
    QProb.Equiv (secondMoment (negativeBinomialNatDistro r cap a b shape positive))
      (negativeBinomialSecondMomentClosed r cap a b positive) :=
  QProb.equiv_trans (secondMoment_factorialMoment _)
    (QProb.add_congr (negativeBinomial_factorialMoment r cap a b 2 shape positive)
      (negativeBinomial_mean r cap a b shape positive))

def negativeBinomialVarianceClosed (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a) : QProb :=
  QProb.sub (negativeBinomialSecondMomentClosed r cap a b positive)
    (QProb.mul (negativeBinomialMeanClosed r cap a b positive) (negativeBinomialMeanClosed r cap a b positive))
    (closedMoments_cauchy (negativeBinomialNatDistro r cap a b shape positive) _ _
      (negativeBinomial_mean r cap a b shape positive) (negativeBinomial_secondMoment r cap a b shape positive))

theorem negativeBinomial_variance (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a) :
    QProb.Equiv (variance (negativeBinomialNatDistro r cap a b shape positive))
      (negativeBinomialVarianceClosed r cap a b shape positive) :=
  variance_closed_moments _ _ _ (negativeBinomial_mean r cap a b shape positive)
    (negativeBinomial_secondMoment r cap a b shape positive)

def negativeBinomialCensoredMeanClosed (r cap a b : Nat) (positive : 0 < a + b) : QProb :=
  negativeBinomialCensoredFactorialClosed r cap a b 1 positive

def negativeBinomialCensoredSecondMomentClosed (r cap a b : Nat) (positive : 0 < a + b) : QProb :=
  QProb.add (negativeBinomialCensoredFactorialClosed r cap a b 2 positive)
    (negativeBinomialCensoredMeanClosed r cap a b positive)

theorem negativeBinomialCensoredOfTotal_mean (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a + b) :
    QProb.Equiv (mean (negativeBinomialCensoredNatDistroOfTotal r cap a b shape positive))
      (negativeBinomialCensoredMeanClosed r cap a b positive) := by
  simpa only [factorialMoment_one] using
    negativeBinomialCensoredOfTotal_factorialMoment r cap a b 1 shape positive

theorem negativeBinomialCensoredOfTotal_secondMoment (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a + b) :
    QProb.Equiv (secondMoment (negativeBinomialCensoredNatDistroOfTotal r cap a b shape positive))
      (negativeBinomialCensoredSecondMomentClosed r cap a b positive) :=
  QProb.equiv_trans (secondMoment_factorialMoment _)
    (QProb.add_congr (negativeBinomialCensoredOfTotal_factorialMoment r cap a b 2 shape positive)
      (negativeBinomialCensoredOfTotal_mean r cap a b shape positive))

def negativeBinomialCensoredVarianceClosed (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a + b) : QProb :=
  QProb.sub (negativeBinomialCensoredSecondMomentClosed r cap a b positive)
    (QProb.mul (negativeBinomialCensoredMeanClosed r cap a b positive)
      (negativeBinomialCensoredMeanClosed r cap a b positive))
    (closedMoments_cauchy (negativeBinomialCensoredNatDistroOfTotal r cap a b shape positive) _ _
      (negativeBinomialCensoredOfTotal_mean r cap a b shape positive)
      (negativeBinomialCensoredOfTotal_secondMoment r cap a b shape positive))

theorem negativeBinomialCensoredOfTotal_variance (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a + b) :
    QProb.Equiv (variance (negativeBinomialCensoredNatDistroOfTotal r cap a b shape positive))
      (negativeBinomialCensoredVarianceClosed r cap a b shape positive) :=
  variance_closed_moments _ _ _ (negativeBinomialCensoredOfTotal_mean r cap a b shape positive)
    (negativeBinomialCensoredOfTotal_secondMoment r cap a b shape positive)

theorem negativeBinomialCensored_mean (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a) :
    QProb.Equiv (mean (negativeBinomialCensoredNatDistro r cap a b shape positive))
      (negativeBinomialCensoredMeanClosed r cap a b (Nat.add_pos_left positive b)) :=
  negativeBinomialCensoredOfTotal_mean r cap a b shape (Nat.add_pos_left positive b)

theorem negativeBinomialCensored_secondMoment (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a) :
    QProb.Equiv (secondMoment (negativeBinomialCensoredNatDistro r cap a b shape positive))
      (negativeBinomialCensoredSecondMomentClosed r cap a b (Nat.add_pos_left positive b)) :=
  negativeBinomialCensoredOfTotal_secondMoment r cap a b shape (Nat.add_pos_left positive b)

theorem negativeBinomialCensored_variance (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a) :
    QProb.Equiv (variance (negativeBinomialCensoredNatDistro r cap a b shape positive))
      (negativeBinomialCensoredVarianceClosed r cap a b shape (Nat.add_pos_left positive b)) :=
  negativeBinomialCensoredOfTotal_variance r cap a b shape (Nat.add_pos_left positive b)

end Thesis.Probability.Distros
