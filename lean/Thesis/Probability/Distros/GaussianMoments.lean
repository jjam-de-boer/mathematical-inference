import Thesis.Probability.Distros.Concentration
import Thesis.Probability.Distros.ChiSquared
import Thesis.Probability.FiniteSignedMass

namespace Thesis.Probability.Distros

open Combinatorics

/-!
Exact finite-coordinate moments.  The signed coordinate is `k - radius`;
its odd first moment vanishes, and the even moments are finite kernel sums.
-/

/-- `E[(k - radius)^(2*power)]`, computed without signed rationals. -/
def gaussianEvenMoment (radius : Nat) (q : QProb) (bounded : QProb.LE q QProb.one)
    (power : Nat) : QProb :=
  (discreteGaussianDistro radius q bounded).expectNat
    (fun k => natSqDiff k.val radius ^ power)

/-- The natural squared-distance observable is the square of the actual
signed centred coordinate. -/
theorem natSqDiff_signed_square (k radius : Nat) :
    ((k : Int) - (radius : Int)) * ((k : Int) - (radius : Int)) =
      (natSqDiff k radius : Int) := by
  by_cases h : k ≤ radius
  · have hd : (k : Int) - (radius : Int) = -((radius - k : Nat) : Int) := by omega
    simp [natSqDiff, h, hd, Int.natCast_mul, Int.neg_mul_neg]
  · have hd : (k : Int) - (radius : Int) = ((k - radius : Nat) : Int) := by omega
    simp [natSqDiff, h, hd, Int.natCast_mul]

theorem gaussianEvenMoment_finite_sum (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) (power : Nat) :
    gaussianEvenMoment radius q bounded power =
      ⟨natSum (2 * radius + 1) (fun k =>
          finWeight (discreteGaussianWeight radius q) k * natSqDiff k radius ^ power),
        (discreteGaussianDistro radius q bounded).record.den,
        (discreteGaussianDistro radius q bounded).record.den_pos⟩ := by
  simp only [gaussianEvenMoment, Distro.expectNat, discreteGaussianDistro,
    ofFinWeights]
  rw [natIntegral_finWeighted (2 * radius + 1) (discreteGaussianWeight radius q)
    (fun k => natSqDiff k radius ^ power)]

theorem gaussianSquare_rawMoment (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) (power : Nat) :
    rawMoment (naturalDistro (gaussianSquareRecord radius q bounded)) power =
      gaussianEvenMoment radius q bounded power := by
  simp only [rawMoment_expectNat, naturalDistro, gaussianSquareRecord, gaussianEvenMoment,
    Distro.expectNat, FiniteProbRecord.map, id]
  rw [natIntegral_map (discreteGaussianDistro radius q bounded).record.atoms
    (fun k => natSqDiff k.val radius) (fun value => value ^ power)]

theorem gaussianSquare_mean (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    mean (naturalDistro (gaussianSquareRecord radius q bounded)) =
      gaussianEvenMoment radius q bounded 1 := gaussianSquare_rawMoment radius q bounded 1

theorem gaussianSquare_secondMoment (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    secondMoment (naturalDistro (gaussianSquareRecord radius q bounded)) =
      gaussianEvenMoment radius q bounded 2 := gaussianSquare_rawMoment radius q bounded 2

theorem gaussianEvenMoment_cauchy (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.LE (QProb.mul (gaussianEvenMoment radius q bounded 1)
      (gaussianEvenMoment radius q bounded 1)) (gaussianEvenMoment radius q bounded 2) := by
  let μ := naturalDistro (gaussianSquareRecord radius q bounded)
  have h := QProb.le_congr (meanSq_equiv_mul μ)
    (secondMomentScaled_equiv μ) (meanSq_le_secondMoment μ)
  simpa only [μ, gaussianSquare_mean, gaussianSquare_secondMoment] using h

/-- Variance of one squared coordinate: its fourth centred moment minus
the square of its second centred moment. -/
def gaussianSquareVariance (radius : Nat) (q : QProb) (bounded : QProb.LE q QProb.one) :
    QProb :=
  QProb.sub (gaussianEvenMoment radius q bounded 2)
    (QProb.mul (gaussianEvenMoment radius q bounded 1) (gaussianEvenMoment radius q bounded 1))
    (gaussianEvenMoment_cauchy radius q bounded)

theorem gaussianSquare_variance (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.Equiv (variance (naturalDistro (gaussianSquareRecord radius q bounded)))
      (gaussianSquareVariance radius q bounded) := by
  let μ := naturalDistro (gaussianSquareRecord radius q bounded)
  have h := QProb.le_congr (meanSq_equiv_mul μ)
    (secondMomentScaled_equiv μ) (meanSq_le_secondMoment μ)
  have hs := QProb.sub_congr (secondMomentScaled_equiv μ) (meanSq_equiv_mul μ)
    (meanSq_le_secondMoment μ) h
  simpa only [μ, gaussianSquare_mean, gaussianSquare_secondMoment, gaussianSquareVariance]
    using hs

theorem chiSquared_mean_finite (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.Equiv (mean (chiSquaredDistro df radius q bounded))
      (QProb.scale df (gaussianEvenMoment radius q bounded 1)) := by
  refine QProb.equiv_trans (chiSquared_mean df radius q bounded) ?_
  apply QProb.scale_congr
  rw [mean, gaussianSquare_rawMoment]
  exact QProb.equiv_refl _

theorem chiSquared_variance_finite (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.Equiv (variance (chiSquaredDistro df radius q bounded))
      (QProb.scale df (gaussianSquareVariance radius q bounded)) :=
  QProb.equiv_trans (chiSquared_variance df radius q bounded)
    (QProb.scale_congr df (gaussianSquare_variance radius q bounded))

theorem signedAtomMass_natIntegral (atoms : List (Ω × Nat)) (f : Ω → Nat) :
    FiniteProbRecord.signedAtomMass atoms (fun value => (f value : Int)) =
      (natIntegral atoms f : Int) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [FiniteProbRecord.signedAtomMass, List.map_cons, List.sum_cons,
        natIntegral, Int.natCast_add, Int.natCast_mul] at ih ⊢
      rw [ih]

/-- The signed centred Gaussian coordinate has exactly zero mean. -/
theorem discreteGaussian_signed_mean_zero (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    (discreteGaussianDistro radius q bounded).record.signedMass
      (fun k => (k.val : Int) - (radius : Int)) = 0 := by
  let μ := discreteGaussianNatDistro radius q bounded
  have hm := discreteGaussian_mean radius q bounded
  rw [mean_expectNat] at hm
  change natIntegral μ.distro.record.atoms μ.embed * 1 = radius * μ.distro.record.den at hm
  rw [Nat.mul_one] at hm
  have sum := FiniteProbRecord.signedAtomMass_add μ.distro.record.atoms
    (fun k => (k.val : Int) - (radius : Int)) (fun _ => (radius : Int))
  have point : (fun k : Fin (2 * radius + 1) =>
      ((k.val : Int) - (radius : Int)) + (radius : Int)) =
      (fun k => (k.val : Int)) := by funext k; omega
  rw [point, signedAtomMass_natIntegral, FiniteProbRecord.signedAtomMass_const,
    μ.distro.record.total_mass] at sum
  change natIntegral μ.distro.record.atoms Fin.val = _ at hm
  rw [hm] at sum
  simp only [Int.natCast_mul] at sum
  have hcomm : (radius : Int) * (μ.distro.record.den : Int) =
      (μ.distro.record.den : Int) * (radius : Int) := Int.mul_comm _ _
  rw [hcomm] at sum
  change FiniteProbRecord.signedAtomMass μ.distro.record.atoms
    (fun k => (k.val : Int) - (radius : Int)) = 0
  omega

theorem discreteGaussian_secondMoment_centered (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.Equiv (secondMoment (discreteGaussianNatDistro radius q bounded))
      (QProb.add (gaussianEvenMoment radius q bounded 1) (QProb.ofNat (radius * radius))) := by
  let μ := discreteGaussianNatDistro radius q bounded
  have hm := discreteGaussian_mean radius q bounded
  rw [mean_expectNat] at hm
  change natIntegral μ.distro.record.atoms Fin.val * 1 = radius * μ.distro.record.den at hm
  rw [Nat.mul_one] at hm
  have hi := natIntegral_congr μ.distro.record.atoms
    (fun k => k.val * k.val + radius * radius)
    (fun k => natSqDiff k.val radius + k.val * (2 * radius))
    (fun k => by
      change k.val * k.val + radius * radius = natSqDiff k.val radius + k.val * (2 * radius)
      rw [natSqDiff_balance]
      ac_rfl)
  rw [natIntegral_add, natIntegral_add, natIntegral_constant,
    natIntegral_mul, μ.distro.record.total_mass, hm] at hi
  have hdouble : radius * μ.distro.record.den * (2 * radius) =
      μ.distro.record.den * (radius * radius) + μ.distro.record.den * (radius * radius) := by
    have double (d r : Nat) : r * d * (2 * r) = d * (r * r) + d * (r * r) := by
      have twice : 2 * r = r + r := by omega
      rw [twice, Nat.mul_add]
      ac_rfl
    exact double _ _
  rw [hdouble] at hi
  have hnum : natIntegral μ.distro.record.atoms (fun k => k.val * k.val) =
      natIntegral μ.distro.record.atoms (fun k => natSqDiff k.val radius) +
        μ.distro.record.den * (radius * radius) := by omega
  simp only [secondMoment, rawMoment_expectNat, gaussianEvenMoment,
    Distro.expectNat, Nat.pow_succ, Nat.pow_zero, Nat.mul_one,
    QProb.Equiv, QProb.add, QProb.ofNat, Nat.one_mul]
  change natIntegral μ.distro.record.atoms (fun k => k.val * k.val) * μ.distro.record.den = _
  rw [hnum]
  ac_rfl

/-- The shifted natural coordinate and the signed centred coordinate have
the same variance: the exact finite second centred moment. -/
theorem discreteGaussian_variance (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.Equiv (variance (discreteGaussianNatDistro radius q bounded))
      (gaussianEvenMoment radius q bounded 1) := by
  let μ := discreteGaussianNatDistro radius q bounded
  have hmeanSquare : QProb.Equiv (QProb.mul (mean μ) (mean μ))
      (QProb.ofNat (radius * radius)) := by
    refine QProb.equiv_trans (QProb.mul_congr (discreteGaussian_mean radius q bounded)
      (discreteGaussian_mean radius q bounded)) ?_
    exact QProb.equiv_refl _
  apply qprob_add_cancel_right _ _ (QProb.ofNat (radius * radius))
  exact QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) (QProb.equiv_symm hmeanSquare))
    (QProb.equiv_trans (variance_balance μ) (discreteGaussian_secondMoment_centered radius q bounded))

theorem gaussianEvenMoment_zero (radius power : Nat) (positive : 0 < power) :
    QProb.Equiv (gaussianEvenMoment radius QProb.zero (QProb.zero_le _) power) QProb.zero := by
  rw [gaussianEvenMoment_finite_sum]
  have hnum : natSum (2 * radius + 1) (fun k =>
      finWeight (discreteGaussianWeight radius QProb.zero) k * natSqDiff k radius ^ power) = 0 := by
    rw [← natSum_zero_fun (2 * radius + 1)]
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, discreteGaussianWeight_zero]
    by_cases h : k = radius
    · simp only [h, natSqDiff_self, Nat.zero_pow positive, Nat.mul_zero]
    · simp only [if_neg h, Nat.zero_mul]
  simp only [QProb.Equiv]
  rw [hnum]
  simp only [QProb.zero, Nat.zero_mul]

theorem gaussianEvenMoment_radius_zero (q : QProb) (bounded : QProb.LE q QProb.one)
    (power : Nat) (positive : 0 < power) :
    QProb.Equiv (gaussianEvenMoment 0 q bounded power) QProb.zero := by
  rw [gaussianEvenMoment_finite_sum]
  simp only [Nat.mul_zero, natSum, natSqDiff_self,
    Nat.zero_pow positive, Nat.add_zero, QProb.Equiv, QProb.zero, Nat.zero_mul]

theorem discreteGaussian_zero_variance (radius : Nat) :
    QProb.Equiv (variance (discreteGaussianNatDistro radius QProb.zero (QProb.zero_le _)))
      QProb.zero :=
  QProb.equiv_trans (discreteGaussian_variance radius QProb.zero _)
    (gaussianEvenMoment_zero radius 1 (by decide))

theorem discreteGaussian_radius_zero_variance (q : QProb) (bounded : QProb.LE q QProb.one) :
    QProb.Equiv (variance (discreteGaussianNatDistro 0 q bounded)) QProb.zero :=
  QProb.equiv_trans (discreteGaussian_variance 0 q bounded)
    (gaussianEvenMoment_radius_zero q bounded 1 (by decide))

end Thesis.Probability.Distros
