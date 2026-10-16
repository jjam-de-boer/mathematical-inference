import Thesis.Probability.Distros.RationalConcentration
import Thesis.Probability.Distros.RationalMarkov

namespace Thesis.Probability.Distros

/-- The square of a signed rational is a nonnegative rational value. -/
def squaredRatio (value : SignedRatio) : QProb :=
  ⟨value.num.natAbs * value.num.natAbs, value.den * value.den, Nat.mul_pos value.den_pos value.den_pos⟩

theorem squaredRatio_spec (value : SignedRatio) :
    SignedRatio.Equiv (squaredRatio value).toSignedRatio (SignedRatio.mul value value) := by
  simp only [SignedRatio.Equiv, squaredRatio, QProb.toSignedRatio, SignedRatio.mul,
    Int.natCast_mul, Int.natAbs_mul_self]

theorem rationalAtomSum_toSignedRatio (atoms : List (Ω × Nat)) (f : Ω → QProb) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms (fun x => (f x).toSignedRatio))
      (rationalIntegral atoms f).toSignedRatio := by
  induction atoms with
  | nil => exact SignedRatio.equiv_refl _
  | cons atom atoms ih =>
      change SignedRatio.Equiv
        (SignedRatio.add (SignedRatio.scaleNat atom.2 (f atom.1).toSignedRatio)
          (FiniteProbRecord.rationalAtomSum atoms (fun x => (f x).toSignedRatio)))
        (QProb.add (QProb.scale atom.2 (f atom.1)) (rationalIntegral atoms f)).toSignedRatio
      rw [QProb.toSignedRatio_add]
      apply SignedRatio.add_congr _ ih
      simp only [SignedRatio.Equiv, SignedRatio.scaleNat, QProb.toSignedRatio,
        QProb.scale, Int.natCast_mul]

theorem Distro.rationalExpectation_toSignedRatio (μ : Distro Ω) (f : Ω → QProb) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => (f x).toSignedRatio))
      (μ.expectation f).toSignedRatio := by
  refine SignedRatio.equiv_trans
    (SignedRatio.divideNat_congr (rationalAtomSum_toSignedRatio μ.record.atoms f) μ.record.den μ.record.den_pos) ?_
  change SignedRatio.Equiv (SignedRatio.divideNat (rationalIntegral μ.record.atoms f).toSignedRatio μ.record.den μ.record.den_pos)
    (QProb.div (rationalIntegral μ.record.atoms f) (QProb.ofNat μ.record.den) μ.record.den_pos).toSignedRatio
  simp only [SignedRatio.Equiv, SignedRatio.divideNat, QProb.toSignedRatio,
    QProb.div, QProb.ofNat, Nat.mul_one, Int.natCast_mul]

private theorem ratio_square_sub_expand (x m : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.mul (SignedRatio.sub x m) (SignedRatio.sub x m))
      (SignedRatio.add (SignedRatio.sub (SignedRatio.sub (SignedRatio.mul x x) (SignedRatio.mul m x))
        (SignedRatio.mul m x)) (SignedRatio.mul m m)) := by
  simp only [SignedRatio.Equiv, SignedRatio.mul, SignedRatio.sub, SignedRatio.add, SignedRatio.neg,
    Int.natCast_mul, Int.mul_add, Int.add_mul, Int.neg_add, Int.neg_mul, Int.mul_neg,
    Int.neg_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

private theorem ratio_sub_sub_add (a b : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.add (SignedRatio.sub (SignedRatio.sub a b) b) b) (SignedRatio.sub a b) := by
  simp only [SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add, SignedRatio.neg,
    Int.natCast_mul, Int.mul_add, Int.add_mul, Int.neg_add, Int.neg_mul, Int.mul_neg,
    Int.neg_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- The rational variance is the expectation of the genuine centered square. -/
theorem Distro.rationalVariance_centered (μ : Distro Ω) (f : Ω → SignedRatio) :
    SignedRatio.Equiv
      (μ.rationalExpectation (fun x => SignedRatio.mul
        (SignedRatio.sub (f x) (μ.rationalExpectation f)) (SignedRatio.sub (f x) (μ.rationalExpectation f))))
      (μ.rationalVariance f) := by
  let m := μ.rationalExpectation f
  let square := fun x => SignedRatio.mul (f x) (f x)
  let cross := fun x => SignedRatio.mul m (f x)
  have crossMean := μ.rationalExpectation_mul_left m f
  have inner := SignedRatio.equiv_trans (μ.rationalExpectation_sub square cross)
    (ratio_sub_congr (SignedRatio.equiv_refl _) crossMean)
  have outer := SignedRatio.equiv_trans
    (μ.rationalExpectation_sub (fun x => SignedRatio.sub (square x) (cross x)) cross)
    (ratio_sub_congr inner crossMean)
  have expand := μ.rationalExpectation_congr _
    (fun x => SignedRatio.add (SignedRatio.sub (SignedRatio.sub (square x) (cross x)) (cross x)) (SignedRatio.mul m m))
    (fun x => ratio_square_sub_expand (f x) m)
  exact SignedRatio.equiv_trans expand (SignedRatio.equiv_trans
    (μ.rationalExpectation_add (fun x => SignedRatio.sub (SignedRatio.sub (square x) (cross x)) (cross x))
      (fun _ => SignedRatio.mul m m))
    (SignedRatio.equiv_trans (SignedRatio.add_congr outer (μ.rationalExpectation_constant (SignedRatio.mul m m)))
      (ratio_sub_sub_add _ _)))

/-- Nonnegative rational packaging of the existing signed-rational variance.
The specification below proves that the conversion never clips a negative value. -/
def Distro.varianceRational (μ : Distro Ω) (f : Ω → SignedRatio) : QProb :=
  ⟨(μ.rationalVariance f).num.toNat, (μ.rationalVariance f).den, (μ.rationalVariance f).den_pos⟩

theorem Distro.varianceRational_spec (μ : Distro Ω) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.varianceRational f).toSignedRatio (μ.rationalVariance f) := by
  change ((μ.rationalVariance f).num.toNat : Int) * ((μ.rationalVariance f).den : Int) =
    (μ.rationalVariance f).num * ((μ.rationalVariance f).den : Int)
  rw [Int.toNat_of_nonneg (μ.rationalVariance_nonnegative f)]

theorem Distro.squaredRatioDeviation_mean (μ : Distro Ω) (f : Ω → SignedRatio) :
    QProb.Equiv (μ.expectation (fun x => squaredRatio (SignedRatio.sub (f x) (μ.rationalExpectation f))))
      (μ.varianceRational f) := by
  have embedding := μ.rationalExpectation_toSignedRatio
    (fun x => squaredRatio (SignedRatio.sub (f x) (μ.rationalExpectation f)))
  have square := μ.rationalExpectation_congr _ _
    (fun x => squaredRatio_spec (SignedRatio.sub (f x) (μ.rationalExpectation f)))
  exact (QProb.toSignedRatio_equiv_iff _ _).mp (SignedRatio.equiv_trans (SignedRatio.equiv_symm embedding)
    (SignedRatio.equiv_trans square (SignedRatio.equiv_trans (μ.rationalVariance_centered f)
      (SignedRatio.equiv_symm (μ.varianceRational_spec f)))))

/-- The exact event |f-E[f]| ≥ radius, using only decidable natural comparisons. -/
def Distro.rationalDeviationEvent (μ : Distro Ω) (f : Ω → SignedRatio) (radius : QProb) : Event Ω :=
  fun x =>
    let delta := SignedRatio.sub (f x) (μ.rationalExpectation f)
    decide (radius.num * radius.num * (delta.den * delta.den) ≤
      (delta.num.natAbs * delta.num.natAbs) * (radius.den * radius.den))

theorem Distro.rationalDeviationEvent_value (μ : Distro Ω) (f : Ω → SignedRatio) (radius : QProb) (x : Ω) :
    μ.rationalDeviationEvent f radius x = decide (SignedRatio.LE (QProb.mul radius radius).toSignedRatio
      (SignedRatio.mul (SignedRatio.sub (f x) (μ.rationalExpectation f)) (SignedRatio.sub (f x) (μ.rationalExpectation f)))) := by
  apply decide_eq_decide.mpr
  exact (SignedRatio.toSignedRatio_le_iff (QProb.mul radius radius)
    (squaredRatio (SignedRatio.sub (f x) (μ.rationalExpectation f)))).symm.trans
      (SignedRatio.le_congr (SignedRatio.equiv_refl _)
        (squaredRatio_spec (SignedRatio.sub (f x) (μ.rationalExpectation f))))

/-- Chebyshev for all signed rational observables and all positive rational
radii, including zero variance and arbitrary fraction presentations. -/
theorem Distro.chebyshev_rationalObservable (μ : Distro Ω) (f : Ω → SignedRatio) (radius : QProb)
    (positive : 0 < radius.num) :
    QProb.LE (μ.record.probVal (μ.rationalDeviationEvent f radius))
      (QProb.div (μ.varianceRational f) (QProb.mul radius radius) (Nat.mul_pos positive positive)) := by
  have bound := μ.markov_rational
    (fun x => squaredRatio (SignedRatio.sub (f x) (μ.rationalExpectation f)))
    (QProb.mul radius radius) (Nat.mul_pos positive positive)
  exact QProb.le_congr (QProb.equiv_refl _)
    (QProb.div_congr (μ.squaredRatioDeviation_mean f) (QProb.equiv_refl _)
      (Nat.mul_pos positive positive) (Nat.mul_pos positive positive)) bound

end Thesis.Probability.Distros
