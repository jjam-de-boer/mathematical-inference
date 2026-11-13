import Thesis.Probability.Distros.SignedConcentration

namespace Thesis.Probability.Distros

/-- Scaling and adding integer observables gives the usual covariance
quadratic form on the record's common squared denominator. -/
theorem Distro.signedCovariance_linear_self_num (μ : Distro Ω) (f g : Ω → Int) (a b : Int) :
    (μ.signedCovariance (fun x => a * f x + b * g x) (fun x => a * f x + b * g x)).num =
      a * a * (μ.signedCovariance f f).num + b * b * (μ.signedCovariance g g).num +
        2 * a * b * (μ.signedCovariance f g).num := by
  have expansion := μ.signedCovariance_sum_self_num (fun x => a * f x) (fun x => b * g x)
  simp only [signedCovariance_scale_left, signedCovariance_scale_right, SignedMoment.scale] at expansion
  rw [expansion]
  ac_rfl

theorem Distro.signedCovariance_zero_of_varianceInt_zero (μ : Distro Ω) (f g : Ω → Int)
    (zero : (μ.varianceInt f).num = 0) : (μ.signedCovariance f g).num = 0 := by
  rcases (μ.varianceInt_zero_iff_constant f).mp zero with ⟨c, constant⟩
  have mean : μ.record.signedMass f = (μ.record.den : Int) * c := by
    change FiniteProbRecord.signedAtomMass μ.record.atoms f = _
    rw [signedAtomMass_congr_positive _ f (fun _ => c) constant,
      FiniteProbRecord.signedAtomMass_const, μ.record.total_mass]
  have product : μ.record.signedMass (fun x => f x * g x) = c * μ.record.signedMass g := by
    change FiniteProbRecord.signedAtomMass μ.record.atoms _ = _
    rw [signedAtomMass_congr_positive _ (fun x => f x * g x) (fun x => c * g x)
      (fun atom member weight => by
        change f atom.1 * g atom.1 = c * g atom.1
        rw [constant atom member weight]), FiniteProbRecord.signedAtomMass_mul_left]
    rfl
  change (μ.record.den : Int) * μ.record.signedMass (fun x => f x * g x) -
    μ.record.signedMass f * μ.record.signedMass g = 0
  rw [mean, product, ← Int.mul_assoc, Int.sub_self]

/-- Covariance Cauchy–Schwarz with the common positive denominator cleared.
The zero-variance case is proved separately, so no positive-variance premise
or division by a possibly zero moment is hidden in this inequality. -/
theorem Distro.signedCovariance_cauchy_num (μ : Distro Ω) (f g : Ω → Int) :
    (μ.signedCovariance f g).num * (μ.signedCovariance f g).num ≤
      (μ.signedCovariance f f).num * (μ.signedCovariance g g).num := by
  let A := (μ.signedCovariance f f).num
  let B := (μ.signedCovariance g g).num
  let C := (μ.signedCovariance f g).num
  have nonnegative := μ.signedCovariance_self_nonnegative g
  change 0 ≤ B at nonnegative
  by_cases zero : B = 0
  · have varianceZero : (μ.varianceInt g).num = 0 := by
      apply Int.ofNat_inj.mp
      exact (μ.varianceInt_num_cast g).trans zero
    have cross := μ.signedCovariance_zero_of_varianceInt_zero g f varianceZero
    rw [μ.signedCovariance_symm g f] at cross
    change C = 0 at cross
    change C * C ≤ A * B
    simp only [cross, zero, Int.mul_zero, Int.le_refl]
  · have positive : 0 < B := by omega
    have quadratic := μ.signedCovariance_self_nonnegative (fun x => B * f x + (-C) * g x)
    rw [μ.signedCovariance_linear_self_num] at quadratic
    change 0 ≤ B * B * A + (-C) * (-C) * B + 2 * B * (-C) * C at quadratic
    have factor : B * B * A + (-C) * (-C) * B + 2 * B * (-C) * C = B * (A * B - C * C) := by
      calc
        _ = B * (A * B) + B * (C * C) - 2 * (B * (C * C)) := by
          simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.sub_eq_add_neg]
          ac_rfl
        _ = B * (A * B) - B * (C * C) := by omega
        _ = _ := (Int.mul_sub _ _ _).symm
    rw [factor] at quadratic
    have result := Int.nonneg_of_mul_nonneg_right quadratic positive
    change C * C ≤ A * B
    omega

/-- A signed rational square is an ordinary nonnegative rational. -/
def SignedMoment.square (moment : SignedMoment) : QProb :=
  ⟨moment.num.natAbs * moment.num.natAbs, moment.den * moment.den, Nat.mul_pos moment.den_pos moment.den_pos⟩

/-- Cov(f,g)² ≤ Var(f) Var(g), for arbitrary integer observables. -/
theorem Distro.signedCovariance_cauchy (μ : Distro Ω) (f g : Ω → Int) :
    QProb.LE (SignedMoment.square (μ.signedCovariance f g))
      (QProb.mul (μ.varianceInt f) (μ.varianceInt g)) := by
  have numerator : (μ.signedCovariance f g).num.natAbs * (μ.signedCovariance f g).num.natAbs ≤
      (μ.varianceInt f).num * (μ.varianceInt g).num := by
    apply Int.ofNat_le.mp
    rw [Int.natAbs_mul_self, Int.natCast_mul, μ.varianceInt_num_cast, μ.varianceInt_num_cast]
    exact μ.signedCovariance_cauchy_num f g
  change ((μ.signedCovariance f g).num.natAbs * (μ.signedCovariance f g).num.natAbs) *
      ((μ.record.den * μ.record.den) * (μ.record.den * μ.record.den)) ≤
    ((μ.varianceInt f).num * (μ.varianceInt g).num) *
      ((μ.record.den * μ.record.den) * (μ.record.den * μ.record.den))
  exact Nat.mul_le_mul_right _ numerator

end Thesis.Probability.Distros
