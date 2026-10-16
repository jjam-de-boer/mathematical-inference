import Thesis.Probability.Distros.ConditionalPartitions

namespace Thesis.Probability.Distros

private theorem ratio_sub_add_sub (a b c : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.add (SignedRatio.sub a b) (SignedRatio.sub b c)) (SignedRatio.sub a c) := by
  simp only [SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add, SignedRatio.neg,
    Int.natCast_mul, Int.mul_add, Int.mul_neg,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- Total covariance over a finite partition:
Cov(f,g) = E[Cov(f,g | cell)] + Cov(E[f | cell], E[g | cell]).
Both original observables and the conditional means are signed rational-valued.
Zero-mass cells use the explicit zero conditional mean and contribute no mass. -/
theorem AtomPartition.total_covariance {μ : Distro Ω} (partition : AtomPartition μ) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f g)
      (SignedRatio.add
        (partition.distro.rationalExpectation (fun cell => conditionalBlockCovariance cell f g))
        (partition.distro.rationalCovariance (fun cell => conditionalBlockMean cell f) (fun cell => conditionalBlockMean cell g))) := by
  let ν := partition.distro
  let mf := fun cell => conditionalBlockMean cell f
  let mg := fun cell => conditionalBlockMean cell g
  let product := fun cell => SignedRatio.mul (mf cell) (mg cell)
  have within : SignedRatio.Equiv (ν.rationalExpectation (fun cell => conditionalBlockCovariance cell f g))
      (SignedRatio.sub (μ.rationalExpectation (fun x => SignedRatio.mul (f x) (g x))) (ν.rationalExpectation product)) :=
    SignedRatio.equiv_trans (ν.rationalExpectation_sub _ _)
      (ratio_sub_congr (partition.total_expectation _) (SignedRatio.equiv_refl _))
  have between : SignedRatio.Equiv (ν.rationalCovariance mf mg)
      (SignedRatio.sub (ν.rationalExpectation product)
        (SignedRatio.mul (μ.rationalExpectation f) (μ.rationalExpectation g))) :=
    ratio_sub_congr (SignedRatio.equiv_refl _)
      (SignedRatio.mul_congr (partition.total_expectation f) (partition.total_expectation g))
  exact SignedRatio.equiv_symm (SignedRatio.equiv_trans (SignedRatio.add_congr within between) (ratio_sub_add_sub _ _ _))

/-- Total variance with a genuine rational-valued conditional-mean observable. -/
theorem AtomPartition.total_variance {μ : Distro Ω} (partition : AtomPartition μ) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalVariance f)
      (SignedRatio.add
        (partition.distro.rationalExpectation (fun cell => conditionalBlockVariance cell f))
        (partition.distro.rationalVariance (fun cell => conditionalBlockMean cell f))) :=
  partition.total_covariance f f

end Thesis.Probability.Distros
