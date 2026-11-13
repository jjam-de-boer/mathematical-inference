import Thesis.Probability.Distros.SignedCovariance
import Thesis.Probability.FiniteRationalMoment
import Thesis.Probability.SignedRatioAlgebra

namespace Thesis.Probability.Distros

/-- Signed rational observables include the nonintegral conditional means
needed in finite total-variance and total-covariance formulas. -/
def Distro.rationalExpectation (μ : Distro Ω) (f : Ω → SignedRatio) : SignedRatio := μ.record.rationalMean f

def Distro.rationalCovariance (μ : Distro Ω) (f g : Ω → SignedRatio) : SignedRatio :=
  SignedRatio.sub (μ.rationalExpectation (fun x => SignedRatio.mul (f x) (g x)))
    (SignedRatio.mul (μ.rationalExpectation f) (μ.rationalExpectation g))

def Distro.rationalVariance (μ : Distro Ω) (f : Ω → SignedRatio) : SignedRatio := μ.rationalCovariance f f

def SignedMoment.toRatio (moment : SignedMoment) : SignedRatio := ⟨moment.num, moment.den, moment.den_pos⟩

private theorem scaleNat_add (weight : Nat) (a b : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.scaleNat weight (SignedRatio.add a b))
      (SignedRatio.add (SignedRatio.scaleNat weight a) (SignedRatio.scaleNat weight b)) := by
  simp only [SignedRatio.Equiv, SignedRatio.scaleNat, SignedRatio.add, Int.natCast_mul, Int.mul_add, Int.add_mul]
  ac_rfl

private theorem scaleNat_mul (weight : Nat) (a b : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.scaleNat weight (SignedRatio.mul a b))
      (SignedRatio.mul a (SignedRatio.scaleNat weight b)) := by
  simp only [SignedRatio.Equiv, SignedRatio.scaleNat, SignedRatio.mul, Int.natCast_mul]
  ac_rfl

private theorem divideNat_add (a b : SignedRatio) (denominator : Nat) (positive : 0 < denominator) :
    SignedRatio.Equiv (SignedRatio.divideNat (SignedRatio.add a b) denominator positive)
      (SignedRatio.add (SignedRatio.divideNat a denominator positive) (SignedRatio.divideNat b denominator positive)) := by
  simp only [SignedRatio.Equiv, SignedRatio.divideNat, SignedRatio.add, Int.natCast_mul, Int.add_mul]
  ac_rfl

private theorem divideNat_mul (a b : SignedRatio) (denominator : Nat) (positive : 0 < denominator) :
    SignedRatio.Equiv (SignedRatio.divideNat (SignedRatio.mul a b) denominator positive)
      (SignedRatio.mul a (SignedRatio.divideNat b denominator positive)) := by
  simp only [SignedRatio.Equiv, SignedRatio.divideNat, SignedRatio.mul, Int.natCast_mul]
  ac_rfl

theorem rationalAtomSum_congr (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio)
    (same : ∀ x, SignedRatio.Equiv (f x) (g x)) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms f) (FiniteProbRecord.rationalAtomSum atoms g) :=
  SignedRatio.listSum_map_congr atoms _ _ (fun atom => SignedRatio.scaleNat_congr atom.2 (same atom.1))

theorem rationalAtomSum_add (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms (fun x => SignedRatio.add (f x) (g x)))
      (SignedRatio.add (FiniteProbRecord.rationalAtomSum atoms f) (FiniteProbRecord.rationalAtomSum atoms g)) :=
  SignedRatio.equiv_trans (SignedRatio.listSum_map_congr atoms _ _ (fun atom => scaleNat_add atom.2 (f atom.1) (g atom.1)))
    (SignedRatio.listSum_map_add atoms _ _)

theorem rationalAtomSum_mul_left (atoms : List (Ω × Nat)) (factor : SignedRatio) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms (fun x => SignedRatio.mul factor (f x)))
      (SignedRatio.mul factor (FiniteProbRecord.rationalAtomSum atoms f)) := by
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr atoms _ _
    (fun atom => scaleNat_mul atom.2 factor (f atom.1))) ?_
  have result := SignedRatio.mul_listSum factor (atoms.map (fun atom => SignedRatio.scaleNat atom.2 (f atom.1)))
  simpa only [FiniteProbRecord.rationalAtomSum, List.map_map, Function.comp_def] using SignedRatio.equiv_symm result

theorem Distro.rationalExpectation_congr (μ : Distro Ω) (f g : Ω → SignedRatio)
    (same : ∀ x, SignedRatio.Equiv (f x) (g x)) :
    SignedRatio.Equiv (μ.rationalExpectation f) (μ.rationalExpectation g) :=
  SignedRatio.divideNat_congr (rationalAtomSum_congr _ _ _ same) μ.record.den μ.record.den_pos

theorem Distro.rationalExpectation_map (μ : Distro Ω) (encode : Ω → X) (f : X → SignedRatio) :
    (μ.map encode).rationalExpectation f = μ.rationalExpectation (fun x => f (encode x)) :=
  μ.record.rationalMean_map encode f

theorem Distro.rationalExpectation_add (μ : Distro Ω) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.add (f x) (g x)))
      (SignedRatio.add (μ.rationalExpectation f) (μ.rationalExpectation g)) :=
  SignedRatio.equiv_trans (SignedRatio.divideNat_congr (rationalAtomSum_add _ _ _) μ.record.den μ.record.den_pos)
    (divideNat_add _ _ μ.record.den μ.record.den_pos)

theorem Distro.rationalExpectation_mul_left (μ : Distro Ω) (factor : SignedRatio) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.mul factor (f x)))
      (SignedRatio.mul factor (μ.rationalExpectation f)) :=
  SignedRatio.equiv_trans (SignedRatio.divideNat_congr (rationalAtomSum_mul_left _ _ _) μ.record.den μ.record.den_pos)
    (divideNat_mul _ _ μ.record.den μ.record.den_pos)

theorem Distro.rationalExpectation_constant (μ : Distro Ω) (value : SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun _ => value)) value := by
  refine SignedRatio.equiv_trans (μ.record.rationalMean_cleared (fun _ => value)
    (fun _ => value.num) value.den value.den_pos (fun _ => SignedRatio.equiv_refl _)) ?_
  rw [FiniteProbRecord.signedMass_const]
  simp only [SignedRatio.Equiv, SignedRatio.divideNat, Int.natCast_mul]
  ac_rfl

/-- Integer expectations agree with the existing signed moment interface. -/
theorem Distro.rationalExpectation_int (μ : Distro Ω) (f : Ω → Int) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => (⟨f x, 1, Nat.zero_lt_one⟩ : SignedRatio)))
      (μ.signedExpectation f).toRatio := by
  refine SignedRatio.equiv_trans (μ.record.rationalMean_cleared _ f 1 (Nat.zero_lt_one)
    (fun _ => SignedRatio.equiv_refl _)) ?_
  simp only [SignedRatio.Equiv, SignedRatio.divideNat, SignedMoment.toRatio, signedExpectation, Nat.mul_one]

private theorem negativeOne_mul (value : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.mul ⟨-1, 1, Nat.zero_lt_one⟩ value) (SignedRatio.neg value) := by
  simp only [SignedRatio.Equiv, SignedRatio.mul, SignedRatio.neg, Nat.one_mul,
    Int.neg_mul, Int.one_mul]

theorem Distro.rationalExpectation_neg (μ : Distro Ω) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.neg (f x)))
      (SignedRatio.neg (μ.rationalExpectation f)) :=
  SignedRatio.equiv_trans (μ.rationalExpectation_congr _ _ (fun x => SignedRatio.equiv_symm (negativeOne_mul (f x))))
    (SignedRatio.equiv_trans (μ.rationalExpectation_mul_left _ _) (negativeOne_mul _))

theorem Distro.rationalExpectation_sub (μ : Distro Ω) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.sub (f x) (g x)))
      (SignedRatio.sub (μ.rationalExpectation f) (μ.rationalExpectation g)) :=
  SignedRatio.equiv_trans (μ.rationalExpectation_add _ _)
    (SignedRatio.add_congr (SignedRatio.equiv_refl _) (μ.rationalExpectation_neg g))

theorem ratio_sub_congr {a b c d : SignedRatio} (first : SignedRatio.Equiv a b) (second : SignedRatio.Equiv c d) :
    SignedRatio.Equiv (SignedRatio.sub a c) (SignedRatio.sub b d) :=
  SignedRatio.add_congr first (SignedRatio.neg_congr second)

theorem Distro.rationalExpectation_listSum (μ : Distro Ω) (values : List X) (f : X → Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.listSum (values.map (fun i => f i x))))
      (SignedRatio.listSum (values.map (fun i => μ.rationalExpectation (f i)))) := by
  induction values with
  | nil => exact μ.rationalExpectation_constant SignedRatio.zero
  | cons value values ih =>
      exact SignedRatio.equiv_trans (μ.rationalExpectation_add _ _)
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) ih)

theorem SignedMoment.toRatio_congr {a b : SignedMoment} (same : a.Equiv b) :
    SignedRatio.Equiv a.toRatio b.toRatio := same

/-- Rational covariance extends the existing integer-observable covariance. -/
theorem Distro.rationalCovariance_int (μ : Distro Ω) (f g : Ω → Int) :
    SignedRatio.Equiv
      (μ.rationalCovariance (fun x => ⟨f x, 1, Nat.zero_lt_one⟩) (fun x => ⟨g x, 1, Nat.zero_lt_one⟩))
      (μ.signedCovariance f g).toRatio := by
  have expression := ratio_sub_congr (μ.rationalExpectation_int (fun x => f x * g x))
    (SignedRatio.mul_congr (μ.rationalExpectation_int f) (μ.rationalExpectation_int g))
  exact SignedRatio.equiv_trans expression
    (SignedRatio.equiv_symm (SignedMoment.toRatio_congr (μ.signedCovariance_expectations f g)))

/-- Conditional variance decompositions use the same variance as the
existing nonnegative integer-observable interface. -/
theorem Distro.rationalVariance_int (μ : Distro Ω) (f : Ω → Int) :
    SignedRatio.Equiv (μ.rationalVariance (fun x => ⟨f x, 1, Nat.zero_lt_one⟩))
      (SignedMoment.ofQProb (μ.varianceInt f)).toRatio :=
  SignedRatio.equiv_trans (μ.rationalCovariance_int f f)
    (SignedRatio.equiv_symm (SignedMoment.toRatio_congr (μ.varianceInt_signed f)))

theorem Distro.rationalVariance_nat (μ : Distro Ω) (f : Ω → Nat) :
    SignedRatio.Equiv (μ.rationalVariance (fun x => ⟨(f x : Int), 1, Nat.zero_lt_one⟩))
      (SignedMoment.ofQProb (variance (⟨μ, f⟩ : NatDistro Ω))).toRatio :=
  SignedRatio.equiv_trans (μ.rationalVariance_int (fun x => (f x : Int)))
    (SignedMoment.toRatio_congr (SignedMoment.ofQProb_congr (μ.varianceInt_nat f)))

end Thesis.Probability.Distros
