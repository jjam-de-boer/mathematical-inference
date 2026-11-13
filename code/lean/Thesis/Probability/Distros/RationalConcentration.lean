import Thesis.Probability.Distros.RationalClearing
import Thesis.Probability.Distros.SignedCauchy

namespace Thesis.Probability.SignedRatio

theorem equiv_num_zero_iff {a b : SignedRatio} (same : Equiv a b) : a.num = 0 ↔ b.num = 0 := by
  constructor
  · intro zero
    exact (equiv_zero_iff b).mp (equiv_trans (equiv_symm same) ((equiv_zero_iff a).mpr zero))
  · intro zero
    exact (equiv_zero_iff a).mp (equiv_trans same ((equiv_zero_iff b).mpr zero))

theorem le_iff_cross (a b : SignedRatio) : LE a b ↔ a.num * (b.den : Int) ≤ b.num * (a.den : Int) := by
  change 0 ≤ b.num * (a.den : Int) + -a.num * (b.den : Int) ↔ _
  rw [Int.neg_mul]
  exact Int.sub_nonneg

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.Distros

/-- Almost-sure equivalence is sufficient for moment congruence; arbitrary
values on zero-weight occurrences do not affect a rational integral. -/
theorem rationalAtomSum_congr_positive (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio)
    (same : ∀ atom ∈ atoms, 0 < atom.2 → SignedRatio.Equiv (f atom.1) (g atom.1)) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms f) (FiniteProbRecord.rationalAtomSum atoms g) := by
  induction atoms with
  | nil => exact SignedRatio.equiv_refl _
  | cons atom atoms ih =>
      apply SignedRatio.add_congr
      · by_cases zero : atom.2 = 0
        · simp only [SignedRatio.Equiv, SignedRatio.scaleNat, zero, Int.natCast_zero, Int.zero_mul]
        · exact SignedRatio.scaleNat_congr atom.2 (same atom (List.mem_cons_self ..) (Nat.pos_of_ne_zero zero))
      · exact ih (fun other member => same other (List.mem_cons_of_mem _ member))

theorem Distro.rationalExpectation_congr_positive (μ : Distro Ω) (f g : Ω → SignedRatio)
    (same : μ.AlmostSurely (fun x => SignedRatio.Equiv (f x) (g x))) :
    SignedRatio.Equiv (μ.rationalExpectation f) (μ.rationalExpectation g) :=
  SignedRatio.divideNat_congr (rationalAtomSum_congr_positive _ _ _ same) μ.record.den μ.record.den_pos

theorem Distro.rationalCovariance_congr_positive (μ : Distro Ω) (f f' g g' : Ω → SignedRatio)
    (first : μ.AlmostSurely (fun x => SignedRatio.Equiv (f x) (f' x)))
    (second : μ.AlmostSurely (fun x => SignedRatio.Equiv (g x) (g' x))) :
    SignedRatio.Equiv (μ.rationalCovariance f g) (μ.rationalCovariance f' g') :=
  ratio_sub_congr
    (μ.rationalExpectation_congr_positive _ _ (fun atom member weight =>
      SignedRatio.mul_congr (first atom member weight) (second atom member weight)))
    (SignedRatio.mul_congr (μ.rationalExpectation_congr_positive _ _ first)
      (μ.rationalExpectation_congr_positive _ _ second))

theorem Distro.rationalVariance_constant (μ : Distro Ω) (c : SignedRatio) :
    SignedRatio.Equiv (μ.rationalVariance (fun _ => c)) SignedRatio.zero :=
  SignedRatio.equiv_trans
    (ratio_sub_congr (μ.rationalExpectation_constant (SignedRatio.mul c c))
      (SignedRatio.mul_congr (μ.rationalExpectation_constant c) (μ.rationalExpectation_constant c)))
    ((SignedRatio.sub_equiv_zero_iff _ _).mpr (SignedRatio.equiv_refl _))

/-- Zero variance characterizes actual almost-sure rational constants.
The conclusion uses rational equivalence, so unreduced presentations and
zero-weight outliers are both harmless. -/
theorem Distro.rationalVariance_zero_iff_constant (μ : Distro Ω) (f : Ω → SignedRatio) :
    (μ.rationalVariance f).num = 0 ↔ ∃ c : SignedRatio, μ.AlmostSurely (fun x => SignedRatio.Equiv (f x) c) := by
  constructor
  · intro zero
    let d := ratioObservableDenominator μ.record.atoms f
    have hd := ratioObservableDenominator_pos μ.record.atoms f
    let a := ratioObservableNumerator d f
    have cleared := μ.rationalCovariance_cleared f f a a d d hd hd
      (ratioObservable_cleared μ.record.atoms f) (ratioObservable_cleared μ.record.atoms f)
    have intZero : (μ.varianceInt a).num = 0 := by
      apply Int.ofNat_inj.mp
      rw [μ.varianceInt_num_cast]
      exact (SignedRatio.equiv_num_zero_iff cleared).mp zero
    rcases (μ.varianceInt_zero_iff_constant a).mp intZero with ⟨c, constant⟩
    refine ⟨⟨c, d, hd⟩, fun atom member weight => ?_⟩
    refine SignedRatio.equiv_trans (ratioObservable_cleared μ.record.atoms f atom member) ?_
    change SignedRatio.Equiv ⟨a atom.1, d, hd⟩ ⟨c, d, hd⟩
    rw [constant atom member weight]
    exact SignedRatio.equiv_refl _
  · rintro ⟨c, constant⟩
    exact (SignedRatio.equiv_zero_iff _).mp (SignedRatio.equiv_trans
      (μ.rationalCovariance_congr_positive f (fun _ => c) f (fun _ => c) constant constant)
      (μ.rationalVariance_constant c))

/-- Cov(f,g)^2 ≤ Var(f) Var(g) for all signed rational observables.
Finite support supplies the two clearing denominators; there is no global
integrality premise or nonzero-variance restriction. -/
theorem Distro.rationalCovariance_cauchy (μ : Distro Ω) (f g : Ω → SignedRatio) :
    SignedRatio.LE (SignedRatio.mul (μ.rationalCovariance f g) (μ.rationalCovariance f g))
      (SignedRatio.mul (μ.rationalVariance f) (μ.rationalVariance g)) := by
  let d := ratioObservableDenominator μ.record.atoms f
  let e := ratioObservableDenominator μ.record.atoms g
  have hd := ratioObservableDenominator_pos μ.record.atoms f
  have he := ratioObservableDenominator_pos μ.record.atoms g
  let a := ratioObservableNumerator d f
  let b := ratioObservableNumerator e g
  have cross := μ.rationalCovariance_cleared f g a b d e hd he
    (ratioObservable_cleared μ.record.atoms f) (ratioObservable_cleared μ.record.atoms g)
  have first := μ.rationalCovariance_cleared f f a a d d hd hd
    (ratioObservable_cleared μ.record.atoms f) (ratioObservable_cleared μ.record.atoms f)
  have second := μ.rationalCovariance_cleared g g b b e e he he
    (ratioObservable_cleared μ.record.atoms g) (ratioObservable_cleared μ.record.atoms g)
  apply (SignedRatio.le_congr (SignedRatio.mul_congr cross cross) (SignedRatio.mul_congr first second)).mpr
  rw [SignedRatio.le_iff_cross]
  let D := μ.record.den * μ.record.den
  change ((μ.signedCovariance a b).num * (μ.signedCovariance a b).num) *
      (((D * (d * d)) * (D * (e * e)) : Nat) : Int) ≤
    ((μ.signedCovariance a a).num * (μ.signedCovariance b b).num) *
      (((D * (d * e)) * (D * (d * e)) : Nat) : Int)
  have denominator : (D * (d * d)) * (D * (e * e)) = (D * (d * e)) * (D * (d * e)) := by ac_rfl
  rw [denominator]
  exact Int.mul_le_mul_of_nonneg_right (μ.signedCovariance_cauchy_num a b) (Int.natCast_nonneg _)

end Thesis.Probability.Distros
