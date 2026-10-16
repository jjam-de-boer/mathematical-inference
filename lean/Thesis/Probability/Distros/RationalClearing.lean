import Thesis.Probability.Distros.RationalMoments
import Thesis.Probability.SignedRatioOrder

namespace Thesis.Probability.Distros

/-- A denominator constructed only from the supplied finite atom occurrences.
No equality decision or enumeration of the ambient outcome type is needed. -/
def ratioObservableDenominator (atoms : List (Ω × Nat)) (f : Ω → SignedRatio) : Nat :=
  observableDenominator atoms (fun x => ⟨0, (f x).den, (f x).den_pos⟩)

theorem ratioObservableDenominator_pos (atoms : List (Ω × Nat)) (f : Ω → SignedRatio) :
    0 < ratioObservableDenominator atoms f :=
  observableDenominator_pos atoms _

def ratioObservableNumerator (denominator : Nat) (f : Ω → SignedRatio) (x : Ω) : Int :=
  (f x).num * ((denominator / (f x).den : Nat) : Int)

theorem ratioObservable_cleared (atoms : List (Ω × Nat)) (f : Ω → SignedRatio)
    (atom : Ω × Nat) (member : atom ∈ atoms) :
    SignedRatio.Equiv (f atom.1)
      ⟨ratioObservableNumerator (ratioObservableDenominator atoms f) f atom.1,
        ratioObservableDenominator atoms f, ratioObservableDenominator_pos atoms f⟩ := by
  have dvd := observableDenominator_dvd atoms (fun x => (⟨0, (f x).den, (f x).den_pos⟩ : QProb)) atom member
  change (f atom.1).num * (ratioObservableDenominator atoms f : Int) =
    ((f atom.1).num * ((ratioObservableDenominator atoms f / (f atom.1).den : Nat) : Int)) * (f atom.1).den
  rw [Int.mul_assoc, ← Int.natCast_mul, Nat.div_mul_cancel dvd]

theorem rationalAtomSum_congr_on_support (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio)
    (same : ∀ atom ∈ atoms, SignedRatio.Equiv (f atom.1) (g atom.1)) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms f) (FiniteProbRecord.rationalAtomSum atoms g) := by
  induction atoms with
  | nil => exact SignedRatio.equiv_refl _
  | cons atom atoms ih =>
      exact SignedRatio.add_congr
        (SignedRatio.scaleNat_congr atom.2 (same atom (List.mem_cons_self ..)))
        (ih (fun other member => same other (List.mem_cons_of_mem _ member)))

theorem Distro.rationalExpectation_congr_on_support (μ : Distro Ω) (f g : Ω → SignedRatio)
    (same : ∀ atom ∈ μ.record.atoms, SignedRatio.Equiv (f atom.1) (g atom.1)) :
    SignedRatio.Equiv (μ.rationalExpectation f) (μ.rationalExpectation g) :=
  SignedRatio.divideNat_congr (rationalAtomSum_congr_on_support _ _ _ same) μ.record.den μ.record.den_pos

/-- Integrating an integer observable divided by a positive common denominator. -/
theorem Distro.rationalExpectation_commonDen (μ : Distro Ω) (f : Ω → Int)
    (denominator : Nat) (positive : 0 < denominator) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => ⟨f x, denominator, positive⟩))
      (SignedRatio.divideNat (μ.signedExpectation f).toRatio denominator positive) :=
  μ.record.rationalMean_cleared _ f denominator positive (fun _ => SignedRatio.equiv_refl _)

theorem Distro.rationalExpectation_cleared (μ : Distro Ω) (f : Ω → SignedRatio)
    (g : Ω → Int) (denominator : Nat) (positive : 0 < denominator)
    (same : ∀ atom ∈ μ.record.atoms, SignedRatio.Equiv (f atom.1) ⟨g atom.1, denominator, positive⟩) :
    SignedRatio.Equiv (μ.rationalExpectation f)
      (SignedRatio.divideNat (μ.signedExpectation g).toRatio denominator positive) :=
  SignedRatio.equiv_trans (μ.rationalExpectation_congr_on_support _ _ same)
    (μ.rationalExpectation_commonDen g denominator positive)

theorem Distro.rationalCovariance_congr_on_support (μ : Distro Ω) (f f' g g' : Ω → SignedRatio)
    (first : ∀ atom ∈ μ.record.atoms, SignedRatio.Equiv (f atom.1) (f' atom.1))
    (second : ∀ atom ∈ μ.record.atoms, SignedRatio.Equiv (g atom.1) (g' atom.1)) :
    SignedRatio.Equiv (μ.rationalCovariance f g) (μ.rationalCovariance f' g') :=
  ratio_sub_congr
    (μ.rationalExpectation_congr_on_support _ _ (fun atom member => SignedRatio.mul_congr (first atom member) (second atom member)))
    (SignedRatio.mul_congr (μ.rationalExpectation_congr_on_support _ _ first)
      (μ.rationalExpectation_congr_on_support _ _ second))

/-- Denominator clearing preserves covariance, with one denominator factor
from each observable. The probability record itself is unchanged. -/
theorem Distro.rationalCovariance_commonDen (μ : Distro Ω) (f g : Ω → Int)
    (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    SignedRatio.Equiv (μ.rationalCovariance (fun x => ⟨f x, d, hd⟩) (fun x => ⟨g x, e, he⟩))
      (SignedRatio.divideNat (μ.signedCovariance f g).toRatio (d * e) (Nat.mul_pos hd he)) := by
  have expression := ratio_sub_congr
    (μ.rationalExpectation_commonDen (fun x => f x * g x) (d * e) (Nat.mul_pos hd he))
    (SignedRatio.mul_congr (μ.rationalExpectation_commonDen f d hd) (μ.rationalExpectation_commonDen g e he))
  refine SignedRatio.equiv_trans expression ?_
  simp only [SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add, SignedRatio.neg,
    SignedRatio.mul, SignedRatio.divideNat, SignedMoment.toRatio, signedExpectation,
    signedCovariance, Int.natCast_mul, Int.add_mul, Int.neg_mul, Int.sub_mul]
  congr 1 <;> ac_rfl

theorem Distro.rationalCovariance_cleared (μ : Distro Ω) (f g : Ω → SignedRatio)
    (a b : Ω → Int) (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (first : ∀ atom ∈ μ.record.atoms, SignedRatio.Equiv (f atom.1) ⟨a atom.1, d, hd⟩)
    (second : ∀ atom ∈ μ.record.atoms, SignedRatio.Equiv (g atom.1) ⟨b atom.1, e, he⟩) :
    SignedRatio.Equiv (μ.rationalCovariance f g)
      (SignedRatio.divideNat (μ.signedCovariance a b).toRatio (d * e) (Nat.mul_pos hd he)) :=
  SignedRatio.equiv_trans (μ.rationalCovariance_congr_on_support _ _ _ _ first second)
    (μ.rationalCovariance_commonDen a b d e hd he)

/-- Event-law equality transports arbitrary signed rational expectations.
The common denominator is computed over both explicit finite supports. -/
theorem Distro.SameLaw.rationalExpectation {μ ν : Distro Ω} (same : μ.SameLaw ν) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation f) (ν.rationalExpectation f) := by
  let atoms := μ.record.atoms ++ ν.record.atoms
  let denominator := ratioObservableDenominator atoms f
  have positive := ratioObservableDenominator_pos atoms f
  let g := ratioObservableNumerator denominator f
  have first := μ.rationalExpectation_cleared f g denominator positive
    (fun atom member => ratioObservable_cleared atoms f atom (List.mem_append_left _ member))
  have second := ν.rationalExpectation_cleared f g denominator positive
    (fun atom member => ratioObservable_cleared atoms f atom (List.mem_append_right _ member))
  exact SignedRatio.equiv_trans first (SignedRatio.equiv_trans
    (SignedRatio.divideNat_congr (SignedMoment.toRatio_congr (same.signedExpectation g)) denominator positive)
    (SignedRatio.equiv_symm second))

theorem Distro.SameLaw.rationalCovariance {μ ν : Distro Ω} (same : μ.SameLaw ν) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f g) (ν.rationalCovariance f g) :=
  ratio_sub_congr (same.rationalExpectation (fun x => SignedRatio.mul (f x) (g x)))
    (SignedRatio.mul_congr (same.rationalExpectation f) (same.rationalExpectation g))

theorem Distro.SameLaw.rationalVariance {μ ν : Distro Ω} (same : μ.SameLaw ν) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalVariance f) (ν.rationalVariance f) := same.rationalCovariance f f

theorem Distro.rationalCovariance_map (μ : Distro Ω) (encode : Ω → X) (f g : X → SignedRatio) :
    (μ.map encode).rationalCovariance f g = μ.rationalCovariance (fun x => f (encode x)) (fun x => g (encode x)) := by
  simp only [rationalCovariance, rationalExpectation_map]

theorem Distro.rationalVariance_map (μ : Distro Ω) (encode : Ω → X) (f : X → SignedRatio) :
    (μ.map encode).rationalVariance f = μ.rationalVariance (fun x => f (encode x)) :=
  μ.rationalCovariance_map encode f f

/-- Every signed rational observable has nonnegative variance. Clearing is
performed on finite support, so no global bound on observable denominators is assumed. -/
theorem Distro.rationalVariance_nonnegative (μ : Distro Ω) (f : Ω → SignedRatio) :
    SignedRatio.Nonnegative (μ.rationalVariance f) := by
  let d := ratioObservableDenominator μ.record.atoms f
  have hd := ratioObservableDenominator_pos μ.record.atoms f
  let g := ratioObservableNumerator d f
  have same := μ.rationalCovariance_cleared f f g g d d hd hd
    (ratioObservable_cleared μ.record.atoms f) (ratioObservable_cleared μ.record.atoms f)
  exact (SignedRatio.nonnegative_congr same).mpr (μ.signedCovariance_self_nonnegative g)

end Thesis.Probability.Distros
