import Thesis.Probability.ConstructiveRealLimits
import Thesis.Probability.RationalNorm
import Thesis.Probability.RationalPrecision

namespace Thesis.Probability.ConstructiveReal

/-- Two-sided rational error in the closed real order. No arbitrary real
comparison is performed to produce or consume this certificate. -/
def Within (error : QProb) (x y : ConstructiveReal) : Prop :=
  LE x (add y (ofSignedRatio error.toSignedRatio)) ∧ LE y (add x (ofSignedRatio error.toSignedRatio))

theorem within_symm {error : QProb} {x y : ConstructiveReal} (bounded : Within error x y) : Within error y x :=
  ⟨bounded.2, bounded.1⟩

theorem within_congr {error : QProb} {x x' y y' : ConstructiveReal} (first : Equiv x x') (second : Equiv y y') :
    Within error x y ↔ Within error x' y' :=
  and_congr (le_congr first (add_congr second (equiv_refl _)))
    (le_congr second (add_congr first (equiv_refl _)))

private theorem combine_errors (z : ConstructiveReal) (first second : QProb) :
    Equiv (add (add z (ofSignedRatio second.toSignedRatio)) (ofSignedRatio first.toSignedRatio))
      (add z (ofSignedRatio (QProb.add first second).toSignedRatio)) := by
  rw [QProb.toSignedRatio_add]
  exact equiv_trans (add_assoc _ _ _)
    (add_congr (equiv_refl _) (equiv_trans (add_comm _ _) (ofSignedRatio_add _ _)))

theorem within_triangle {first second : QProb} {x y z : ConstructiveReal}
    (left : Within first x y) (right : Within second y z) : Within (QProb.add first second) x z := by
  constructor
  · have compared := le_trans left.1 (add_le_add right.1 (le_refl _))
    exact (le_congr (equiv_refl _) (combine_errors z first second)).mp compared
  · have compared := le_trans right.2 (add_le_add left.2 (le_refl _))
    have combined := equiv_trans (add_assoc x (ofSignedRatio first.toSignedRatio) (ofSignedRatio second.toSignedRatio))
      (add_congr (equiv_refl x) (ofSignedRatio_add first.toSignedRatio second.toSignedRatio))
    rw [QProb.toSignedRatio_add]
    exact (le_congr (equiv_refl _) combined).mp compared

theorem within_mono {first second : QProb} {x y : ConstructiveReal}
    (bounded : Within first x y) (larger : QProb.LE first second) : Within second x y := by
  have errors := (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr larger)
  exact ⟨le_trans bounded.1 (add_le_add (le_refl _) errors), le_trans bounded.2 (add_le_add (le_refl _) errors)⟩

theorem within_ofSignedRatio_iff (a b : SignedRatio) (error : QProb) :
    Within error (ofSignedRatio a) (ofSignedRatio b) ↔ QProb.LE (SignedRatio.sub a b).magnitude error := by
  unfold Within
  have first := (le_congr (equiv_refl (ofSignedRatio a)) (ofSignedRatio_add b error.toSignedRatio)).trans
    (ofSignedRatio_le_iff _ _)
  have second := (le_congr (equiv_refl (ofSignedRatio b)) (ofSignedRatio_add a error.toSignedRatio)).trans
    (ofSignedRatio_le_iff _ _)
  exact (and_congr first second).trans (SignedRatio.magnitude_sub_le_iff a b error).symm

/-- Closed order is separated by all positive rational error tolerances. -/
theorem le_of_forall_rational_error (x y : ConstructiveReal)
    (bounded : ∀ error : PositiveRatio, LE x (add y (ofSignedRatio error.toSignedRatio))) : LE x y := by
  intro first second
  apply SignedRatio.le_of_forall_add_positive
  intro error
  have compared := bounded error.half first error
  have widened := SignedRatio.add_le_add (y.enclose error.half).width (SignedRatio.le_refl error.half.toSignedRatio)
  have collected := SignedRatio.equiv_trans (SignedRatio.add_assoc (y.enclose error.half).lower
    error.half.toSignedRatio error.half.toSignedRatio)
    (SignedRatio.add_congr (SignedRatio.equiv_refl _) error.half_add_half)
  have near := (SignedRatio.le_congr (SignedRatio.equiv_refl _) collected).mp (SignedRatio.le_trans compared widened)
  exact SignedRatio.le_trans near (SignedRatio.add_le_add (y.coherent error.half second) (SignedRatio.le_refl _))

theorem equiv_of_within_all (x y : ConstructiveReal)
    (bounded : ∀ error : PositiveRatio, Within error.toQProb x y) : Equiv x y :=
  ⟨le_of_forall_rational_error x y (fun error => (bounded error).1),
    le_of_forall_rational_error y x (fun error => (bounded error).2)⟩

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.RegularRationalApproximation

/-- The rational algorithm's advertised error is also a real distance bound. -/
theorem limit_within (approximation : RegularRationalApproximation) (precision : PositiveRatio) :
    ConstructiveReal.Within precision.toQProb approximation.limit (ConstructiveReal.ofSignedRatio (approximation.value precision)) := by
  have bounds := approximation.approximation_bounds precision
  constructor
  · exact (ConstructiveReal.le_congr (ConstructiveReal.equiv_refl _) (ConstructiveReal.ofSignedRatio_add _ _)).mpr bounds.2
  · have translated := ConstructiveReal.add_le_add bounds.1
      (ConstructiveReal.le_refl (ConstructiveReal.ofSignedRatio precision.toSignedRatio))
    have reduced := ConstructiveReal.equiv_trans
      (ConstructiveReal.ofSignedRatio_add (SignedRatio.sub (approximation.value precision) precision.toSignedRatio) precision.toSignedRatio)
      ((ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr
        (SignedRatio.sub_add_cancel (approximation.value precision) precision.toSignedRatio))
    exact (ConstructiveReal.le_congr reduced (ConstructiveReal.equiv_refl _)).mp translated

theorem error_of_limit_equiv (first second : RegularRationalApproximation)
    (same : ConstructiveReal.Equiv first.limit second.limit) (left right : PositiveRatio) :
    QProb.LE (SignedRatio.sub (first.value left) (second.value right)).magnitude
      (QProb.add left.toQProb right.toQProb) := by
  have fromCenter := ConstructiveReal.within_symm (first.limit_within left)
  have aligned := (ConstructiveReal.within_congr (ConstructiveReal.equiv_refl _) same).mp fromCenter
  exact (ConstructiveReal.within_ofSignedRatio_iff _ _ _).mp
    (ConstructiveReal.within_triangle aligned (second.limit_within right))

/-- Any fixed multiple of the requested rational errors still separates
limit values. The comparison precision is computed from that multiple. -/
theorem limit_equiv_of_error_bound (first second : RegularRationalApproximation) (factor : Nat)
    (bounded : ∀ left right, QProb.LE (SignedRatio.sub (first.value left) (second.value right)).magnitude
      (QProb.mul (QProb.ofNat factor) (QProb.add left.toQProb right.toQProb))) :
    ConstructiveReal.Equiv first.limit second.limit := by
  apply ConstructiveReal.equiv_of_within_all
  intro tolerance
  let denominator := 2 * (factor + 1)
  have positive : 0 < denominator := Nat.mul_pos (by decide) (Nat.zero_lt_succ factor)
  let precision := tolerance.divideNat denominator positive
  have left := first.limit_within precision
  have middle := (ConstructiveReal.within_ofSignedRatio_iff _ _ _).mpr (bounded precision precision)
  have right := ConstructiveReal.within_symm (second.limit_within precision)
  have combined := ConstructiveReal.within_triangle (ConstructiveReal.within_triangle left middle) right
  have regrouped : QProb.Equiv
      (QProb.add (QProb.add precision.toQProb
        (QProb.mul (QProb.ofNat factor) (QProb.add precision.toQProb precision.toQProb))) precision.toQProb)
      (QProb.mul precision.toQProb (QProb.ofNat denominator)) := by
    simp only [denominator, QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat,
      Nat.mul_one, Nat.one_mul, Nat.two_mul, Nat.mul_two, Nat.mul_add, Nat.add_mul]
    ac_rfl
  have sameError := QProb.equiv_trans regrouped (PositiveRatio.divide_mul tolerance denominator positive)
  exact ConstructiveReal.within_mono combined
    (QProb.le_congr (QProb.equiv_refl _) sameError (QProb.le_refl _))

end Thesis.Probability.RegularRationalApproximation
