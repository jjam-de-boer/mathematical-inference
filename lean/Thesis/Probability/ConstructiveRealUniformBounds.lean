import Thesis.Probability.ConstructiveRealDifferenceLimits
import Thesis.Probability.ConstructiveRealBounds
import Thesis.Probability.ConstructiveRealDistanceScaling

namespace Thesis.Probability.ConstructiveReal

/-- A presentation-independent natural bound for fine approximants of any
real in the supplied interval. Only the fixed endpoints are enclosed. -/
def intervalMagnitudeBound (lower upper : ConstructiveReal) : Nat :=
  upper.naturalUpper + (neg lower).naturalUpper + 1

private theorem natural_add_one (count : Nat) :
    Equiv (add (ofSignedRatio (QProb.ofNat count).toSignedRatio) one)
      (ofSignedRatio (QProb.ofNat (count + 1)).toSignedRatio) :=
  equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by
    simp only [SignedRatio.Equiv, SignedRatio.add, QProb.ofNat, QProb.toSignedRatio,
      SignedRatio.one, Int.natCast_add, Int.natCast_one, Nat.mul_one, Int.mul_one]))

private theorem natural_mono (first second : Nat) (ordered : first ≤ second) :
    LE (ofSignedRatio (QProb.ofNat first).toSignedRatio) (ofSignedRatio (QProb.ofNat second).toSignedRatio) :=
  (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (by
    simpa only [QProb.LE, QProb.ofNat, Nat.mul_one] using ordered))

private theorem approximant_upper (x upper : ConstructiveReal) (value : SignedRatio)
    (bounded : LE x upper) (precision : PositiveRatio) (small : PositiveRatio.LE precision PositiveRatio.one)
    (close : Within precision.toQProb x (ofSignedRatio value)) :
    LE (ofSignedRatio value) (ofSignedRatio (QProb.ofNat (upper.naturalUpper + 1)).toSignedRatio) := by
  have precisionBound : LE (ofSignedRatio precision.toSignedRatio) one :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr small)
  exact le_trans close.2 ((le_congr (equiv_refl _) (natural_add_one upper.naturalUpper)).mp
    (add_le_add (le_trans bounded upper.le_naturalUpper) precisionBound))

/-- Bounds on real values yield one bound for all their fine rational
presentations. No sign decision on the varying real is made. -/
theorem magnitude_bounded_of_interval (x lower upper : ConstructiveReal)
    (above : LE lower x) (below : LE x upper)
    (precision : PositiveRatio) (small : PositiveRatio.LE precision PositiveRatio.one) :
    QProb.LE (x.rationalApproximation.value precision).magnitude (QProb.ofNat (intervalMagnitudeBound lower upper)) := by
  let value := x.rationalApproximation.value precision
  have close : Within precision.toQProb x (ofSignedRatio value) :=
    (within_congr x.rationalApproximation_limit (equiv_refl _)).mp (x.rationalApproximation.limit_within precision)
  have forward := approximant_upper x upper value below precision small close
  have negativeClose : Within precision.toQProb (neg x) (ofSignedRatio (SignedRatio.neg value)) :=
    (within_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg value))).mp (within_neg close)
  have backward := approximant_upper (neg x) (neg lower) (SignedRatio.neg value)
    ((neg_le_neg_iff lower x).mpr above) precision small negativeClose
  have upperCount : upper.naturalUpper + 1 ≤ intervalMagnitudeBound lower upper := by unfold intervalMagnitudeBound; omega
  have lowerCount : (neg lower).naturalUpper + 1 ≤ intervalMagnitudeBound lower upper := by unfold intervalMagnitudeBound; omega
  exact (SignedRatio.magnitude_le_iff value _).mpr
    ⟨(ofSignedRatio_le_iff _ _).mp (le_trans forward (natural_mono _ _ upperCount)),
      (ofSignedRatio_le_iff _ _).mp (le_trans backward (natural_mono _ _ lowerCount))⟩

/-- Signed multiplication with a fixed supplied uniform approximation bound.
Unlike a bound computed from each factor presentation, this constant can be
shared by an entire path and used in a uniform composition modulus. -/
theorem within_mul_right_uniform {error : QProb} {x y factor : ConstructiveReal} (count : Nat)
    (close : Within error x y)
    (bounded : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (factor.rationalApproximation.value precision).magnitude (QProb.ofNat count)) :
    Within (QProb.mul error (QProb.ofNat count)) (mul x factor) (mul y factor) := by
  have estimate := mul_within_bounded error QProb.zero y.rationalApproximation.magnitudeBound count close
    (within_refl QProb.zero factor) y.rationalApproximation.magnitude_bounded bounded
  have collected : QProb.Equiv (QProb.add (QProb.mul error (QProb.ofNat count))
      (QProb.mul (QProb.ofNat y.rationalApproximation.magnitudeBound) QProb.zero)) (QProb.mul error (QProb.ofNat count)) :=
    QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) (by
      simp only [QProb.Equiv, QProb.mul, QProb.zero, Nat.mul_zero, Nat.zero_mul])) (QProb.add_zero _)
  exact within_mono estimate (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal
