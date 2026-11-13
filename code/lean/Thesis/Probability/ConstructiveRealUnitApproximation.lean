import Thesis.Probability.ConstructiveRealOrderedRing
import Thesis.Probability.RationalApproximationSequence

namespace Thesis.Probability.ConstructiveReal

/-- A nonnegative rational approximation of a real, using only a finite
comparison of its rational endpoint with zero. -/
def unitCenter (x : ConstructiveReal) (precision : PositiveRatio) : QProb :=
  ⟨(x.nonnegativeCenter precision).num.toNat, (x.nonnegativeCenter precision).den, (x.nonnegativeCenter precision).den_pos⟩

theorem unitCenter_value (x : ConstructiveReal) (precision : PositiveRatio) :
    SignedRatio.Equiv (x.unitCenter precision).toSignedRatio (x.nonnegativeCenter precision) := by
  have positive := (SignedRatio.zero_le_iff_nonnegative _).mp (x.nonnegativeCenter_nonnegative precision)
  have recovered := Int.toNat_of_nonneg positive
  simp only [unitCenter, QProb.toSignedRatio, SignedRatio.Equiv, recovered]

theorem unitCenter_within (x : ConstructiveReal) (nonnegative : LE zero x) (precision : PositiveRatio) :
    Within precision.toQProb x (ofSignedRatio (x.unitCenter precision).toSignedRatio) :=
  (within_congr (equiv_refl x) ((ofSignedRatio_equiv_iff _ _).mpr (unitCenter_value x precision))).mpr
    (x.nonnegativeCenter_within nonnegative precision)

/-- Clamped lower endpoints remain lower bounds on a nonnegative real. -/
theorem unitCenter_le (x : ConstructiveReal) (nonnegative : LE zero x) (precision : PositiveRatio) :
    LE (ofSignedRatio (x.unitCenter precision).toSignedRatio) x := by
  apply (le_congr ((ofSignedRatio_equiv_iff _ _).mpr (unitCenter_value x precision)) (equiv_refl x)).mpr
  unfold nonnegativeCenter
  split
  · exact x.lower_bound precision
  · exact nonnegative

theorem unitCenter_bounded (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) (precision : PositiveRatio) :
    (x.unitCenter precision).num ≤ (x.unitCenter precision).den := by
  have compared := (SignedRatio.toSignedRatio_le_iff (x.unitCenter precision) QProb.one).mp
    ((ofSignedRatio_le_iff _ _).mp (show LE (ofSignedRatio (x.unitCenter precision).toSignedRatio)
      (ofSignedRatio QProb.one.toSignedRatio) from le_trans (x.unitCenter_le nonnegative precision) bounded))
  simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using compared

theorem unitCenter_ofQProb (mass : QProb) (precision : PositiveRatio) :
    (ofSignedRatio mass.toSignedRatio).unitCenter precision = mass := by
  have positive : SignedRatio.LE SignedRatio.zero mass.toSignedRatio :=
    (SignedRatio.zero_le_iff_nonnegative _).mpr (Int.natCast_nonneg mass.num)
  have center : (ofSignedRatio mass.toSignedRatio).nonnegativeCenter precision = mass.toSignedRatio := by
    change (if SignedRatio.LE SignedRatio.zero mass.toSignedRatio then mass.toSignedRatio else SignedRatio.zero) = mass.toSignedRatio
    exact if_pos positive
  have numerator := congrArg (fun value : SignedRatio => value.num.toNat) center
  have denominator := congrArg SignedRatio.den center
  have ext (a b : QProb) (sameNum : a.num = b.num) (sameDen : a.den = b.den) : a = b := by
    cases a
    cases b
    cases sameNum
    cases sameDen
    rfl
  exact ext _ mass numerator denominator

/-- A scalar unit-interval approximation sequence. Coordinatewise use does
not assert normalization or exact feasibility of any probability vector. -/
def unitSequence (x : ConstructiveReal) (nonnegative : LE zero x) : RealCauchySequence where
  value n := ofSignedRatio (x.unitCenter (PositiveRatio.unitPrecision n)).toSignedRatio
  modulus precision := precision.half.den
  cauchy precision n m left right := by
    have compared := within_triangle (within_symm (x.unitCenter_within nonnegative (PositiveRatio.unitPrecision n)))
      (x.unitCenter_within nonnegative (PositiveRatio.unitPrecision m))
    have smaller := QProb.add_le_add (PositiveRatio.unitPrecision_le precision.half n left) (PositiveRatio.unitPrecision_le precision.half m right)
    exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) precision.half_sum smaller)

theorem unitSequence_limit (x : ConstructiveReal) (nonnegative : LE zero x) : Equiv (x.unitSequence nonnegative).limit x := by
  apply RealCauchySequence.limit_unique _ _ (fun precision => precision.den)
  intro precision n later
  exact within_mono (within_symm (x.unitCenter_within nonnegative (PositiveRatio.unitPrecision n)))
    (PositiveRatio.unitPrecision_le precision n later)

end Thesis.Probability.ConstructiveReal
