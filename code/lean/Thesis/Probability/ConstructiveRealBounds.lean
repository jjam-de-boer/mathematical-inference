import Thesis.Probability.ConstructiveRealDistance

namespace Thesis.Probability.ConstructiveReal

/-- A positive natural upper bound computed from a single rational enclosure. -/
def naturalUpper (x : ConstructiveReal) : Nat := (x.enclose PositiveRatio.one).upper.num.natAbs + 1

theorem naturalUpper_pos (x : ConstructiveReal) : 0 < x.naturalUpper := Nat.zero_lt_succ _

theorem le_naturalUpper (x : ConstructiveReal) : LE x (ofSignedRatio (QProb.ofNat x.naturalUpper).toSignedRatio) := by
  let upper := (x.enclose PositiveRatio.one).upper
  have size : QProb.LE upper.magnitude (QProb.ofNat x.naturalUpper) := by
    change upper.num.natAbs * 1 ≤ (upper.num.natAbs + 1) * upper.den
    have increased := Nat.le_mul_of_pos_right (upper.num.natAbs + 1) upper.den_pos
    omega
  exact le_trans (x.upper_bound PositiveRatio.one)
    ((ofSignedRatio_le_iff _ _).mpr (SignedRatio.le_trans (SignedRatio.le_magnitude upper)
      ((SignedRatio.toSignedRatio_le_iff _ _).mpr size)))

end Thesis.Probability.ConstructiveReal
