import Thesis.Probability.ConstructiveRealCauchy
import Thesis.Probability.ConstructiveRealRing

namespace Thesis.Probability.ConstructiveReal

/-- Negation preserves a certified rational distance bound. -/
theorem within_neg {error : QProb} {x y : ConstructiveReal} (close : Within error x y) : Within error (neg x) (neg y) := by
  let e := ofSignedRatio error.toSignedRatio
  have cancel (z : ConstructiveReal) : Equiv (add (neg (add z e)) e) (neg z) :=
    equiv_trans (add_congr (neg_add z e) (equiv_refl _))
      (equiv_trans (add_assoc _ _ _) (equiv_trans
        (add_congr (equiv_refl _) (equiv_trans (add_comm _ _) (add_neg e))) (add_zero _)))
  constructor
  · exact (le_congr (cancel x) (equiv_refl _)).mp
      (add_le_add ((neg_le_neg_iff _ _).mpr close.2) (le_refl e))
  · exact (le_congr (cancel y) (equiv_refl _)).mp
      (add_le_add ((neg_le_neg_iff _ _).mpr close.1) (le_refl e))

theorem ofSignedRatio_sub (a b : SignedRatio) :
    Equiv (sub (ofSignedRatio a) (ofSignedRatio b)) (ofSignedRatio (SignedRatio.sub a b)) :=
  equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg b))) (ofSignedRatio_add _ _)

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- Pointwise negation retains the original effective modulus. -/
def neg (sequence : RealCauchySequence) : RealCauchySequence where
  value n := ConstructiveReal.neg (sequence.value n)
  modulus := sequence.modulus
  cauchy precision n m left right := within_neg (sequence.cauchy precision n m left right)

theorem neg_limit (sequence : RealCauchySequence) : Equiv sequence.neg.limit (ConstructiveReal.neg sequence.limit) := by
  apply limit_unique _ _ (fun precision => sequence.modulus precision.half.half)
  intro precision n later
  exact within_neg (sequence.tail_within precision n later)

def sub (first second : RealCauchySequence) : RealCauchySequence := first.add second.neg

theorem sub_limit (first second : RealCauchySequence) :
    Equiv (first.sub second).limit (ConstructiveReal.sub first.limit second.limit) :=
  equiv_trans (first.add_limit second.neg) (add_congr (equiv_refl _) second.neg_limit)

end Thesis.Probability.RealCauchySequence
