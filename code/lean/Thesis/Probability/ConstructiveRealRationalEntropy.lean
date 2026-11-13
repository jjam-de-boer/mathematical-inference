import Thesis.Probability.EntropyContinuity
import Thesis.Probability.EntropyRealProducts
import Thesis.Probability.ConstructiveRealLogarithm

namespace Thesis.Probability.ConstructiveReal

/-- The already implemented exact rational entropy contribution, interpreted
as an analytic value. Zero rational masses never evaluate a logarithm. -/
def rationalEntropyTerm (mass : QProb) : ConstructiveReal := (Thesis.Probability.entropyTerm mass).interpret

/-- A strictly positive input radius for the proved rational entropy modulus. -/
def entropyInputPrecision (precision : PositiveRatio) : PositiveRatio :=
  ⟨1, (entropyContinuityThreshold precision.toQProb).den, by decide, (entropyContinuityThreshold precision.toQProb).den_pos⟩

theorem rationalEntropyTerm_congr {p q : QProb} (same : QProb.Equiv p q) : Equiv (rationalEntropyTerm p) (rationalEntropyTerm q) :=
  ExactLog.interpret_congr (entropyTerm_congr same)

/-- Uniform rational continuity transfers the exact entropy bound to a
certified analytic distance bound, including either zero mass. -/
theorem rationalEntropyTerm_within (precision : PositiveRatio) (p q : QProb)
    (pBound : p.num ≤ p.den) (qBound : q.num ≤ q.den)
    (close : QProb.LE (SignedRatio.sub p.toSignedRatio q.toSignedRatio).magnitude (entropyInputPrecision precision).toQProb) :
    Within precision.toQProb (rationalEntropyTerm p) (rationalEntropyTerm q) := by
  have twoSided := (SignedRatio.magnitude_sub_le_iff _ _ _).mp close
  have left : QProb.LE p (QProb.add q (entropyContinuityThreshold precision.toQProb)) := by
    apply (SignedRatio.toSignedRatio_le_iff _ _).mp
    rw [QProb.toSignedRatio_add]
    exact twoSided.1
  have right : QProb.LE q (QProb.add p (entropyContinuityThreshold precision.toQProb)) := by
    apply (SignedRatio.toSignedRatio_le_iff _ _).mp
    rw [QProb.toSignedRatio_add]
    exact twoSided.2
  have estimate := entropyTerm_uniform_continuity precision.toQProb precision.num_pos p q pBound qBound left right
  have transfer (a b : QProb)
      (bounded : ExactLog.LE (Thesis.Probability.entropyTerm a)
        (ExactLog.add (Thesis.Probability.entropyTerm b) (ExactLog.ofSignedRatio precision.toSignedRatio))) :
      LE (rationalEntropyTerm a) (add (rationalEntropyTerm b) (ofSignedRatio precision.toSignedRatio)) :=
    (le_congr (equiv_refl _) (equiv_trans (ExactLog.interpret_add _ _)
      (add_congr (equiv_refl _) (ExactLog.interpret_ofSignedRatio _)))).mp (ExactLog.interpret_mono bounded)
  exact ⟨transfer p q estimate.1, transfer q p estimate.2⟩

/-- On positive rational inputs, the analytic contribution has the usual
product formula for any valid logarithm lower-bound witness. -/
theorem rationalEntropyTerm_formula (mass : QProb) (positive : 0 < mass.num) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) (ofSignedRatio mass.toSignedRatio)) :
    Equiv (rationalEntropyTerm mass)
      (neg (mul (ofSignedRatio mass.toSignedRatio) ((ofSignedRatio mass.toSignedRatio).positiveLog2 lower bounded))) :=
  equiv_trans (entropyTerm_interpret_mul mass positive)
    (neg_congr (mul_congr (equiv_refl _) (equiv_symm (positiveLog2_ofPositiveRatio ⟨mass.num, mass.den, positive, mass.den_pos⟩ lower bounded))))

end Thesis.Probability.ConstructiveReal
