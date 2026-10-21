import Thesis.Probability.EntropyTermBounds
import Thesis.Probability.ExactLogRational

namespace Thesis.Examples.EntropySmallMass
open Probability

example : ExactLog.LE (ExactLog.log ⟨1024, 1023, by decide, by decide⟩)
    (ExactLog.ofSignedRatio ⟨1, 512, by decide⟩) :=
  log_inverse_complement_bound 1024 512 (by decide) (by decide) (by decide)

example : ExactLog.LE (ExactLog.scaleRatio ⟨1, 8, by decide⟩ (ExactLog.log ⟨3, 1, by decide, by decide⟩))
    (ExactLog.scaleRatio ⟨1, 4, by decide⟩ (ExactLog.log ⟨3, 1, by decide, by decide⟩)) :=
  ExactLog.scaleRatio_weight_mono (by decide) _ (by decide)

/-- The dyadic boundary theorem applies to arbitrary rational masses,
not only probabilities whose denominator is a power of two. -/
example : ExactLog.LE (entropyTerm ⟨3, 10000000, by decide⟩)
    (ExactLog.ofSignedRatio ⟨1, 256, by decide⟩) :=
  entropyTerm_boundary_precision _ (by decide) 8 (by decide +kernel)

/-- Zero is covered by the same requested-error interface. -/
example : ExactLog.LE (entropyTerm QProb.zero)
    (ExactLog.ofSignedRatio (⟨1, 1000, by decide⟩ : QProb).toSignedRatio) :=
  entropyTerm_near_zero ⟨1, 1000, by decide⟩ (by decide) QProb.zero (by decide) (by decide +kernel)

example (tolerance : QProb) (positive : 0 < tolerance.num) (p : QProb)
    (bounded : p.num ≤ p.den) (small : QProb.LE p (entropyBoundaryThreshold tolerance)) :
    ExactLog.LE (entropyTerm p) (ExactLog.ofSignedRatio tolerance.toSignedRatio) :=
  entropyTerm_near_zero tolerance positive p bounded small

end Thesis.Examples.EntropySmallMass
