import Thesis.Probability.EntropySmallMass
import Thesis.Probability.ExactLogRational

namespace Thesis.Examples.EntropySmallMass
open Probability

example : ExactLog.LE (ExactLog.log ⟨1024, 1023, by decide, by decide⟩)
    (ExactLog.ofSignedRatio ⟨1, 512, by decide⟩) :=
  log_inverse_complement_bound 1024 512 (by decide) (by decide) (by decide)

example : ExactLog.LE (ExactLog.scaleRatio ⟨1, 8, by decide⟩ (ExactLog.log ⟨3, 1, by decide, by decide⟩))
    (ExactLog.scaleRatio ⟨1, 4, by decide⟩ (ExactLog.log ⟨3, 1, by decide, by decide⟩)) :=
  ExactLog.scaleRatio_weight_mono (by decide) _ (by decide)

end Thesis.Examples.EntropySmallMass
