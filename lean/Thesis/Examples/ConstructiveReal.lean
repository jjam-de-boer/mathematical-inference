import Thesis.Probability.EntropyInterpretation

namespace Thesis.Examples.ConstructiveReal
open Probability

private def precision : PositiveRatio := ⟨1, 100, by decide, by decide⟩
private def three : ExactLog := ExactLog.log ⟨3, 1, by decide, by decide⟩

/-- Enclosures are actually computed at the requested rational precision. -/
example : SignedRatio.LE ⟨157, 100, by decide⟩ (three.interpret.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (three.interpret.enclose precision).upper ⟨160, 100, by decide⟩ := by decide +kernel
example : SignedRatio.LE (three.interpret.enclose precision).upper
    (SignedRatio.add (three.interpret.enclose precision).lower precision.toSignedRatio) :=
  (three.interpret.enclose precision).width

/-- A rational-bit certificate transfers to the new real order. -/
example : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio ⟨158, 100, by decide⟩) three.interpret := by
  have exactBound : ExactLog.LE (ExactLog.ofSignedRatio ⟨158, 100, by decide⟩) three := by decide +kernel
  exact (ConstructiveReal.le_congr (ExactLog.interpret_ofSignedRatio _) (ConstructiveReal.equiv_refl _)).mp
    (ExactLog.interpret_mono exactBound)

example : ConstructiveReal.Equiv (ConstructiveReal.ofSignedRatio ⟨2, 4, by decide⟩)
    (ConstructiveReal.ofSignedRatio ⟨3, 6, by decide⟩) :=
  (ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)

/-- These algebraic laws hold for arbitrary coherent real presentations. -/
example (x y z : ConstructiveReal) :
    ConstructiveReal.Equiv (ConstructiveReal.add (ConstructiveReal.add x y) z)
      (ConstructiveReal.add x (ConstructiveReal.add y z)) := ConstructiveReal.add_assoc x y z
example (x : ConstructiveReal) : ConstructiveReal.Equiv (ConstructiveReal.sub x x) ConstructiveReal.zero :=
  ConstructiveReal.add_neg x
example (x y z : ConstructiveReal) :
    ConstructiveReal.LE (ConstructiveReal.add x z) (ConstructiveReal.add y z) ↔ ConstructiveReal.LE x y :=
  ConstructiveReal.add_le_add_right_iff x y z

example (x y : ExactLog) : ConstructiveReal.LE x.interpret y.interpret ↔ ExactLog.LE x y := ExactLog.interpret_le_iff x y
example (x y : ExactLog) : ConstructiveReal.Equiv x.interpret y.interpret ↔ ExactLog.Equiv x y := ExactLog.interpret_equiv_iff x y
example (weight : QProb) (x : ExactLog) :
    ConstructiveReal.Equiv (ExactLog.scaleRatio weight x).interpret
      (ConstructiveReal.scaleRatio weight x.interpret) := ExactLog.interpret_scaleRatio weight x

/-- The null convention survives the interpretation without evaluating log 0. -/
example : ConstructiveReal.entropyTerm (⟨0, 19, by decide⟩ : QProb) = ConstructiveReal.zero :=
  ConstructiveReal.entropyTerm_zero _ rfl
example : ConstructiveReal.Equiv (entropySum [⟨2, 3, by decide⟩, QProb.zero, ⟨1, 3, by decide⟩]).interpret
    (ConstructiveReal.entropySum [⟨2, 3, by decide⟩, QProb.zero, ⟨1, 3, by decide⟩]) := entropySum_interpret _
example (p r : QProb) (positive : 0 < r.num) :
    ConstructiveReal.Equiv (relativeEntropyTerm p r positive).interpret (ConstructiveReal.relativeEntropyTerm p r positive) :=
  relativeEntropyTerm_interpret p r positive

end Thesis.Examples.ConstructiveReal
