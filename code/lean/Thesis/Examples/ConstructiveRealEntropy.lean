import Thesis.Probability.ConstructiveRealEntropySum
import Thesis.Probability.ConstructiveRealRelativeEntropy

namespace Thesis.Examples.ConstructiveRealEntropy
open Probability ConstructiveReal

/-- A fair binary law with an explicit noncanonical zero and two different
unreduced representations of one half. The continuous sum is exactly one bit. -/
private def fairWithZero : List {q : QProb // q.num ≤ q.den} :=
  [⟨⟨2, 4, by decide⟩, by decide⟩, ⟨⟨0, 7, by decide⟩, by decide⟩, ⟨⟨3, 6, by decide⟩, by decide⟩]

private theorem fairWithZero_entropy :
    Equiv (realEntropySum (fairWithZero.map UnitIntervalValue.ofBoundedQProb)) one :=
  equiv_trans (realEntropySum_ofQProb fairWithZero)
    (equiv_trans (ExactLog.interpret_congr (by decide +kernel :
      ExactLog.Equiv (Probability.entropySum (fairWithZero.map Subtype.val)) (ExactLog.ofSignedRatio SignedRatio.one)))
      (ExactLog.interpret_ofSignedRatio SignedRatio.one))

example : Equiv (mul (realEntropySum (fairWithZero.map UnitIntervalValue.ofBoundedQProb)) lnTwo) lnTwo :=
  equiv_trans (mul_congr fairWithZero_entropy (equiv_refl lnTwo)) (one_mul lnTwo)

/-- An entropy error bound at zero needs no decision whether the nearby
analytic input is zero or positive. -/
example (x : UnitIntervalValue) (precision : PositiveRatio)
    (close : Within (entropyInputPrecision precision).half.toQProb x.value zero) :
    Within precision.toQProb x.entropy zero := by
  have zeroBound : LE zero one := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  exact (within_congr (equiv_refl _) (realEntropyTerm_zero (le_refl zero) zeroBound)).mp
    (realEntropyTerm_within x.value zero x.nonnegative (le_refl zero) x.bounded zeroBound precision close)

/-- Zero insertion also works for a real presentation merely equivalent to
zero, rather than definitionally the canonical zero. -/
example (mass : UnitIntervalValue) (vanished : Equiv mass.value zero) (rest : List UnitIntervalValue) :
    Equiv (realEntropySum (mass :: rest)) (realEntropySum rest) := realEntropySum_cons_zero mass vanished rest

private def nullMass : QProb := ⟨0, 9, by decide⟩
private def referenceMass : QProb := ⟨2, 3, by decide⟩
private def nullCoordinate : UnitIntervalValue := .ofQProb nullMass (by decide)
private def referenceLower : PositiveRatio := ⟨1, 9, by decide, by decide⟩
private theorem referenceLower_bound : LE (ofSignedRatio referenceLower.toSignedRatio) (ofSignedRatio referenceMass.toSignedRatio) :=
  (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)

/-- A noncanonical zero observation contributes zero against a nonuniform
reference with a separately supplied, deliberately smaller positive bound. -/
example : Equiv (nullCoordinate.value.realRelativeEntropyTerm nullCoordinate.nonnegative nullCoordinate.bounded
    (ofSignedRatio referenceMass.toSignedRatio) referenceLower referenceLower_bound) zero :=
  equiv_trans (realRelativeEntropyTerm_ofQProb nullMass referenceMass nullCoordinate.nonnegative nullCoordinate.bounded
    (by decide) referenceLower referenceLower_bound)
    (equiv_trans (ExactLog.interpret_congr (by decide +kernel :
      ExactLog.Equiv (Probability.relativeEntropyTerm nullMass referenceMass (by decide)) ExactLog.zero))
      (ExactLog.interpret_ofSignedRatio SignedRatio.zero))

private def halfMass : QProb := ⟨2, 4, by decide⟩
private def quarterMass : QProb := ⟨1, 4, by decide⟩
private def halfCoordinate : UnitIntervalValue := .ofQProb halfMass (by decide)
private def eighth : PositiveRatio := ⟨1, 8, by decide, by decide⟩
private theorem eighth_quarter : LE (ofSignedRatio eighth.toSignedRatio) (ofSignedRatio quarterMass.toSignedRatio) :=
  (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)

/-- The KL contribution (1/2) log₂((1/2)/(1/4)) is exactly one half. -/
example : Equiv (halfCoordinate.value.realRelativeEntropyTerm halfCoordinate.nonnegative halfCoordinate.bounded
    (ofSignedRatio quarterMass.toSignedRatio) eighth eighth_quarter) (ofSignedRatio halfMass.toSignedRatio) :=
  equiv_trans (realRelativeEntropyTerm_ofQProb halfMass quarterMass halfCoordinate.nonnegative halfCoordinate.bounded
    (by decide) eighth eighth_quarter)
    (equiv_trans (ExactLog.interpret_congr (by decide +kernel :
      ExactLog.Equiv (Probability.relativeEntropyTerm halfMass quarterMass (by decide)) (ExactLog.ofSignedRatio halfMass.toSignedRatio)))
      (ExactLog.interpret_ofSignedRatio halfMass.toSignedRatio))

end Thesis.Examples.ConstructiveRealEntropy
