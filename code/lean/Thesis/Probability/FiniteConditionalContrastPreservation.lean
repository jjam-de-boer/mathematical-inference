import Thesis.Probability.FiniteConditionalContrast

namespace Thesis.Probability.FiniteProbRecord

/-!
# Conditional-contrast vanishing is preserved by event probabilities

Two records may have different carriers, denominators, duplicate labels and
zero occurrences. Agreement of their evidence and joint-event probabilities
still preserves whether a proposed conditional contrast has mean zero.

At positive evidence, compare the actual conditionals through the existing
division-congruence theorem. At null evidence, both contrasts vanish without
forming either conditional. The only support test is decidable natural event
mass positivity. This theorem preserves vanishing, rather than asserting an
identity of the records' raw signed sums or their fraction presentations.
-/

theorem conditionalContrast_mean_zero_iff_of_probVal
    (left : FiniteProbRecord Ω) (right : FiniteProbRecord X)
    (leftEvidence leftEvent : Event Ω) (rightEvidence rightEvent : Event X) (value : QProb)
    (sameEvidence : QProb.Equiv (left.probVal leftEvidence) (right.probVal rightEvidence))
    (sameJoint : QProb.Equiv (left.probVal (fun sample => leftEvidence sample && leftEvent sample))
      (right.probVal (fun sample => rightEvidence sample && rightEvent sample))) :
    SignedRatio.Equiv
        (left.rationalMean (fun sample => ⟨conditionalContrast leftEvidence leftEvent value sample, 1, Nat.zero_lt_one⟩))
        SignedRatio.zero ↔
      SignedRatio.Equiv
        (right.rationalMean (fun sample => ⟨conditionalContrast rightEvidence rightEvent value sample, 1, Nat.zero_lt_one⟩))
        SignedRatio.zero := by
  by_cases supported : left.EventPositive leftEvidence
  · have rightSupported : right.EventPositive rightEvidence := (QProb.equiv_num_pos_iff sameEvidence).mp supported
    have conditionals := QProb.equiv_trans (left.conditionOn_probVal leftEvidence leftEvent supported)
      (QProb.equiv_trans (QProb.div_congr sameJoint sameEvidence supported rightSupported)
        (QProb.equiv_symm (right.conditionOn_probVal rightEvidence rightEvent rightSupported)))
    rw [left.rationalMean_conditionalContrast_zero_iff leftEvidence leftEvent value supported,
      right.rationalMean_conditionalContrast_zero_iff rightEvidence rightEvent value rightSupported]
    exact ⟨fun agrees => QProb.equiv_trans (QProb.equiv_symm conditionals) agrees,
      fun agrees => QProb.equiv_trans conditionals agrees⟩
  · have rightUnsupported : ¬ right.EventPositive rightEvidence :=
      fun positive => supported ((QProb.equiv_num_pos_iff sameEvidence).mpr positive)
    exact ⟨fun _ => right.rationalMean_conditionalContrast_zero_of_not_positive rightEvidence rightEvent value rightUnsupported,
      fun _ => left.rationalMean_conditionalContrast_zero_of_not_positive leftEvidence leftEvent value supported⟩

end Thesis.Probability.FiniteProbRecord
