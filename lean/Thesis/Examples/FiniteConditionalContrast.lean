import Thesis.Probability.FiniteConditionalContrast
import Thesis.Probability.Distros.PartialMomentBounds

namespace Thesis.Examples.FiniteConditionalContrast

open Probability Probability.FiniteProbRecord Probability.Distros

/-!
# Conditional contrasts on unreduced records and null evidence

The same record retains two occurrences of label `1`, an unreduced common
denominator, and a zero-weight occurrence of label `2`. The first comparison
uses an unreduced proposed value. The second keeps a nonzero response at a
null label while proving only its mean vanishes. The third uses an incorrect
proposed value and recovers positive evidence from its nonzero contrast.

The symbolic application also checks the optimizer's existing integer-response
interface. Only the small finite record calculations use kernel decision.
No optimizer is executed and no conditional is formed at null evidence.
-/

/-- The foundational record theorem applies directly to the existing
integer-response expectation, without changing either probability interface. -/
example (law : Distro Ω) (condition outcome : Event Ω) (value : QProb)
    (positive : law.record.EventPositive condition) :
    SignedRatio.Equiv
      (law.rationalExpectation (integerResponse (conditionalContrast condition outcome value)))
      SignedRatio.zero ↔
      QProb.Equiv ((law.record.conditionOn condition positive).probVal outcome) value :=
  law.record.rationalMean_conditionalContrast_zero_iff condition outcome value positive

def record : FiniteProbRecord (Fin 3) :=
  ⟨[(0, 4), (1, 2), (1, 2), (2, 0)], 8, by decide, rfl⟩

def evidence : Event (Fin 3) := fun value => decide (value ≠ 0)
def event : Event (Fin 3) := fun value => decide (value = 1)
def proposed : QProb := ⟨2, 2, by decide⟩

def contrastMean (condition outcome : Event (Fin 3)) (value : QProb) : SignedRatio :=
  record.rationalMean (fun label => ⟨conditionalContrast condition outcome value label, 1, Nat.zero_lt_one⟩)

theorem evidence_positive : record.EventPositive evidence := by decide +kernel

/-- The zero-weight label is deliberately retained even though its response
is nonzero. Agreement concerns an integral, not every declared label. -/
theorem retained_zero_label_contrast : conditionalContrast evidence event proposed 2 = -2 := by decide +kernel

theorem supported_conditional_agrees :
    QProb.Equiv ((record.conditionOn evidence evidence_positive).probVal event) proposed :=
  (record.signedMass_conditionalContrast_zero_iff evidence event proposed evidence_positive).mp
    (by decide +kernel)

theorem supported_mean_zero : SignedRatio.Equiv (contrastMean evidence event proposed) SignedRatio.zero :=
  (record.rationalMean_conditionalContrast_zero_iff evidence event proposed evidence_positive).mpr
    supported_conditional_agrees

def nullEvidence : Event (Fin 3) := fun value => decide (value = 2)
def nullProposed : QProb := ⟨3, 7, by decide⟩

theorem evidence_null : ¬ record.EventPositive nullEvidence := by decide +kernel

/-- This value is a response at the retained label, not a conditional
probability at the null event. -/
theorem null_label_contrast : conditionalContrast nullEvidence topEvent nullProposed 2 = 4 := by decide +kernel

theorem null_mean_zero : SignedRatio.Equiv (contrastMean nullEvidence topEvent nullProposed) SignedRatio.zero :=
  record.rationalMean_conditionalContrast_zero_of_not_positive nullEvidence topEvent nullProposed evidence_null

def incorrect : QProb := ⟨1, 3, by decide⟩

theorem incorrect_signedMass : record.signedMass (conditionalContrast topEvent event incorrect) = 4 :=
  by decide +kernel

theorem incorrect_mean_nonzero : ¬ SignedRatio.Equiv (contrastMean topEvent event incorrect) SignedRatio.zero := by
  intro zero
  have mean := record.rationalMean_conditionalContrast topEvent event incorrect
  have massZero := (SignedRatio.equiv_zero_iff _).mp
    (SignedRatio.equiv_trans (SignedRatio.equiv_symm mean) zero)
  rw [incorrect_signedMass] at massZero
  omega

/-- The nonzero contrast supplies support without a conditional premise. -/
theorem support_from_nonzero_contrast : record.EventPositive topEvent :=
  record.eventPositive_of_conditionalContrast_mean_ne_zero topEvent event incorrect incorrect_mean_nonzero

end Thesis.Examples.FiniteConditionalContrast
