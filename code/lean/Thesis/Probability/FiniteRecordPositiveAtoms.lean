import Thesis.Probability.FiniteSignedMass
import Thesis.Probability.FiniteSupportedSum

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Remove zero atoms without changing a finite probability record's law

Compression operates on the number of positive atoms, not on an artificial
assumption that every supplied atom was positive.  This explicit preprocessing
retains repeated labels, their order and all positive weights, removes only
zero occurrences, and keeps the original positive denominator.

Every event probability and every integer-valued moment is preserved.  The
proofs inspect Boolean filters and natural weights directly; they do not use
classical empty-filter equivalences or choose a supported representative.
-/

def positiveAtoms (atoms : List (Ω × Nat)) : List (Ω × Nat) :=
  atoms.filter (fun atom => decide (0 < atom.2))

theorem positiveAtoms_totalMass (atoms : List (Ω × Nat)) : totalMass (positiveAtoms atoms) = totalMass atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      by_cases positive : 0 < weight
      · have accepted := decide_eq_true positive
        simpa only [positiveAtoms, List.filter_cons, accepted, if_true, totalMass] using
          congrArg (fun mass => weight + mass) inductionHypothesis
      · have zero : weight = 0 := by omega
        subst weight
        have rejected : decide (0 < (0 : Nat)) = false := rfl
        simpa only [positiveAtoms, List.filter_cons, rejected, Bool.false_eq_true, if_false,
          totalMass, Nat.zero_add] using inductionHypothesis

theorem positiveAtoms_eventMass (atoms : List (Ω × Nat)) (event : Event Ω) :
    eventMass (positiveAtoms atoms) event = eventMass atoms event := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp only [positiveAtoms] at inductionHypothesis
      rcases atom with ⟨value, weight⟩
      by_cases positive : 0 < weight
      · have accepted := decide_eq_true positive
        cases selected : event value <;>
          simp only [positiveAtoms, List.filter_cons, accepted, if_true, eventMass,
            selected, Bool.false_eq_true, if_false, inductionHypothesis]
      · have zero : weight = 0 := by omega
        subst weight
        have rejected : decide (0 < (0 : Nat)) = false := rfl
        cases selected : event value <;>
          simpa only [positiveAtoms, List.filter_cons, rejected, Bool.false_eq_true, if_false,
            eventMass, selected, if_true, Nat.zero_add] using inductionHypothesis

theorem positiveAtoms_signedAtomMass (atoms : List (Ω × Nat)) (integrand : Ω → Int) :
    signedAtomMass (positiveAtoms atoms) integrand = signedAtomMass atoms integrand := by
  unfold signedAtomMass positiveAtoms
  apply Eq.symm
  apply FiniteSupportedSum.sum_eq_filter_of_zero
  intro atom _ absent
  have notPositive : ¬ 0 < atom.2 := of_decide_eq_false absent
  have zero : atom.2 = 0 := by omega
  rw [zero, Int.natCast_zero, Int.zero_mul]

theorem positiveAtoms_positive (atoms : List (Ω × Nat)) (atom : Ω × Nat)
    (listed : atom ∈ positiveAtoms atoms) : 0 < atom.2 :=
  of_decide_eq_true (List.mem_filter.mp listed).2

def trimZeros (record : FiniteProbRecord Ω) : FiniteProbRecord Ω where
  atoms := positiveAtoms record.atoms
  den := record.den
  den_pos := record.den_pos
  total_mass := (positiveAtoms_totalMass record.atoms).trans record.total_mass

/-- Equality is literal because even the original denominator is retained.
No new conditional or completion at a null event is introduced. -/
theorem trimZeros_probVal (record : FiniteProbRecord Ω) (event : Event Ω) :
    record.trimZeros.probVal event = record.probVal event := by
  simp only [probVal, trimZeros, positiveAtoms_eventMass]

theorem trimZeros_signedMass (record : FiniteProbRecord Ω) (integrand : Ω → Int) :
    record.trimZeros.signedMass integrand = record.signedMass integrand := by
  exact positiveAtoms_signedAtomMass record.atoms integrand

theorem trimZeros_positive (record : FiniteProbRecord Ω) (atom : Ω × Nat)
    (listed : atom ∈ record.trimZeros.atoms) : 0 < atom.2 := positiveAtoms_positive record.atoms atom listed

end FiniteProbRecord
end Probability
end Thesis
