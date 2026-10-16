import Thesis.Probability.Distros.FinitePresentation
import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.Distros.MultivariateHypergeometric

namespace Thesis.Examples.FiniteRecordPresentation

open Probability Probability.Distros

/-!
# Sampling codes, duplicate labels and null observed values

The occurrence presentation deliberately keeps two atoms labelled `7`, one
of zero weight. The domain presentation instead has one code per permitted
value and retains the entirely absent value `8`. These exact small fixtures
guard against conflating sampling indices with observed values.

Symbolic applications to the newer list-valued urn and hypergeometric laws
check their actual finite adapters without enumerating large denominators,
asserting that `List Nat` itself is finite, or weakening support conditions.
-/

def repeated : Distro Nat where
  record := ⟨[(7, 2), (7, 0), (9, 1)], 3, by decide, rfl⟩

theorem occurrence_count : repeated.finitePresentation.card = 3 := rfl

theorem repeated_record_recovered :
    repeated.finitePresentation.record.map repeated.finitePresentation.decode = repeated.record :=
  repeated.finitePresentation_recovered

def declared : List Nat := [7, 8, 9]

private theorem covered : forall atom, atom ∈ repeated.record.atoms → atom.1 ∈ declared := by
  intro atom member
  simp only [repeated, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals decide +kernel

def finiteDomain := repeated.finiteDomainPresentation declared covered

/-- A permitted but unobserved value remains available as a variable value,
not discarded by a positive-support-only encoding. -/
theorem absent_value_retained : ∃ code, finiteDomain.decode code = 8 :=
  repeated.finiteDomainPresentation_covers declared covered 8 (by decide +kernel)

theorem absent_value_probability :
    QProb.Equiv (finiteDomain.record.probVal (fun code => decide (finiteDomain.decode code = 8))) QProb.zero :=
  QProb.equiv_trans (finiteDomain.probVal (fun value => decide (value = 8))) (by decide +kernel)

theorem supported_condition_preserved :
    QProb.Equiv
      ((repeated.finitePresentation.record.conditionOn
        (fun code => decide (repeated.finitePresentation.decode code = 7))
        ((repeated.finitePresentation.eventPositive_iff (fun value => decide (value = 7))).mpr
          (by decide +kernel))).probVal (fun code => decide (repeated.finitePresentation.decode code = 9)))
      ((repeated.record.conditionOn (fun value => decide (value = 7)) (by decide +kernel)).probVal
        (fun value => decide (value = 9))) :=
  repeated.finitePresentation.conditionOn_probVal
    (fun value => decide (value = 7)) (fun value => decide (value = 9)) (by decide +kernel)

/-- Arbitrary rational urn parameters retain the complete ordered-path law
after finite-code sampling, including categories of initial weight zero. -/
theorem rational_urn_events (trials : Nat) (parameters : List QProb)
    (positive : 0 < (QProb.listSum parameters).num) (event : Event (List Nat)) :
    let distro := rationalPolyaDistro trials parameters positive
    QProb.Equiv (distro.finitePresentation.record.probVal
      (fun code => event (distro.finitePresentation.decode code))) (distro.record.probVal event) :=
  (rationalPolyaDistro trials parameters positive).finitePresentation.probVal event

/-- The finite-population law is encoded with its actual combinatorial
weights, not by assuming a finite ambient list type or expanding its denominator. -/
theorem hypergeometric_events (draws : Nat) (stocks : List Nat)
    (positive : 0 < Probability.Combinatorics.binom stocks.sum draws) (event : Event (List Nat)) :
    let distro := multivariateHypergeometricDistro draws stocks positive
    QProb.Equiv (distro.finitePresentation.record.probVal
      (fun code => event (distro.finitePresentation.decode code))) (distro.record.probVal event) :=
  (multivariateHypergeometricDistro draws stocks positive).finitePresentation.probVal event

end Thesis.Examples.FiniteRecordPresentation
