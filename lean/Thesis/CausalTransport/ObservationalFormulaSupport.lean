import Thesis.Causality.ProbabilityStatus
import Thesis.Probability.FiniteRecordSupport
import Thesis.CausalTransport.ObservationalFormulaDiagnostics

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Exact applicability from observational support patterns

The current probability-expression language is nonnegative. Its additions,
products, positive-denominator divisions and guarded weighted branches have
an exact three-state abstraction. Kernel leaves can obtain their state by
testing which complete observed assignments have positive singleton mass.
Numerical probabilities are not required to decide this state.

This module connects those two finite computations to the existing actual
observational evaluator. It includes every current term constructor and both
current guards. In particular, a probability-one action guard means that no
supported assignment violates the requested action. It does not require the
requested complete assignment itself to have positive mass.

These are applicability and finite-catalogue facts. They do not certify an
arbitrary input formula, enumerate all valid derivations, prove support of an
original conditional causal target, or decide fixed-law identifiability.
Hypothetical Boolean patterns may also be impossible under the causal graph;
the exactness theorem applies when the pattern comes from an actual record.
-/

namespace ProbabilityTerm

/-- Boolean union of supported assignment cells, without their masses. -/
def eventStatus (pattern : S.Assignment → Bool) (event : Event S.Assignment) : ProbabilityResult.Status :=
  if FiniteProbRecord.eventSupported S.assignmentEnumeration pattern event then .positive else .zero

theorem eventStatus_record (record : FiniteProbRecord S.Assignment) (event : Event S.Assignment) :
    eventStatus record.support event = ProbabilityResult.valueStatus (record.probVal event) := by
  unfold eventStatus
  rw [FiniteProbRecord.eventSupported_eq record _ S.assignmentEnumeration_complete]
  by_cases zero : FiniteProbRecord.eventMass record.atoms event = 0
  · simp [FiniteProbRecord.EventPositive, zero, ProbabilityResult.valueStatus, FiniteProbRecord.probVal]
  · have positive := Nat.pos_of_ne_zero zero
    simp [FiniteProbRecord.EventPositive, positive, zero, ProbabilityResult.valueStatus, FiniteProbRecord.probVal]

/-- Run the full partial-expression support semantics from singleton
positivity alone. Actionful leaves remain rejected, exactly as before. -/
def supportStatus (pattern : S.Assignment → Bool) : ProbabilityTerm S → S.Assignment → ProbabilityResult.Status
  | .zero, _ => .zero
  | .kernel kernel, reference =>
      if kernel.hasAction then .undefined else
        ProbabilityResult.Status.divide
          (eventStatus pattern (kernel.numeratorEvent reference))
          (eventStatus pattern (kernel.conditionEvent reference))
  | .marginalize nodes inner, reference =>
      ProbabilityResult.Status.sum ((marginalAssignments S nodes reference).map
        (fun variant => inner.supportStatus pattern variant))
  | .evaluateAt fixed inner, _ => inner.supportStatus pattern fixed
  | .add left right, reference => ProbabilityResult.Status.add
      (left.supportStatus pattern reference) (right.supportStatus pattern reference)
  | .multiply left right, reference => ProbabilityResult.Status.multiply
      (left.supportStatus pattern reference) (right.supportStatus pattern reference)
  | .weightedMultiply weight factor, reference => ProbabilityResult.Status.weightedMultiply
      (weight.supportStatus pattern reference) (factor.supportStatus pattern reference)
  | .divide numerator denominator, reference => ProbabilityResult.Status.divide
      (numerator.supportStatus pattern reference) (denominator.supportStatus pattern reference)

/-- Exact, not merely sufficient, abstract evaluation. A defined zero and
an undefined expression always remain different states. -/
theorem supportStatus_exact (term : ProbabilityTerm S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) :
    term.supportStatus record.support reference = ProbabilityResult.status (term.observationalDenote record reference) := by
  induction term generalizing reference with
  | zero => rfl
  | kernel kernel =>
      cases active : kernel.hasAction with
      | true => simp only [supportStatus, observationalDenote, active, if_true, ProbabilityResult.status]
      | false =>
          simp only [supportStatus, observationalDenote, active, Bool.false_eq_true, if_false,
            ProbabilityResult.status_divide, ProbabilityResult.status, eventStatus_record]
  | marginalize nodes inner ih =>
      simp only [supportStatus, observationalDenote, ProbabilityResult.status_sum, List.map_map]
      apply congrArg ProbabilityResult.Status.sum
      apply List.map_congr_left
      intro variant _listed
      exact ih variant
  | evaluateAt fixed inner ih => exact ih fixed
  | add left right leftIH rightIH =>
      simp only [supportStatus, observationalDenote, ProbabilityResult.status_add, leftIH, rightIH]
  | multiply left right leftIH rightIH =>
      simp only [supportStatus, observationalDenote, ProbabilityResult.status_multiply, leftIH, rightIH]
  | weightedMultiply weight factor weightIH factorIH =>
      simp only [supportStatus, observationalDenote, ProbabilityResult.status_weightedMultiply, weightIH, factorIH]
  | divide numerator denominator numeratorIH denominatorIH =>
      simp only [supportStatus, observationalDenote, ProbabilityResult.status_divide, numeratorIH, denominatorIH]

/-- Nonzero rational masses may change arbitrarily while retaining support.
Only the returned status is invariant, not the numerical formula value. -/
theorem status_eq_of_support_eq (term : ProbabilityTerm S) {left right : FiniteProbRecord S.Assignment}
    (same : left.support = right.support) (reference : S.Assignment) :
    ProbabilityResult.status (term.observationalDenote left reference) =
      ProbabilityResult.status (term.observationalDenote right reference) := by
  rw [← supportStatus_exact, ← supportStatus_exact, same]

end ProbabilityTerm

namespace ObservationalFormulaGuard

/-- Probability one is the absence of positive support in the complement,
not an equality test on a hypothetical numerical probability. -/
def checkSupport (guard : ObservationalFormulaGuard S) (pattern : S.Assignment → Bool)
    (reference : S.Assignment) : Bool :=
  match guard with
  | .always => true
  | .actionOne action =>
      !(FiniteProbRecord.eventSupported S.assignmentEnumeration pattern
        (fun sample => !(Kernel.agreesOn action reference sample)))

theorem checkSupport_exact (guard : ObservationalFormulaGuard S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) : guard.checkSupport record.support reference = guard.check record reference := by
  cases guard with
  | always => rfl
  | actionOne action =>
      apply Bool.eq_iff_iff.mpr
      rw [check_actionOne_iff, FiniteProbRecord.probVal_one_iff_complement_not_positive]
      simp [checkSupport, FiniteProbRecord.eventSupported_eq record _ S.assignmentEnumeration_complete]

end ObservationalFormulaGuard

namespace ObservationalFormulaPlan

def availableOnSupport (plan : ObservationalFormulaPlan S) (pattern : S.Assignment → Bool)
    (reference : S.Assignment) : Bool :=
  plan.guard.checkSupport pattern reference && (plan.formula.supportStatus pattern reference).isDefined

theorem availableOnSupport_exact (plan : ObservationalFormulaPlan S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) : plan.availableOnSupport record.support reference = plan.available record reference := by
  simp only [availableOnSupport, available, ObservationalFormulaGuard.checkSupport_exact,
    ProbabilityTerm.supportStatus_exact, ProbabilityResult.status_isDefined]

/-- All current guards and all printed support requirements are invariant
under support-preserving numerical reweighting. Certification remains a
separate prerequisite for interpreting any available plan causally. -/
theorem available_eq_of_support_eq (plan : ObservationalFormulaPlan S)
    {left right : FiniteProbRecord S.Assignment} (same : left.support = right.support) (reference : S.Assignment) :
    plan.available left reference = plan.available right reference := by
  rw [← availableOnSupport_exact, ← availableOnSupport_exact, same]

/-- Coverage by a *supplied* finite list can be tested without numeric
weights. No claim about candidates absent from that list is encoded here. -/
def coversSupport (plans : List (ObservationalFormulaPlan S)) (pattern : S.Assignment → Bool)
    (reference : S.Assignment) : Bool := plans.any (fun plan => plan.availableOnSupport pattern reference)

theorem coversSupport_exact (plans : List (ObservationalFormulaPlan S)) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) :
    coversSupport plans record.support reference = plans.any (fun plan => plan.available record reference) := by
  apply List.any_congr
  intro plan _listed
  exact availableOnSupport_exact plan record reference

end ObservationalFormulaPlan
end Thesis.Causality
