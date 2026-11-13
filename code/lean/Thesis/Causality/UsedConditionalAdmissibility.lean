import Thesis.Causality.Admissibility
import Thesis.Causality.SupportAwareKernelAlgebra

namespace Thesis
namespace Causality

open Probability

/-!
# Explicit admissibility of every actually used conditional

The joint and conditional identification papers permit observed zeros but
require positive conditioners for every conditional that is actually used.
They explain that sums can be restricted to positive-probability events.
References: https://ftp.cs.ucla.edu/pub/stat_ser/r327.pdf, p. 2, and
https://ftp.cs.ucla.edu/pub/stat_ser/r329.pdf, p. 2.

This module makes that requirement precise for the existing finite expression
language, independently of any graph, engine trace, compiler `Data`, or
do-calculus derivation.  A kernel leaf tests its actual conditioner.  A
quotient tests its displayed denominator.  Strict sums inspect exactly their
listed variants; fixed evaluation uses its displayed assignment.  A guarded
product inspects its factor only at a positive defined weight.  In particular
an undefined weight is not zero, and a skipped null-weight factor is not given
an arbitrary conditional value.  Ordinary products remain strict.

The predicate contains primitive positivity tests and their syntactic demand
contexts, not a field assuming that the whole expression or derivation is
supported.  Structural recursion constructs a rational support witness from
these tests.  The converse checks that no stronger hidden support obligation
has been introduced.  For action-free syntax, observational agreement
preserves the predicate; causal conditioner support is not transferred by
that argument.

This specifies the *used-conditional* part of admissibility.  The separate
action tests and original intervened conditioner in `Admissibility` remain
separate conditions of an application.  This module alone neither selects
their quantification nor assembles a full identification completeness theorem.
-/

namespace ProbabilityResult

/-- A finite displayed result is positive exactly when its own rational
numerator is positive.  `none` fails this check rather than supplying zero. -/
def positiveTest (result : Result) : Bool :=
  result.any (fun value => decide (0 < value.num))

/-- Construct the positive value by inspecting the actual result.  The
boolean test justifies its numerator inequality; no representative is chosen
from propositional existence and no missing conditional is completed. -/
noncomputable def PositiveSupportedValue.of_positiveTest (result : Result)
    (positive : positiveTest result = true) : PositiveSupportedValue result := by
  cases result with
  | none => cases positive
  | some value => exact ⟨value, .value (QProb.equiv_refl value), of_decide_eq_true positive⟩

/-- Positive support implies the same finite test on the actual displayed
representative.  Rational cross-multiplication preserves numerator positivity;
the support witness need not contain that identical representative. -/
theorem PositiveSupportedValue.positiveTest {result : Result}
    (positive : PositiveSupportedValue result) : ProbabilityResult.positiveTest result = true := by
  cases result with
  | none => cases positive.equivalent
  | some value =>
      have actualPositive : 0 < value.num := by
        cases positive.equivalent with
        | value equivalent => exact (QProb.equiv_num_pos_iff equivalent).mpr positive.positive
      exact decide_eq_true actualPositive

end ProbabilityResult

variable {S : ObservedSignature.{0}}

namespace ProbabilityTerm

/-- Primitive positivity obligations at every conditional actually demanded
by this finite expression.  Guarding is directional: only a positive defined
left weight demands the right factor.  Zero outcomes and null skipped factors
are allowed, but strict multiplication and marginalization keep their ordinary
semantics.  For action-free terms all these tests use only the observed law. -/
def UsedConditionalsAdmissibleAt (model : ExactModel S) : ProbabilityTerm S → S.Assignment → Prop
  | .zero, _ => True
  | .kernel queryKernel, reference => queryKernel.ConditioningAdmissibleAt model reference
  | .marginalize nodes inner, reference =>
      forall variant, variant ∈ marginalAssignments S nodes reference → inner.UsedConditionalsAdmissibleAt model variant
  | .evaluateAt fixed inner, _ => inner.UsedConditionalsAdmissibleAt model fixed
  | .add left right, reference =>
      left.UsedConditionalsAdmissibleAt model reference ∧ right.UsedConditionalsAdmissibleAt model reference
  | .multiply left right, reference =>
      left.UsedConditionalsAdmissibleAt model reference ∧ right.UsedConditionalsAdmissibleAt model reference
  | .weightedMultiply weight factor, reference =>
      weight.UsedConditionalsAdmissibleAt model reference ∧
        (ProbabilityResult.positiveTest (weight.denote model reference) = true →
          factor.UsedConditionalsAdmissibleAt model reference)
  | .divide numerator denominator, reference =>
      numerator.UsedConditionalsAdmissibleAt model reference ∧
        denominator.UsedConditionalsAdmissibleAt model reference ∧
          ProbabilityResult.positiveTest (denominator.denote model reference) = true

/-- The primitive used-conditional tests construct the actual finite rational
value.  Recursion follows expression syntax and the exact finite marginal
enumeration, not an assumed compiler tree or a denotational-soundness theorem. -/
noncomputable def supportedAt_of_usedConditionalsAdmissible
    (model : ExactModel S) (term : ProbabilityTerm S) (reference : S.Assignment)
    (admissible : term.UsedConditionalsAdmissibleAt model reference) : term.SupportedAt model reference := by
  induction term generalizing reference with
  | zero => exact ⟨QProb.zero, .value (QProb.equiv_refl _)⟩
  | kernel kernel => exact Kernel.supportedAt_of_condition_positive model kernel reference admissible
  | marginalize nodes inner inductionHypothesis =>
      exact ProbabilityResult.sum_map_supported_of_mem (marginalAssignments S nodes reference)
        (fun variant => inner.denote model variant)
        (fun variant listed => inductionHypothesis variant (admissible variant listed))
  | evaluateAt fixed inner inductionHypothesis => exact inductionHypothesis fixed admissible
  | add left right leftInduction rightInduction =>
      exact ProbabilityResult.add_supported (leftInduction reference admissible.1) (rightInduction reference admissible.2)
  | multiply left right leftInduction rightInduction =>
      exact ProbabilityResult.multiply_supported (leftInduction reference admissible.1) (rightInduction reference admissible.2)
  | weightedMultiply weight factor weightInduction factorInduction =>
      exact ProbabilityResult.weightedMultiply_supported (weightInduction reference admissible.1)
        (fun positive => factorInduction reference (admissible.2 positive.positiveTest))
  | divide numerator denominator numeratorInduction _denominatorInduction =>
      exact ProbabilityResult.divide_supported_of_positive_denominator (numeratorInduction reference admissible.1)
        (ProbabilityResult.PositiveSupportedValue.of_positiveTest _ admissible.2.2)

/-- Read the same primitive demand conditions back from a defined expression.
This necessity direction keeps the domain exact: no factor test is imposed
at a zero guard, no unlisted marginal variant is inspected, and no positive
outcome numerator is inferred from ordinary support. -/
theorem usedConditionalsAdmissibleAt_of_supported
    (model : ExactModel S) (term : ProbabilityTerm S) (reference : S.Assignment)
    (supported : term.SupportedAt model reference) : term.UsedConditionalsAdmissibleAt model reference := by
  induction term generalizing reference with
  | zero => trivial
  | kernel kernel => exact Kernel.conditionPositive_of_supportedAt model kernel reference supported
  | marginalize nodes inner inductionHypothesis =>
      intro variant listed
      letI : DecidableEq S.Assignment :=
        FiniteProduct.assignmentDecidableEq S.count S.Value S.valueDecidableEq
      exact inductionHypothesis variant
        (ProbabilityResult.supported_map_of_mem_sum (marginalAssignments S nodes reference)
          (fun candidate => inner.denote model candidate) variant listed supported)
  | evaluateAt fixed inner inductionHypothesis => exact inductionHypothesis fixed supported
  | add left right leftInduction rightInduction =>
      exact ⟨leftInduction reference (ProbabilityResult.supported_left_of_add supported),
        rightInduction reference (ProbabilityResult.supported_right_of_add supported)⟩
  | multiply left right leftInduction rightInduction =>
      exact ⟨leftInduction reference (ProbabilityResult.supported_left_of_multiply supported),
        rightInduction reference (ProbabilityResult.supported_right_of_multiply supported)⟩
  | weightedMultiply weight factor weightInduction factorInduction =>
      refine ⟨weightInduction reference (ProbabilityResult.supported_weight_of_weightedMultiply supported), ?_⟩
      intro positive
      exact factorInduction reference (ProbabilityResult.supported_factor_of_weightedMultiply
        (ProbabilityResult.PositiveSupportedValue.of_positiveTest _ positive) supported)
  | divide numerator denominator numeratorInduction denominatorInduction =>
      exact ⟨numeratorInduction reference (ProbabilityResult.supported_numerator_of_divide supported),
        denominatorInduction reference (ProbabilityResult.supported_denominator_of_divide supported),
        (ProbabilityResult.positiveDenominatorOfSupportedDivide supported).positiveTest⟩

/-- The explicit primitive tests exactly characterize definition of the
partial expression.  The forward support value is computed, not chosen from
the `Nonempty` proposition appearing in this statement. -/
theorem usedConditionalsAdmissibleAt_iff_supported (model : ExactModel S)
    (term : ProbabilityTerm S) (reference : S.Assignment) :
    term.UsedConditionalsAdmissibleAt model reference ↔ Nonempty (term.SupportedAt model reference) := by
  constructor
  · intro admissible
    exact ⟨supportedAt_of_usedConditionalsAdmissible model term reference admissible⟩
  · rintro ⟨supported⟩
    exact usedConditionalsAdmissibleAt_of_supported model term reference supported

/-- All used-conditional demand tests are observable for action-free syntax.
The proof transfers the constructed printed value, then reads back the
primitive tests; it does not transfer a causal kernel or compiler `Data`. -/
theorem UsedConditionalsAdmissibleAt.transfer {left right : ExactModel S}
    (observational : ObservationalAgreement left right) (term : ProbabilityTerm S)
    (actionFree : term.ActionFree) (reference : S.Assignment)
    (admissible : term.UsedConditionalsAdmissibleAt left reference) :
    term.UsedConditionalsAdmissibleAt right reference :=
  usedConditionalsAdmissibleAt_of_supported right term reference
    (ProbabilityResult.Supported.transport (actionFree_invariant left right observational term actionFree reference)
      (supportedAt_of_usedConditionalsAdmissible left term reference admissible))

end ProbabilityTerm

end Causality
end Thesis
