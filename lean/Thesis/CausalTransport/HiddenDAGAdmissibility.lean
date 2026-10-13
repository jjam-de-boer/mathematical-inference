import Thesis.CausalTransport.HiddenDAGSemantics
import Thesis.Causality.UsedConditionalAdmissibility
import Thesis.Causality.PositiveDerivationSupport

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Native action, conditioning and used-conditional admissibility

These predicates inspect the original finite hidden-DAG record.  Native
conditioning uses its actual intervened distribution; native action overlap
uses its actual observed law and the signature's observed action parents.
The native used-conditional predicate recurses over the literal expression
with native kernel and term evaluation.  It is not defined by evaluating an
arbitrarily selected canonical model or by assuming a compiler's support.

The proved intervention-preserving collapse separately preserves every
primitive test, demand guard and finite summation context.  Thus the generic
syntax-directed admissibility-to-support theorem applies to original DAGs,
with arbitrary finite hidden and private-noise alphabets.  Neither a published
latent-projection interface nor do-calculus soundness is used for these
positivity and support constructions.

Pointwise action admissibility and uniform overlap on supported parent
contexts remain distinct.  The final application-domain statement must say
which one it quantifies.  In particular native conditioner positivity is
not replaced by factual action overlap, and observational agreement is not
used to transfer causal conditioner support.
-/

namespace FiniteHiddenDAGSCM

/-- The displayed action conditional is positive at this observed parent
context.  Positivity is checked on its joint action-and-parent cylinder;
the generic cylinder theorem also guarantees its positive conditioner. -/
def ObservationalActionAdmissibleAt (model : FiniteHiddenDAGSCM S P)
    (action : NodeSet S) (reference : S.Assignment) : Prop :=
  0 < (model.observationalDist.probVal
    (Kernel.agreesOn (NodeSet.union action (S.actionParents action)) reference)).num

/-- Fixed action values have positive overlap on every supported observed
parent context.  Null parent contexts require nothing; this is not positivity
of all observed atoms or a pointwise test at an unrelated parent assignment. -/
def ObservationalActionAdmissibleOnParentSupport (model : FiniteHiddenDAGSCM S P)
    (action : NodeSet S) (reference : S.Assignment) : Prop :=
  forall variant : S.Assignment,
    Kernel.agreesOn action reference variant = true →
    0 < (model.observationalDist.probVal (Kernel.agreesOn (S.actionParents action) variant)).num →
    model.ObservationalActionAdmissibleAt action variant

/-- Actual native conditioning admissibility, independent of whether the
selected outcome has positive mass.  Hard interventions remain executable
even outside the separate observational action-admissibility domain. -/
def ConditioningAdmissibleAt (model : FiniteHiddenDAGSCM S P) (kernel : Kernel S)
    (reference : S.Assignment) : Prop :=
  0 < ((model.kernelDistribution kernel reference).probVal (kernel.conditionEvent reference)).num

/-- Literal observational preservation keeps the pointwise action test. -/
theorem observationalActionAdmissibleAt_iff_collapsed (model : FiniteHiddenDAGSCM S P)
    (action : NodeSet S) (reference : S.Assignment) :
    model.ObservationalActionAdmissibleAt action reference ↔
      Thesis.Causality.ObservationalActionAdmissibleAt model.toLatentRootSCM action reference := by
  change 0 < (model.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union action (S.actionParents action)) reference)).num ↔
    0 < (model.toLatentRootSCM.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union action (S.actionParents action)) reference)).num
  rw [model.toLatentRootSCM_observationalDist]

/-- All supported-parent contexts, not just one selected context, are
preserved by the actual collapse's observational-record equality. -/
theorem observationalActionAdmissibleOnParentSupport_iff_collapsed (model : FiniteHiddenDAGSCM S P)
    (action : NodeSet S) (reference : S.Assignment) :
    model.ObservationalActionAdmissibleOnParentSupport action reference ↔
      Thesis.Causality.ObservationalActionAdmissibleOnParentSupport model.toLatentRootSCM action reference := by
  simp only [ObservationalActionAdmissibleOnParentSupport,
    Thesis.Causality.ObservationalActionAdmissibleOnParentSupport, ObservationalActionAdmissibleAt,
    Thesis.Causality.ObservationalActionAdmissibleAt, Thesis.Causality.ObservationalCylinderPositiveAt,
    model.toLatentRootSCM_observationalDist]

/-- Uniform supported-parent action overlap is an observable property of
the native law.  Parent positivity transfers backwards before action-cell
positivity transfers forwards; no causal support transfer is inferred. -/
theorem ObservationalActionAdmissibleOnParentSupport.transfer
    {left right : FiniteHiddenDAGSCM S P} (observational : left.ObservationalAgreement right)
    {action : NodeSet S} {reference : S.Assignment}
    (admissible : left.ObservationalActionAdmissibleOnParentSupport action reference) :
    right.ObservationalActionAdmissibleOnParentSupport action reference := by
  intro variant sameAction parentPositive
  have leftParent : 0 < (left.observationalDist.probVal
      (Kernel.agreesOn (S.actionParents action) variant)).num :=
    (QProb.equiv_num_pos_iff (observational _)).mpr parentPositive
  exact (QProb.equiv_num_pos_iff (observational _)).mp (admissible variant sameAction leftParent)

/-- Actual intervention preservation keeps the original conditioner test.
This is equality of the finite distributions, not a soundness inference. -/
theorem conditioningAdmissibleAt_iff_collapsed (model : FiniteHiddenDAGSCM S P)
    (kernel : Kernel S) (reference : S.Assignment) :
    model.ConditioningAdmissibleAt kernel reference ↔
      kernel.ConditioningAdmissibleAt model.toLatentRootSCM reference := by
  unfold ConditioningAdmissibleAt Kernel.ConditioningAdmissibleAt
  rw [model.kernelDistribution_preserved kernel reference]

/-- The native counterpart of the explicit used-conditional demand tests.
Every kernel conditioner and quotient denominator is read in the original
record.  The same directional positive-weight guard controls unused factors. -/
def UsedConditionalsAdmissibleAt (model : FiniteHiddenDAGSCM S P) : ProbabilityTerm S → S.Assignment → Prop
  | .zero, _ => True
  | .kernel queryKernel, reference => model.ConditioningAdmissibleAt queryKernel reference
  | .marginalize nodes inner, reference =>
      forall variant, variant ∈ ProbabilityTerm.marginalAssignments S nodes reference →
        model.UsedConditionalsAdmissibleAt inner variant
  | .evaluateAt fixed inner, _ => model.UsedConditionalsAdmissibleAt inner fixed
  | .add left right, reference =>
      model.UsedConditionalsAdmissibleAt left reference ∧ model.UsedConditionalsAdmissibleAt right reference
  | .multiply left right, reference =>
      model.UsedConditionalsAdmissibleAt left reference ∧ model.UsedConditionalsAdmissibleAt right reference
  | .weightedMultiply weight factor, reference =>
      model.UsedConditionalsAdmissibleAt weight reference ∧
        (ProbabilityResult.positiveTest (model.termDenote weight reference) = true →
          model.UsedConditionalsAdmissibleAt factor reference)
  | .divide numerator denominator, reference =>
      model.UsedConditionalsAdmissibleAt numerator reference ∧
        model.UsedConditionalsAdmissibleAt denominator reference ∧
          ProbabilityResult.positiveTest (model.termDenote denominator reference) = true

/-- Preserve the entire primitive demand predicate, including each listed
marginal variant and every guard.  Native admissibility is defined above in
its own semantics; this theorem is the separately proved bridge. -/
theorem usedConditionalsAdmissibleAt_iff_collapsed (model : FiniteHiddenDAGSCM S P)
    (term : ProbabilityTerm S) : forall reference,
    model.UsedConditionalsAdmissibleAt term reference ↔
      term.UsedConditionalsAdmissibleAt model.toLatentRootSCM reference := by
  intro reference
  induction term generalizing reference with
  | zero => rfl
  | kernel queryKernel => exact model.conditioningAdmissibleAt_iff_collapsed queryKernel reference
  | marginalize nodes inner inductionHypothesis =>
      constructor
      · intro admissible variant listed
        exact (inductionHypothesis variant).mp (admissible variant listed)
      · intro admissible variant listed
        exact (inductionHypothesis variant).mpr (admissible variant listed)
  | evaluateAt fixed inner inductionHypothesis => exact inductionHypothesis fixed
  | add left right leftIH rightIH =>
      simp only [UsedConditionalsAdmissibleAt, ProbabilityTerm.UsedConditionalsAdmissibleAt,
        leftIH reference, rightIH reference]
  | multiply left right leftIH rightIH =>
      simp only [UsedConditionalsAdmissibleAt, ProbabilityTerm.UsedConditionalsAdmissibleAt,
        leftIH reference, rightIH reference]
  | weightedMultiply weight factor weightIH factorIH =>
      simp only [UsedConditionalsAdmissibleAt, ProbabilityTerm.UsedConditionalsAdmissibleAt,
        weightIH reference, factorIH reference, model.termDenote_preserved weight reference]
  | divide numerator denominator numeratorIH denominatorIH =>
      simp only [UsedConditionalsAdmissibleAt, ProbabilityTerm.UsedConditionalsAdmissibleAt,
        numeratorIH reference, denominatorIH reference, model.termDenote_preserved denominator reference]

/-- Primitive native conditioning positivity constructs the actual native
kernel value.  It does not assume observational overlap or a complete tree. -/
noncomputable def supportedAt_of_conditioningAdmissible (model : FiniteHiddenDAGSCM S P)
    (kernel : Kernel S) (reference : S.Assignment)
    (admissible : model.ConditioningAdmissibleAt kernel reference) :
    model.TermSupportedAt (.kernel kernel) reference :=
  model.termSupportedAt_of_collapsed _ reference
    (Kernel.supportedAt_of_condition_positive model.toLatentRootSCM kernel reference
      ((model.conditioningAdmissibleAt_iff_collapsed kernel reference).mp admissible))

/-- All primitive native used-conditional tests construct a native printed
value.  The syntax-directed construction and literal collapse bridge are
independent of graph-indexed soundness and of every compiler's `Data`. -/
noncomputable def supportedAt_of_usedConditionalsAdmissible (model : FiniteHiddenDAGSCM S P)
    (term : ProbabilityTerm S) (reference : S.Assignment)
    (admissible : model.UsedConditionalsAdmissibleAt term reference) : model.TermSupportedAt term reference :=
  model.termSupportedAt_of_collapsed term reference
    (ProbabilityTerm.supportedAt_of_usedConditionalsAdmissible model.toLatentRootSCM term reference
      ((model.usedConditionalsAdmissibleAt_iff_collapsed term reference).mp admissible))

/-- Read every actual native primitive test back from a defined value.
Together with the forward constructor this rules out a hidden strengthening
of the demand domain at null guards or zero outcome numerators. -/
theorem usedConditionalsAdmissibleAt_iff_supported (model : FiniteHiddenDAGSCM S P)
    (term : ProbabilityTerm S) (reference : S.Assignment) :
    model.UsedConditionalsAdmissibleAt term reference ↔ Nonempty (model.TermSupportedAt term reference) := by
  constructor
  · intro admissible
    exact ⟨model.supportedAt_of_usedConditionalsAdmissible term reference admissible⟩
  · rintro ⟨supported⟩
    exact (model.usedConditionalsAdmissibleAt_iff_collapsed term reference).mpr
      (ProbabilityTerm.usedConditionalsAdmissibleAt_of_supported model.toLatentRootSCM term reference
        (model.termSupportedAt_to_collapsed term reference supported))

/-- All used-conditional tests of action-free native syntax are observable.
The original causal conditioner of a requested query is not part of this
transfer statement; its admissibility must remain explicit on both sides. -/
theorem UsedConditionalsAdmissibleAt.transfer {left right : FiniteHiddenDAGSCM S P}
    (observational : left.ObservationalAgreement right) (term : ProbabilityTerm S)
    (actionFree : term.ActionFree) (reference : S.Assignment)
    (admissible : left.UsedConditionalsAdmissibleAt term reference) :
    right.UsedConditionalsAdmissibleAt term reference :=
  (right.usedConditionalsAdmissibleAt_iff_supported term reference).mpr
    ⟨ProbabilityResult.Supported.transport (actionFree_invariant left right observational term actionFree reference)
      (left.supportedAt_of_usedConditionalsAdmissible term reference admissible)⟩

/-- Positive records meet even uniform parent-context action admissibility.
The generic proof is transported by literal observed-law preservation, without
importing native denotational soundness or selecting a canonical model. -/
theorem ObservationallyPositive.actionAdmissibleOnParentSupport {model : FiniteHiddenDAGSCM S P}
    (positive : model.ObservationallyPositive) (action : NodeSet S) (reference : S.Assignment) :
    model.ObservationalActionAdmissibleOnParentSupport action reference := by
  have rootPositive : Thesis.Causality.ObservationallyPositive model.toLatentRootSCM := by
    intro assignment
    rw [model.toLatentRootSCM_observationalDist]
    exact positive assignment
  exact (model.observationalActionAdmissibleOnParentSupport_iff_collapsed action reference).mpr
    (rootPositive.actionAdmissibleOnParentSupport action reference)

/-- Positive records meet the primitive used-conditional checks of every
kernel-generated expression.  `ZeroFree` excludes the literal zero constructor,
not zero probabilities in the broader model class.  This coverage lemma keeps
the positive countermodel domain available for later completeness assembly. -/
theorem ObservationallyPositive.usedConditionalsAdmissibleAt_of_zeroFree
    {model : FiniteHiddenDAGSCM S P} (positive : model.ObservationallyPositive)
    (term : ProbabilityTerm S) (zeroFree : term.ZeroFree) (reference : S.Assignment) :
    model.UsedConditionalsAdmissibleAt term reference := by
  have rootPositive : Thesis.Causality.ObservationallyPositive model.toLatentRootSCM := by
    intro assignment
    rw [model.toLatentRootSCM_observationalDist]
    exact positive assignment
  exact (model.usedConditionalsAdmissibleAt_iff_collapsed term reference).mpr
    (ProbabilityTerm.usedConditionalsAdmissibleAt_of_supported model.toLatentRootSCM term reference
      (term.positiveSupportedValue_of_zeroFree model.toLatentRootSCM rootPositive zeroFree reference).toSupported)

end FiniteHiddenDAGSCM

end Causality
end Thesis
