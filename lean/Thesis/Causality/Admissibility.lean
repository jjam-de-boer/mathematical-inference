import Thesis.Causality.ConditionalSupport

namespace Thesis
namespace Causality

open Probability

/-!
# Explicit action and conditioning admissibility at zero-containing laws

Shpitser--Pearl's joint and conditional identification papers do not assume
that the complete observed distribution is positive.  Instead they require
the displayed action conditional `P(x | Pa(X) \ X)` to be positive, each
conditional that is actually used to have a positive conditioner, and the
conditional target `P_x(Y | z)` to have `P_x(z) > 0`.

References: https://ftp.cs.ucla.edu/pub/stat_ser/r327.pdf, pp. 2--3, and
https://ftp.cs.ucla.edu/pub/stat_ser/r329.pdf, pp. 2--3.

This module makes those *primitive* tests precise in the existing partial,
finite-rational semantics.  An action's parent context is explicit: it uses
observed directed parents, excludes nodes in the simultaneous action, and
does not replace that context by all observed nodes or by hidden parents.
The pointwise test and the stronger test on every supported parent context
are deliberately separate; a theorem must say which one it needs.

Positivity of a displayed action conditional is represented by positivity of
its joint action-and-parent cylinder.  The equivalence below checks that
this is exactly a positive, genuinely defined conditional, not a value
assigned to division by zero.  Conditioning admissibility uses the actual
intervened record and is equivalent to having a supported partial kernel.
Neither test demands that the outcome probability itself be positive.

These are not yet the admissibility invariant of a whole ID/IDC run.  In
particular the module does not assert that action admissibility alone supplies
every recursive quotient, component exchange, or Bayes marginal.  Connecting
the paper's restrictions on *all used conditionals* to those recursive
obligations is the remaining support-propagation work, not a hidden field
assuming the compiler's complete `Data` or its whole support tree.
-/

variable {S : ObservedSignature}

namespace ObservedSignature

/-- The observed parents of a simultaneous action, with action coordinates
removed.  Scanning the finite node list is constructive and respects the
signature's actual directed graph; no parent is chosen from an existential. -/
def actionParents (S : ObservedSignature) (action : NodeSet S) : NodeSet S :=
  fun parent => !action parent &&
    finAny S.count (fun child => action child && S.directed parent child)

/-- Internal parents of an action block are not conditioners of its displayed
action probability.  This also makes the simultaneous-action case explicit. -/
theorem actionParents_disjoint (S : ObservedSignature) (action : NodeSet S) :
    NodeSet.Disjoint action (S.actionParents action) := by
  intro node selected
  simp only [actionParents, selected, Bool.not_true, Bool.false_and]

end ObservedSignature

/-- The displayed `P(x | Pa(X) \ X)` is defined and strictly positive at
this parent context.  A positive numerator cylinder already forces a
positive parent denominator, as proved below.  Other observed atoms may be
zero; this is not global observational positivity. -/
def ObservationalActionAdmissibleAt (model : FiniteLatentSCM S)
    (action : NodeSet S) (reference : S.Assignment) : Prop :=
  ObservationalCylinderPositiveAt model
    (NodeSet.union action (S.actionParents action)) reference

/-- Uniform action overlap on supported observed-parent contexts, retaining
the fixed action values of `reference`.  Null parent contexts impose no
condition.  This stronger predicate is exposed separately rather than
silently reading a pointwise action test as a universal one. -/
def ObservationalActionAdmissibleOnParentSupport (model : FiniteLatentSCM S)
    (action : NodeSet S) (reference : S.Assignment) : Prop :=
  forall variant : S.Assignment,
    Kernel.agreesOn action reference variant = true →
    ObservationalCylinderPositiveAt model (S.actionParents action) variant →
    ObservationalActionAdmissibleAt model action variant

namespace ObservationalActionAdmissibleAt

/-- The conditioner of an admissible action conditional is itself positive.
No positivity of unrelated coordinates or selected outcome values is used. -/
theorem parent_positive {model : FiniteLatentSCM S} {action : NodeSet S}
    {reference : S.Assignment}
    (admissible : ObservationalActionAdmissibleAt model action reference) :
    ObservationalCylinderPositiveAt model (S.actionParents action) reference :=
  ObservationalCylinderPositiveAt.of_subset
    (NodeSet.subset_union_right action (S.actionParents action)) admissible

/-- Action admissibility is observable: identical whole observed laws
preserve it even if their causal mechanisms or hidden alphabets differ. -/
theorem transfer {left right : FiniteLatentSCM S}
    (observational : ProbabilityTerm.ObservationalAgreement left right)
    {action : NodeSet S} {reference : S.Assignment}
    (admissible : ObservationalActionAdmissibleAt left action reference) :
    ObservationalActionAdmissibleAt right action reference :=
  ObservationalCylinderPositiveAt.transfer observational admissible

/-- Construct the *actual* positive action conditional from the finite
numerator and parent denominator.  The returned value is in `Type`; it is
computed from this record instead of selected using choice. -/
noncomputable def positiveValue {model : FiniteLatentSCM S} {action : NodeSet S}
    {reference : S.Assignment}
    (admissible : ObservationalActionAdmissibleAt model action reference) :
    ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.kernel ⟨action, NodeSet.empty, S.actionParents action⟩).denote
        model reference) := by
  let kernel : Kernel S := ⟨action, NodeSet.empty, S.actionParents action⟩
  have noAction : kernel.hasAction = false :=
    ProbabilityTerm.actionFree_hasAction_false kernel (fun _ => rfl)
  have observational : kernel.distribution model reference = model.observationalDist := by
    simp only [Kernel.distribution, noAction, Bool.false_eq_true, if_false]
  let numerator := (kernel.distribution model reference).probVal (kernel.numeratorEvent reference)
  let denominator := (kernel.distribution model reference).probVal (kernel.conditionEvent reference)
  have denominatorPositive : 0 < denominator.num := by
    simpa only [denominator, observational, kernel, Kernel.conditionEvent] using admissible.parent_positive
  have cylinder : kernel.numeratorEvent reference =
      Kernel.agreesOn (NodeSet.union action (S.actionParents action)) reference := by
    funext sample
    exact (Kernel.agreesOn_union action (S.actionParents action) reference sample).symm
  have numeratorPositive : 0 < numerator.num := by
    simpa only [numerator, observational, cylinder] using admissible
  refine ⟨QProb.div numerator denominator denominatorPositive, ?_,
    Nat.mul_pos numeratorPositive denominator.den_pos⟩
  change ProbabilityResult.Equivalent
    (ProbabilityResult.divide (some numerator) (some denominator)) _
  rw [ProbabilityResult.divide, dif_pos denominatorPositive]
  exact .value (QProb.equiv_refl _)

end ObservationalActionAdmissibleAt

/-- The positive action-conditional interpretation also implies the cylinder
test.  Thus that test neither accepts an undefined conditional nor silently
strengthens positivity of the selected action conditional to the full law. -/
theorem observationalActionAdmissibleAt_iff_positiveValue
    (model : FiniteLatentSCM S) (action : NodeSet S) (reference : S.Assignment) :
    ObservationalActionAdmissibleAt model action reference ↔
      Nonempty (ProbabilityResult.PositiveSupportedValue
        ((ProbabilityTerm.kernel ⟨action, NodeSet.empty, S.actionParents action⟩).denote
          model reference)) := by
  constructor
  · intro admissible
    exact ⟨admissible.positiveValue⟩
  · rintro ⟨positive⟩
    let kernel : Kernel S := ⟨action, NodeSet.empty, S.actionParents action⟩
    let numerator := (kernel.distribution model reference).probVal (kernel.numeratorEvent reference)
    let denominator := (kernel.distribution model reference).probVal (kernel.conditionEvent reference)
    have denominatorPositive : 0 < denominator.num :=
      Kernel.conditionPositive_of_supportedAt model kernel reference positive.toSupported
    have equivalent : ProbabilityResult.Equivalent
        (some (QProb.div numerator denominator denominatorPositive)) (some positive.value) := by
      have actual := positive.equivalent
      change ProbabilityResult.Equivalent
        (ProbabilityResult.divide (some numerator) (some denominator)) (some positive.value) at actual
      simpa only [ProbabilityResult.divide, dif_pos denominatorPositive] using actual
    have numeratorPositive : 0 < numerator.num := by
      cases equivalent with
      | value fractions =>
          have productPositive := (QProb.equiv_num_pos_iff fractions).mpr positive.positive
          change 0 < numerator.num * denominator.den at productPositive
          by_cases numeratorIsPositive : 0 < numerator.num
          · exact numeratorIsPositive
          · have zero : numerator.num = 0 := Nat.eq_zero_of_not_pos numeratorIsPositive
            rw [zero, Nat.zero_mul] at productPositive
            exact False.elim (Nat.not_lt_zero _ productPositive)
    have noAction : kernel.hasAction = false :=
      ProbabilityTerm.actionFree_hasAction_false kernel (fun _ => rfl)
    have observational : kernel.distribution model reference = model.observationalDist := by
      simp only [Kernel.distribution, noAction, Bool.false_eq_true, if_false]
    have cylinder : kernel.numeratorEvent reference =
        Kernel.agreesOn (NodeSet.union action (S.actionParents action)) reference := by
      funext sample
      exact (Kernel.agreesOn_union action (S.actionParents action) reference sample).symm
    simpa only [numerator, observational, cylinder] using numeratorPositive

namespace ObservationalActionAdmissibleOnParentSupport

/-- With no external observed parents, one admissible action cell already
supplies uniform overlap on parent support.  References agreeing on the
fixed action describe the same cylinder; all other coordinates are ignored.
This does not turn that coarse action test into support of a whole ID run. -/
theorem of_noParents {model : FiniteLatentSCM S} {action : NodeSet S}
    {reference : S.Assignment} (noParents : S.actionParents action = NodeSet.empty)
    (admissible : ObservationalActionAdmissibleAt model action reference) :
    ObservationalActionAdmissibleOnParentSupport model action reference := by
  intro variant sameAction _parentPositive
  have agree : forall node, action node = true → reference node = variant node := by
    intro node selected
    have component := (finAll_eq_true_iff _).mp sameAction node
    have actual : variant node = reference node := by
      apply of_decide_eq_true
      simpa only [selected, if_true] using component
    exact actual.symm
  have cylinder : Kernel.agreesOn action reference = Kernel.agreesOn action variant := by
    funext sample
    exact Kernel.agreesOn_reference_congr action reference variant sample agree
  change ObservationalCylinderPositiveAt model (NodeSet.union action (S.actionParents action)) variant
  change ObservationalCylinderPositiveAt model (NodeSet.union action (S.actionParents action)) reference at admissible
  rw [noParents, NodeSet.union_empty_right] at admissible ⊢
  change 0 < (model.observationalDist.probVal (Kernel.agreesOn action reference)).num at admissible
  change 0 < (model.observationalDist.probVal (Kernel.agreesOn action variant)).num
  rw [← cylinder]
  exact admissible

/-- Uniform parent-context action overlap is also determined solely by the
observed law.  Parent support is first transferred backwards; action overlap
is then transferred forwards.  Causal-support transfer is not inferred. -/
theorem transfer {left right : FiniteLatentSCM S}
    (observational : ProbabilityTerm.ObservationalAgreement left right)
    {action : NodeSet S} {reference : S.Assignment}
    (admissible : ObservationalActionAdmissibleOnParentSupport left action reference) :
    ObservationalActionAdmissibleOnParentSupport right action reference := by
  intro variant sameAction parentPositive
  have leftParent := ObservationalCylinderPositiveAt.transfer
    (fun event => QProb.equiv_symm (observational event)) parentPositive
  exact (admissible variant sameAction leftParent).transfer observational

end ObservationalActionAdmissibleOnParentSupport

/-- The existing positive class satisfies even the uniform parent-context
condition.  Positive countermodels therefore remain available to the future
support-admissible failure theorem; no countermodel family is assumed here. -/
theorem ObservationallyPositive.actionAdmissibleOnParentSupport
    {model : ExactModel S} (positive : ObservationallyPositive model)
    (action : NodeSet S) (reference : S.Assignment) :
    ObservationalActionAdmissibleOnParentSupport model action reference := by
  intro variant _sameAction _parentPositive
  exact positive.cylinder_positive (NodeSet.union action (S.actionParents action)) variant

namespace Kernel

/-- A conditional's admissibility is positivity of its actual intervened
conditioner, not of its outcome numerator.  Hard interventions themselves
remain executable even outside the paper's admissible identification domain. -/
def ConditioningAdmissibleAt (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) : Prop :=
  0 < ((kernel.distribution model reference).probVal (kernel.conditionEvent reference)).num

/-- Precisely characterize when this partial kernel has a value.  The forward
witness is its finite rational quotient; the reverse direction extracts its
positive denominator.  No arbitrary completion of a null conditional occurs. -/
theorem conditioningAdmissibleAt_iff_supported
    (model : FiniteLatentSCM S) (kernel : Kernel S) (reference : S.Assignment) :
    ConditioningAdmissibleAt model kernel reference ↔
      Nonempty ((ProbabilityTerm.kernel kernel).SupportedAt model reference) := by
  constructor
  · intro admissible
    exact ⟨supportedAt_of_condition_positive model kernel reference admissible⟩
  · rintro ⟨supported⟩
    exact conditionPositive_of_supportedAt model kernel reference supported

/-- A supported original conditioner remains admissible after promotion of
any finite block to actions.  This propagates *conditioning* admissibility;
it does not assert observational admissibility of the newly forced action.
That distinction is essential at null factual action cells. -/
theorem ConditioningAdmissibleAt.promoteCondition
    {model : FiniteLatentSCM S} {action outcome promoted condition : NodeSet S}
    {reference : S.Assignment}
    (admissible : ConditioningAdmissibleAt model
      ⟨outcome, action, NodeSet.union promoted condition⟩ reference) :
    ConditioningAdmissibleAt model
      ⟨outcome, NodeSet.union action promoted, condition⟩ reference :=
  conditionPositive_of_supportedAt model _ reference
    (supportedAt_promoteCondition model action outcome promoted condition reference
      (supportedAt_of_condition_positive model _ reference admissible))

end Kernel

end Causality
end Thesis
