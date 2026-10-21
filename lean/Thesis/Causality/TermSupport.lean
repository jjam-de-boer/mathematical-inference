import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
# Explicit support witnesses for finite probability terms

A symbolic term denotes a rational value only when every conditional that it
actually uses has positive denominator. These constructors retain that value
and its checked denotation as data. Products need both supplied witnesses;
division additionally needs positivity of the supplied denominator value.
Neither operation appeals to causal soundness to manufacture support.

For observational kernels, the positive-model class supplies every conditioner
cylinder, including those appearing in finite marginalizations. The stronger
numerator-positivity lemma retains its original full-positivity hypothesis:
it must not be applied to arbitrary zero-containing observational models.
Assignment-local sufficient support for such models remains in
`Causality.ObservationalSupport`.

These are shared semantic constructors, independent of identification engines,
historical branch traces and the soundness/completeness assembly. Their original
names and definitions remain available through `CompletenessCertificates`.
-/

/-- An empty-action unconditional kernel is always defined: its
conditioner is the sure event. -/
noncomputable def emptyActionKernel_supportedAt
    (model : FiniteLatentSCM S) (outcome : NodeSet S)
    (assignment : S.Assignment) :
    (ProbabilityTerm.kernel
      ⟨outcome, NodeSet.empty, NodeSet.empty⟩).SupportedAt model assignment :=
  ⟨((Kernel.mk outcome NodeSet.empty NodeSet.empty).distribution
      model assignment).probVal (Kernel.agreesOn outcome assignment),
    Kernel.unconditionalDenote model outcome NodeSet.empty assignment⟩

/-- An observational kernel `P(Y | Z)` is defined in every
observationally positive model: the conditioner cylinder is strictly
positive. -/
noncomputable def observationalConditional_supportedAt
    (model : FiniteLatentSCM S)
    (positive : ObservationallyPositive model)
    (outcome condition : NodeSet S) (assignment : S.Assignment) :
    (ProbabilityTerm.kernel
      ⟨outcome, NodeSet.empty, condition⟩).SupportedAt model assignment := by
  let kernel : Kernel S := ⟨outcome, NodeSet.empty, condition⟩
  have hNoAction : kernel.hasAction = false := by
    apply (finAny_eq_false_iff _).mpr
    intro _i
    rfl
  have hobs : kernel.distribution model assignment = model.observationalDist := by
    simp [Kernel.distribution, hNoAction]
  let denVal :=
    (kernel.distribution model assignment).probVal
      (kernel.conditionEvent assignment)
  let numVal :=
    (kernel.distribution model assignment).probVal
      (kernel.numeratorEvent assignment)
  have hpos : 0 < denVal.num := by
    have hcyl :
        0 <
          (model.observationalDist.probVal
            (Kernel.agreesOn condition assignment)).num :=
      ObservationallyPositive.cylinder_positive positive condition assignment
    simpa [denVal, hobs, Kernel.conditionEvent] using hcyl
  have hdenote :
      ProbabilityResult.Equivalent
        (kernel.denote model assignment)
        (ProbabilityResult.divide (some numVal) (some denVal)) :=
    ProbabilityResult.refl _
  have hdefinedEq :
      ProbabilityResult.divide (some numVal) (some denVal) =
        some (QProb.div numVal denVal hpos) := by
    simp only [ProbabilityResult.divide]
    rw [dif_pos hpos]
  exact
    ⟨QProb.div numVal denVal hpos,
      ProbabilityResult.trans hdenote
        (by
          rw [hdefinedEq]
          exact ProbabilityResult.Equivalent.value (QProb.equiv_refl _))⟩

/-- The denoted value of an observational kernel is strictly positive:
its numerator is the joint cylinder on `Y ∪ Z`. -/
theorem observationalConditional_num_pos
    (model : FiniteLatentSCM S)
    (positive : ObservationallyPositive model)
    (outcome condition : NodeSet S) (assignment : S.Assignment) :
    0 <
      (observationalConditional_supportedAt model positive outcome
        condition assignment).1.num := by
  let kernel : Kernel S := ⟨outcome, NodeSet.empty, condition⟩
  have hNoAction : kernel.hasAction = false := by
    apply (finAny_eq_false_iff _).mpr
    intro _i
    rfl
  have hobs :
      kernel.distribution model assignment = model.observationalDist := by
    simp [Kernel.distribution, hNoAction]
  let denVal :=
    (kernel.distribution model assignment).probVal
      (kernel.conditionEvent assignment)
  let numVal :=
    (kernel.distribution model assignment).probVal
      (kernel.numeratorEvent assignment)
  have hpos : 0 < denVal.num := by
    have hcyl :
        0 <
          (model.observationalDist.probVal
            (Kernel.agreesOn condition assignment)).num :=
      ObservationallyPositive.cylinder_positive positive condition assignment
    simpa [denVal, hobs, Kernel.conditionEvent] using hcyl
  have hnumPos : 0 < numVal.num := by
    have hcyl :
        0 <
          (model.observationalDist.probVal
            (Kernel.agreesOn (NodeSet.union outcome condition)
              assignment)).num :=
      ObservationallyPositive.cylinder_positive positive
        (NodeSet.union outcome condition) assignment
    have hnumEv :
        kernel.numeratorEvent assignment =
          Kernel.agreesOn (NodeSet.union outcome condition) assignment := by
      funext sample
      simpa [Kernel.numeratorEvent] using
        (Kernel.agreesOn_union outcome condition assignment sample).symm
    simpa [numVal, hobs, hnumEv] using hcyl
  have hdefinedEq :
      ProbabilityResult.divide (some numVal) (some denVal) =
        some (QProb.div numVal denVal hpos) := by
    simp only [ProbabilityResult.divide]
    rw [dif_pos hpos]
  have hdenote :
      ProbabilityResult.Equivalent
        ((ProbabilityTerm.kernel
          ⟨outcome, NodeSet.empty, condition⟩).denote model assignment)
        (some (QProb.div numVal denVal hpos)) := by
    simp only [ProbabilityTerm.denote, Kernel.denote]
    rw [hdefinedEq]
    exact ProbabilityResult.Equivalent.value (QProb.equiv_refl _)
  let hsup :=
    observationalConditional_supportedAt model positive outcome condition
      assignment
  show 0 < hsup.1.num
  cases ProbabilityResult.trans (ProbabilityResult.symm hsup.2) hdenote with
  | value hequiv =>
      exact
        (QProb.equiv_num_pos_iff hequiv).mpr
          (Nat.mul_pos hnumPos denVal.den_pos)

/-- Finite sum of an observational conditional `P(Y | Z)`.  Defined
once every variant's conditioner cylinder is strictly positive. -/
noncomputable def observationalConditionalMarginal_supportedAt
    (model : FiniteLatentSCM S)
    (positive : ObservationallyPositive model)
    (outcome condition summed : NodeSet S) (assignment : S.Assignment) :
    (ProbabilityTerm.marginalize summed
      (.kernel ⟨outcome, NodeSet.empty, condition⟩)).SupportedAt
      model assignment := by
  simpa [ProbabilityTerm.denote] using
    ProbabilityResult.sum_map_supported
      (ProbabilityTerm.marginalAssignments S summed assignment)
      (fun variant =>
        (ProbabilityTerm.kernel
          ⟨outcome, NodeSet.empty, condition⟩).denote model variant)
      (fun variant =>
        observationalConditional_supportedAt model positive outcome
          condition variant)

/-- A product of defined terms is defined. -/
noncomputable def ProbabilityTerm.multiply_supportedAt
    {model : FiniteLatentSCM S} {assignment : S.Assignment}
    {left right : ProbabilityTerm S}
    (hleft : left.SupportedAt model assignment)
    (hright : right.SupportedAt model assignment) :
    (ProbabilityTerm.multiply left right).SupportedAt model assignment := by
  simpa [ProbabilityTerm.denote] using
    ProbabilityResult.multiply_supported hleft hright

/-- Divide of two defined terms is defined once the denominator value is
strictly positive.  Positivity is a property of the displayed rational,
not of denotational soundness of a surrounding derivation. -/
noncomputable def ProbabilityTerm.divide_supportedAt
    {model : FiniteLatentSCM S} {assignment : S.Assignment}
    {left right : ProbabilityTerm S}
    (hnum : left.SupportedAt model assignment)
    (hden : right.SupportedAt model assignment)
    (hpos : 0 < hden.1.num) :
    (ProbabilityTerm.divide left right).SupportedAt model assignment := by
  have hdiv :
      ProbabilityResult.Equivalent
        ((ProbabilityTerm.divide left right).denote model assignment)
        (ProbabilityResult.divide (some hnum.1) (some hden.1)) := by
    simpa [ProbabilityTerm.denote] using
      ProbabilityResult.divide_congr hnum.2 hden.2
  have hdefinedEq :
      ProbabilityResult.divide (some hnum.1) (some hden.1) =
        some (QProb.div hnum.1 hden.1 hpos) := by
    simp only [ProbabilityResult.divide]
    rw [dif_pos hpos]
  exact
    ⟨QProb.div hnum.1 hden.1 hpos,
      ProbabilityResult.trans hdiv
        (by
          rw [hdefinedEq]
          exact ProbabilityResult.Equivalent.value (QProb.equiv_refl _))⟩

end Causality
end Thesis
