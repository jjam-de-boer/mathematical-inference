import Thesis.Causality.Semantics

namespace Thesis
namespace Causality

open Probability

/-!
# Intrinsic support algebra for recursive kernels with zeros

These lemmas concern the actual finite probability records, before graph
rules or identification soundness.  An unconditional kernel is supported
even when its outcome has mass zero.  Finite marginalization needs support
only of its enumerated summands.  Division needs a positive denominator, not
a positive numerator.  Keeping those facts separate avoids propagating an
unnecessarily everywhere-positive recursive-input invariant.

A conditional kernel is also compared with its literal quotient of two
unconditional kernels under the same intervention.  The comparison includes
null conditioners: both sides remain undefined there.  It is a proved
finite-record identity, not a new derivation rule or an assumed semantic
certificate leaf.
-/

namespace ProbabilityResult

/-- Construct a quotient from a supported numerator and a positive displayed
denominator.  In particular a supported zero numerator is not rejected. -/
noncomputable def divide_supported_of_positive_denominator {numerator denominator : Result}
    (numeratorSupported : Supported numerator)
    (denominatorPositive : PositiveSupportedValue denominator) :
    Supported (divide numerator denominator) := by
  let value := QProb.div numeratorSupported.1 denominatorPositive.value denominatorPositive.positive
  refine ⟨value, ?_⟩
  exact trans (divide_congr numeratorSupported.2 denominatorPositive.equivalent)
    (by
      simp only [divide, dif_pos denominatorPositive.positive]
      exact .value (QProb.equiv_refl _))

end ProbabilityResult

namespace Kernel

/-- Every unconditional interventional or observational cylinder has an
explicit supported value, including a zero cylinder.  No positivity of the
observed distribution, compatibility or selection of a latent unit is used. -/
noncomputable def unconditional_supportedAt (model : FiniteLatentSCM S)
    (outcome action : NodeSet S) (reference : S.Assignment) :
    (ProbabilityTerm.kernel ⟨outcome, action, NodeSet.empty⟩).SupportedAt model reference :=
  ⟨((Kernel.mk outcome action NodeSet.empty).distribution model reference).probVal
      (agreesOn outcome reference),
    unconditionalDenote model outcome action reference⟩

/-- A positive unconditional conditioner supplies the corresponding
conditional kernel's support under the same intervention.  Its outcome
numerator may be zero.  This is finite-record normalization, not an
application of do-calculus soundness or observed global positivity. -/
noncomputable def supportedAt_of_positive_unconditional_conditioner
    (model : FiniteLatentSCM S) (outcome action condition : NodeSet S)
    (reference : S.Assignment)
    (positive : ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.kernel ⟨condition, action, NodeSet.empty⟩).denote model reference)) :
    (ProbabilityTerm.kernel ⟨outcome, action, condition⟩).SupportedAt model reference := by
  let kernel : Kernel S := ⟨outcome, action, condition⟩
  let distribution := kernel.distribution model reference
  let numerator := distribution.probVal (kernel.numeratorEvent reference)
  let denominator := distribution.probVal (kernel.conditionEvent reference)
  let actual := ProbabilityResult.PositiveSupportedValue.transport
    (unconditionalDenote model condition action reference) positive
  have denominatorPositive : 0 < denominator.num := by
    cases actual.equivalent with
    | value same => exact (QProb.equiv_num_pos_iff same).mpr actual.positive
  refine ⟨QProb.div numerator denominator denominatorPositive, ?_⟩
  change ProbabilityResult.Equivalent
    (ProbabilityResult.divide (some numerator) (some denominator))
    (some (QProb.div numerator denominator denominatorPositive))
  simp only [ProbabilityResult.divide, dif_pos denominatorPositive]
  exact .value (QProb.equiv_refl _)

/-- The unconditional numerator and denominator used by a displayed
conditional.  The same action remains in both kernels; changing the current
host or resetting to an observational marginal is not part of this syntax. -/
def unconditionalQuotientTerm (kernel : Kernel S) : ProbabilityTerm S :=
  .divide
    (.kernel ⟨NodeSet.union kernel.outcome kernel.condition, kernel.action, NodeSet.empty⟩)
    (.kernel ⟨kernel.condition, kernel.action, NodeSet.empty⟩)

/-- Conditional-to-unconditional quotient agreement at every reference,
including missing conditionals and supported zero outcomes.  The proof
normalizes the two unconditional kernels and aligns their actual cylinder
events, without dividing by a probability assumed positive by the caller. -/
noncomputable def unconditionalQuotient_equivalentAt (model : FiniteLatentSCM S)
    (kernel : Kernel S) (reference : S.Assignment) :
    ProbabilityTerm.EquivalentAt model (.kernel kernel) kernel.unconditionalQuotientTerm reference := by
  let joint := NodeSet.union kernel.outcome kernel.condition
  let distribution := kernel.distribution model reference
  have numerator : QProb.Equiv
      (distribution.probVal (kernel.numeratorEvent reference))
      (distribution.probVal (agreesOn joint reference)) := by
    apply distribution.probVal_congr
    intro sample
    exact (agreesOn_union kernel.outcome kernel.condition reference sample).symm
  have sourceCanonical : ProbabilityResult.Equivalent
      ((ProbabilityTerm.kernel kernel).denote model reference)
      (ProbabilityResult.divide
        (some (distribution.probVal (agreesOn joint reference)))
        (some (distribution.probVal (agreesOn kernel.condition reference)))) := by
    change ProbabilityResult.Equivalent
      (ProbabilityResult.divide
        (some (distribution.probVal (kernel.numeratorEvent reference)))
        (some (distribution.probVal (agreesOn kernel.condition reference)))) _
    exact ProbabilityResult.divide_congr (.value numerator)
      (ProbabilityResult.refl (some (distribution.probVal (agreesOn kernel.condition reference))))
  have quotientCanonical : ProbabilityResult.Equivalent
      (kernel.unconditionalQuotientTerm.denote model reference)
      (ProbabilityResult.divide
        (some (distribution.probVal (agreesOn joint reference)))
        (some (distribution.probVal (agreesOn kernel.condition reference)))) :=
    ProbabilityResult.divide_congr
      (unconditionalDenote model joint kernel.action reference)
      (unconditionalDenote model kernel.condition kernel.action reference)
  exact ProbabilityResult.trans sourceCanonical (ProbabilityResult.symm quotientCanonical)

end Kernel

namespace ProbabilityTerm

/-- Support of a finite marginal is supplied only at the actual enumerated
variants.  Zero summands are allowed, and no value is chosen from a mere
existence statement: each variant supplies its constructive support datum. -/
noncomputable def marginalize_supportedAt_of_mem (model : FiniteLatentSCM S)
    (nodes : NodeSet S) (term : ProbabilityTerm S) (reference : S.Assignment)
    (summands : forall variant, variant ∈ marginalAssignments S nodes reference →
      term.SupportedAt model variant) :
    (ProbabilityTerm.marginalize nodes term).SupportedAt model reference :=
  ProbabilityResult.sum_map_supported_of_mem (marginalAssignments S nodes reference)
    (fun variant => term.denote model variant) summands

end ProbabilityTerm
end Causality
end Thesis
