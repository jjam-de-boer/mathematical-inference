import Thesis.Causality.Semantics

namespace Thesis
namespace Causality

/-!
# Guarded products in the existing probability-expression language

The zero-weight guard is part of `ProbabilityTerm`, not an evaluator-only
convention or a replacement for strict multiplication.  Consequently finite
marginalization, literal syntax comparison, observational invariance, and
the source-table interpretation can all see the same operation.

This module lifts the model-independent local-support laws to terms.  Support
of the weight is always required.  Support or equality of the factor is
required only where that weight has positive mass; no value is selected for
an undefined conditional at a zero cell.  The positive branch carries its
explicit rational witness in `Type`, just like ordinary `SupportedAt`.

These are semantic constructors for the support-aware compiler.  They do not
yet assert that a graphical ID success has sufficient observable overlap,
and they do not extend the old everywhere-positive completeness statement.
-/

namespace ProbabilityTerm

/-- Finite marginalization of directed weighted contributions.  Keeping this
as ordinary `marginalize` around the new product preserves the signature's
established substitution enumeration and avoids a second summation syntax. -/
def weightedMarginalize (nodes : NodeSet S) (weight factor : ProbabilityTerm S) :
    ProbabilityTerm S :=
  .marginalize nodes (.weightedMultiply weight factor)

/-- A guarded sum is observational syntax only when both displayed inputs
are observational syntax.  Zero-weight branches do not permit hidden actions
to be disguised as an action-free formula. -/
theorem weightedMarginalize_actionFree (nodes : NodeSet S)
    {weight factor : ProbabilityTerm S}
    (weightFree : weight.ActionFree) (factorFree : factor.ActionFree) :
    (weightedMarginalize nodes weight factor).ActionFree :=
  ⟨weightFree, factorFree⟩

/-- The expression constructor uses exactly the guarded finite algebra, on
exactly the original finite substitution list. -/
theorem weightedMarginalize_denote (model : FiniteLatentSCM S)
    (nodes : NodeSet S) (weight factor : ProbabilityTerm S)
    (reference : S.Assignment) :
    (weightedMarginalize nodes weight factor).denote model reference =
      ProbabilityResult.weightedSum (marginalAssignments S nodes reference)
        (fun variant => weight.denote model variant)
        (fun variant => factor.denote model variant) := rfl

/-- A product's complete value needs the factor only at positive weight.
The factor is left undefined at a zero weight, rather than separately supplied
with a fictitious support witness. -/
noncomputable def weightedMultiply_supportedAt
    {model : FiniteLatentSCM S} {reference : S.Assignment}
    {weight factor : ProbabilityTerm S}
    (weightSupported : weight.SupportedAt model reference)
    (factorOnPositive :
      ProbabilityResult.PositiveSupportedValue (weight.denote model reference) ->
        factor.SupportedAt model reference) :
    (ProbabilityTerm.weightedMultiply weight factor).SupportedAt model reference :=
  ProbabilityResult.weightedMultiply_supported weightSupported factorOnPositive

/-- Guarded congruence preserves the support domain and rational value of the
whole contribution.  Its factor comparison is genuinely local: there is no
comparison obligation at zero weight, even if one factor is undefined. -/
def weightedMultiply_congrAt_on_positive
    {model : FiniteLatentSCM S} {reference : S.Assignment}
    {weight weight' factor factor' : ProbabilityTerm S}
    (weightsEquivalent : EquivalentAt model weight weight' reference)
    (factorsOnPositive :
      ProbabilityResult.PositiveSupportedValue (weight.denote model reference) ->
        EquivalentAt model factor factor' reference) :
    EquivalentAt model (.weightedMultiply weight factor)
      (.weightedMultiply weight' factor') reference :=
  ProbabilityResult.weightedMultiply_congr_on_positive
    weightsEquivalent factorsOnPositive

/-- Every enumerated weight is defined, but only its positive branches need
a defined factor.  Unlisted assignments impose no local support obligation. -/
noncomputable def weightedMarginalize_supportedAt
    {model : FiniteLatentSCM S} (nodes : NodeSet S)
    (weight factor : ProbabilityTerm S) (reference : S.Assignment)
    (weightsSupported : forall variant,
      variant ∈ marginalAssignments S nodes reference ->
        weight.SupportedAt model variant)
    (factorsOnPositive : forall variant,
      variant ∈ marginalAssignments S nodes reference ->
        ProbabilityResult.PositiveSupportedValue (weight.denote model variant) ->
          factor.SupportedAt model variant) :
    (weightedMarginalize nodes weight factor).SupportedAt model reference :=
  ProbabilityResult.weightedSum_supported_of_mem
    (marginalAssignments S nodes reference)
    (fun variant => weight.denote model variant)
    (fun variant => factor.denote model variant)
    weightsSupported factorsOnPositive

/-- Weighted marginals compare factors only at the listed positive weights.
This is the congruence boundary needed when recursively compiling a partial
conditional factor, without asking that it exist on null conditioning cells. -/
noncomputable def weightedMarginalize_congrAt_on_positive
    {model : FiniteLatentSCM S} (nodes : NodeSet S)
    (weight weight' factor factor' : ProbabilityTerm S) (reference : S.Assignment)
    (weightsEquivalent : forall variant,
      variant ∈ marginalAssignments S nodes reference ->
        EquivalentAt model weight weight' variant)
    (factorsOnPositive : forall variant,
      variant ∈ marginalAssignments S nodes reference ->
        ProbabilityResult.PositiveSupportedValue (weight.denote model variant) ->
          EquivalentAt model factor factor' variant) :
    EquivalentAt model (weightedMarginalize nodes weight factor)
      (weightedMarginalize nodes weight' factor') reference :=
  ProbabilityResult.weightedSum_congr_on_positive_mem
    (marginalAssignments S nodes reference)
    (fun variant => weight.denote model variant)
    (fun variant => weight'.denote model variant)
    (fun variant => factor.denote model variant)
    (fun variant => factor'.denote model variant)
    weightsEquivalent factorsOnPositive

end ProbabilityTerm
end Causality
end Thesis
