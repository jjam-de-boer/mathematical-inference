import Thesis.Causality.SupportAwareSemantics

namespace Thesis
namespace Causality
namespace Examples
namespace LocalWeightedSupport

open Probability ProbabilityResult

/-!
# Exact zero-support regressions for weighted finite expressions

These small computations distinguish a missing factor under zero mass from
a missing factor under positive mass.  They also retain the old strict
semantics as a comparison, rather than globally changing how undefined
probabilities are interpreted.  Every displayed equation is kernel reduction
on finite rational data; no native decision procedure or extra axiom is used.

This is the algebraic prerequisite for the zero-containing-distribution
extension, not a claim that its causal identification compiler is complete.
-/

def half : QProb := ⟨1, 2, by decide⟩

def weight : Bool -> Result
  | false => some QProb.zero
  | true => some half

def factor : Bool -> Result
  | false => none
  | true => some half

/-- The zero-weight branch is skipped and the positive branch contributes
`(1/2) * (1/2)`.  Its undefined zero-weight conditional is never filled in. -/
theorem weighted_sum_skips_zero_branch :
    weightedSum [false, true] weight factor = some (⟨1, 4, by decide⟩ : QProb) := rfl

/-- The former strict sum still propagates that missing conditional.  Keeping
this equation true prevents a silent change to existing expression semantics. -/
theorem strict_sum_remains_undefined :
    sum ([false, true].map (fun value => multiply (weight value) (factor value))) =
      none := rfl

/-- Zero-weight skipping cannot repair a missing positive-weight factor. -/
theorem positive_missing_factor_remains_undefined :
    weightedSum [false, true] weight (fun _ => none) = none := rfl

/-- An undefined weight never authorizes skipping, even with a zero factor. -/
theorem undefined_weight_remains_undefined :
    weightedMultiply none (some QProb.zero) = none := rfl

/-- Noncanonical zero presentations choose exactly the same skipped branch.
The operation is not sensitive to a rational's denominator presentation. -/
theorem noncanonical_zero_skips_undefined :
    weightedMultiply (some (⟨0, 7, by decide⟩ : QProb)) none = some QProb.zero := rfl

/-- Strict positive multiplication is unchanged by the weighted guard. -/
theorem supported_positive_product :
    weightedMultiply (some half) (some half) = some (⟨1, 4, by decide⟩ : QProb) := rfl

end LocalWeightedSupport
end Examples
end Causality
end Thesis
