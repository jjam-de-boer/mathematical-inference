import Thesis.Causality.DerivationContext
import Thesis.CausalTransport.NativeDerivationSupportCheck

namespace Thesis.Causality

open Probability

/-!
# Same-endpoint replacement preserves enclosing native proof support

Keep an actual replacement derivation with exactly the original subproof's
source and target. If it passes wherever the old subproof passes, at every
reference of a fixed native model, every enclosing one-hole proof preserves
acceptance. Applying the theorem to each supplied profile retains one common
replacement proof; it does not choose a different proof per hidden model.

The proof is structural monotonicity of the full support checker. Endpoints
and fixed siblings remain literal, including the source weight that selects
a weighted congruence's positive branch. Marginalization uses the hypothesis
at every substituted assignment, and fixed evaluation uses its own reference.
A genuinely zero weight still skips its factor; no global positivity premise
is added. The hypothesis concerns the full check, not the conditional demand
that is vacuous when an endpoint is undefined.

This is a local replacement theorem, not pruning, finite-state saturation,
an exporter, or a universal stopping result. Different endpoint expressions
cannot be substituted merely because their support tables agree. The last
corollary reconstructs the old recursive support data using existing checked
values; it adds no semantic equation, choice or new probability assumption.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S} {G : ObservedGraph S}

namespace DoCalculusDerivationContext

private theorem and_mono {before after fixedBefore fixedAfter : Bool}
    (first : before = true → after = true) (second : fixedBefore = true → fixedAfter = true)
    (accepted : (before && fixedBefore) = true) : (after && fixedAfter) = true :=
  Bool.and_eq_true_iff.mpr
    ⟨first (Bool.and_eq_true_iff.mp accepted).1, second (Bool.and_eq_true_iff.mp accepted).2⟩

private theorem positive_branch_mono {condition : Prop} [Decidable condition] {before after : Bool}
    (improves : before = true → after = true) :
    (if condition then before else true) = true → (if condition then after else true) = true := by
  cases ‹Decidable condition› with
  | isTrue active => simpa only [if_pos active] using improves
  | isFalse inactive => simp only [if_neg inactive, implies_true]

/-- Replace one distinguished subproof without losing any accepted enclosing
application. Quantification over all references is essential: the context may
change the reference or inspect an entire finite marginal family. Literal
endpoint equality is carried by the context's indices, not inferred from
numerical or three-valued support metadata. -/
theorem check_mono {holeLeft holeRight left right : ProbabilityTerm S}
    (context : DoCalculusDerivationContext G holeLeft holeRight left right)
    (model : FiniteHiddenDAGSCM S P)
    (original replacement : DoCalculusDerivation G holeLeft holeRight)
    (improves : ∀ reference, HiddenDAGLocalDerivationSupport.check model reference original = true →
      HiddenDAGLocalDerivationSupport.check model reference replacement = true)
    (reference : S.Assignment)
    (accepted : HiddenDAGLocalDerivationSupport.check model reference (context.fill original) = true) :
    HiddenDAGLocalDerivationSupport.check model reference (context.fill replacement) = true := by
  induction context generalizing reference with
  | hole => exact improves reference accepted
  | symm inner ih => exact and_mono id (ih reference) accepted
  | transLeft inner fixed ih => exact and_mono id (and_mono (ih reference) id) accepted
  | transRight fixed inner ih => exact and_mono id (and_mono id (ih reference)) accepted
  | marginalize nodes inner ih =>
      apply and_mono id ?_ accepted
      intro allChecked
      exact List.all_eq_true.mpr (fun variant member => ih variant (List.all_eq_true.mp allChecked variant member))
  | evaluateAt fixed inner ih => exact and_mono id (ih fixed) accepted
  | addLeft inner fixed ih => exact and_mono id (and_mono (ih reference) id) accepted
  | addRight fixed inner ih => exact and_mono id (and_mono id (ih reference)) accepted
  | multiplyLeft inner fixed ih => exact and_mono id (and_mono (ih reference) id) accepted
  | multiplyRight fixed inner ih => exact and_mono id (and_mono id (ih reference)) accepted
  | weightedLeft inner fixed ih => exact and_mono id (and_mono (ih reference) id) accepted
  | weightedRight fixed inner ih =>
      exact and_mono id (and_mono id (positive_branch_mono (ih reference))) accepted
  | divideLeft inner fixed ih => exact and_mono id (and_mono (ih reference) id) accepted
  | divideRight fixed inner ih => exact and_mono id (and_mono id (ih reference)) accepted
  | eqCongr sameLeft sameRight inner ih => exact and_mono id (ih reference) accepted

/-- Recover the established recursive support witnesses after replacement.
Each witness is rebuilt from the same model's actual evaluation; no value or
proof is selected from an existential or borrowed from a support profile. -/
noncomputable def support_mono {holeLeft holeRight left right : ProbabilityTerm S}
    (context : DoCalculusDerivationContext G holeLeft holeRight left right)
    (model : FiniteHiddenDAGSCM S P)
    (original replacement : DoCalculusDerivation G holeLeft holeRight)
    (improves : ∀ reference, HiddenDAGLocalDerivationSupport.check model reference original = true →
      HiddenDAGLocalDerivationSupport.check model reference replacement = true)
    (reference : S.Assignment)
    (supported : HiddenDAGLocalDerivationSupport model reference (context.fill original)) :
    HiddenDAGLocalDerivationSupport model reference (context.fill replacement) :=
  HiddenDAGLocalDerivationSupport.ofCheck model reference (context.fill replacement)
    (context.check_mono model original replacement improves reference
      (HiddenDAGLocalDerivationSupport.check_of_supported model reference (context.fill original) supported))

end DoCalculusDerivationContext
end Thesis.Causality
