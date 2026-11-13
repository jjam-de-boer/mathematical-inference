import Thesis.CausalTransport.NativeDemandFrames

namespace Thesis.Causality.NativeDemandEncoding.Frame

open Probability NativeDemandTyping

/-!
# A supported filled source suffices for one checked frame replacement

The inner proof must pass its full native checker at the frame's actual
routed demand. Native soundness on the matching graph then preserves the
hole's status at those cells. A structural status calculation lifts that
agreement through each of the ten frame forms. It asserts only status and
support preservation; equal type tables never create a causal equation.

Marginalization retains every substituted reference, including null values.
Fixed evaluation retains its fixed reference. A weighted factor is inspected
only under a positive fixed weight; a zero weight preserves zero even when
the factor is undefined. Changing the weight preserves the same factor mask.
Division retains the denominator's positivity requirement. Literal siblings
are unchanged, and source support still has to supply their required values.

Thus the preceding two-endpoint lift theorem now needs only the supported
filled source in addition to the checked inner proof. The conclusion also
certifies the common encoded frame. This is a single-frame theorem, not a
global rewrite-closure, normalization, reachability or stopping result.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- Pure availability transport. The hypothesis supplies status agreement
only where the hole is needed; it does not claim equality of probabilities. -/
private theorem status_eq_of_routed (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (requested : Demand profiles)
    (same : ∀ index reference, frameDemand profiles frame requested index reference = true →
      termStatus profiles left index reference = termStatus profiles right index reference)
    (index : Fin profiles.length) (reference : S.Assignment) (needed : requested index reference = true) :
    termStatus profiles (frame.fill left) index reference = termStatus profiles (frame.fill right) index reference := by
  cases frame with
  | marginalize nodes =>
      change ProbabilityResult.Status.sum _ = ProbabilityResult.Status.sum _
      apply congrArg ProbabilityResult.Status.sum
      apply List.map_congr_left
      intro variant member
      exact same index variant ((marginalDemand_exact profiles requested nodes index variant).mpr ⟨reference, needed, member⟩)
  | evaluateAt fixed =>
      apply same index fixed
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl,
        List.any_eq_true.mpr ⟨reference, S.assignmentEnumeration_complete reference, needed⟩⟩
  | weightedRight weight =>
      change ProbabilityResult.Status.weightedMultiply (termStatus profiles weight index reference) _ =
        ProbabilityResult.Status.weightedMultiply (termStatus profiles weight index reference) _
      cases weightStatus : termStatus profiles weight index reference with
      | undefined => rfl
      | zero => rfl
      | positive =>
          apply same index reference
          change (requested index reference && decide (termStatus profiles weight index reference = .positive)) = true
          rw [needed, weightStatus]
          rfl
  | addLeft fixed | addRight fixed | multiplyLeft fixed | multiplyRight fixed | weightedLeft fixed | divideLeft fixed | divideRight fixed =>
      have hole := same index reference needed
      simp only [ProbabilityTermFrame.fill, termStatus, hole]

/-- Agreement comes from the supplied causal proof's actual native values,
not from an assumed identity between expressions with matching metadata. -/
theorem filled_status_eq_of_checked (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true)
    (index : Fin profiles.length) (reference : S.Assignment) (needed : requested index reference = true) :
    termStatus profiles (frame.fill left) index reference = termStatus profiles (frame.fill right) index reference :=
  status_eq_of_routed profiles frame requested
    (fun row value active => status_eq_of_checked profiles _ derivation accepted row value active) index reference needed

theorem filled_check_eq_of_checked (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true) :
    NativeDemandTyping.check profiles (frame.fill left) requested = NativeDemandTyping.check profiles (frame.fill right) requested := by
  rw [check_status, check_status]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro supported
    apply (allNeeded_exact ..).mpr
    intro index reference needed
    rw [← filled_status_eq_of_checked profiles frame derivation requested accepted index reference needed]
    exact (allNeeded_exact ..).mp supported index reference needed
  · intro supported
    apply (allNeeded_exact ..).mpr
    intro index reference needed
    rw [filled_status_eq_of_checked profiles frame derivation requested accepted index reference needed]
    exact (allNeeded_exact ..).mp supported index reference needed

theorem right_checked_of_left (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true)
    (source : NativeDemandTyping.check profiles (frame.fill left) requested = true) :
    NativeDemandTyping.check profiles (frame.fill right) requested = true :=
  (filled_check_eq_of_checked profiles frame derivation requested accepted).symm.trans source

/-- Reconstruct the entire original lifted support tree from one supported
filled endpoint. No sibling or denominator obligation is silently omitted. -/
theorem lift_checked_of_left (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true)
    (source : NativeDemandTyping.check profiles (frame.fill left) requested = true) :
    checkDerivation profiles requested (frame.lift derivation) = true :=
  lift_checked profiles frame derivation requested accepted source
    (right_checked_of_left profiles frame derivation requested accepted source)

theorem lift_check_iff_left (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right) (requested : Demand profiles) :
    checkDerivation profiles requested (frame.lift derivation) = true ↔
      checkDerivation profiles (frameDemand profiles frame requested) derivation = true ∧
        NativeDemandTyping.check profiles (frame.fill left) requested = true := by
  constructor
  · intro accepted
    have parts := (lift_check_iff profiles frame derivation requested).mp accepted
    exact ⟨parts.1, (check_fill profiles frame left requested).symm.trans parts.2.1⟩
  · rintro ⟨inner, source⟩
    exact lift_checked_of_left profiles frame derivation requested inner source

/-- The same canonical encoded frame works at both endpoints, including
its complete literal siblings and positive-only factor annotations. -/
theorem encoded_right_checked_of_left (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true)
    (source : ((encode profiles frame left requested).fill (Term.encode profiles left (frameDemand profiles frame requested))).check = true) :
    ((encode profiles frame left requested).fill (Term.encode profiles right (frameDemand profiles frame requested))).check = true :=
  (check_fill_right profiles frame derivation requested accepted).trans
    (right_checked_of_left profiles frame derivation requested accepted ((check_fill profiles frame left requested).symm.trans source))

end Thesis.Causality.NativeDemandEncoding.Frame
