import Thesis.CausalTransport.NativeDemandSteps
import Thesis.CausalTransport.NativeFrameRecovery

namespace Thesis.Causality.NativeDemandEncoding.Step

open Probability NativeDemandTyping

/-!
# Valid sources are preserved by the checked elementary-step grammar

Primitive leaves already carry their actual graph and full native support
certificates at their labelled demand. A valid source fixes that demand and
every enclosing frame annotation. The frame-recovery theorem therefore lets
the checked equation travel through arbitrarily many literal frames without
first assuming support or coherence of the target.

The induction preserves validity in both directions, so explicit reversal
retains the same guarantee. Strict multiplication commutativity and
associativity preserve the canonical masks and require all operand support.
Weighted multiplication keeps its asymmetric positive-factor rule; no AC
rule is supplied for it. Fixed and marginal references remain demanded, and
even unused subtrees retain their complete coherent annotation trees.

These statements concern the existing certified `Step` grammar on the
supplied profile family. Arbitrary raw atoms, unchecked proof detours and
metadata-only equations do not acquire certificates. The Boolean checker is
unchanged. No ground rewrite relation, path search, normalization, universal
formula-coverage theorem or stopping result is introduced.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}
variable {profiles : List (NativeTemplateInstance P)}

private theorem demand_of_annotations (term : Term profiles) (requested : Demand profiles)
    (annotated : term.checkAnnotations requested = true) : requested = term.demand := by
  have same := congrArg Term.demand ((Term.checkAnnotations_exact term requested).mp annotated)
  simpa only [Term.demand_encode] using same

private theorem check_of_endpoints (step : Step profiles) (requested : Demand profiles)
    (source : step.left.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles step.left.erase requested = true)
    (target : step.right.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles step.right.erase requested = true) :
    step.check requested = true :=
  Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨source.1, target.1⟩,
    Bool.and_eq_true_iff.mpr ⟨source.2, target.2⟩⟩

private theorem fill_checks (frame : Frame profiles) (step : Step profiles) (requested : Demand profiles)
    (accepted : step.check (frameDemand profiles frame.erase requested) = true)
    (source : (frame.fill step.left).checkAnnotations requested = true ∧
      NativeDemandTyping.check profiles (frame.fill step.left).erase requested = true) :
    (frame.fill step.right).checkAnnotations requested = true ∧
      NativeDemandTyping.check profiles (frame.fill step.right).erase requested = true :=
  Frame.fill_checks_of_checked frame step.erase.toDerivation requested (step.erase_checked _ accepted) source
    (step.endpoints_canonical _ accepted).2

/-- Every finite nesting is covered without a depth bound. Source and
target annotations refer to the application's same explicit outer demand.
The leaf certificates, rather than equal status tables, supply the equations. -/
theorem endpoints_valid_iff (step : Step profiles) (requested : Demand profiles) :
    (step.left.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles step.left.erase requested = true) ↔
      (step.right.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles step.right.erase requested = true) := by
  induction step generalizing requested with
  | primitive entry =>
      constructor
      · intro source
        have same : requested = entry.demand := by
          simpa only [left, Term.demand_encode] using demand_of_annotations _ requested source.1
        cases same
        refine ⟨Term.checkAnnotations_encode profiles entry.checked.right entry.demand, ?_⟩
        simpa only [right, Term.erase_encode] using (Bool.and_eq_true_iff.mp entry.endpoints_checked).2
      · intro source
        have same : requested = entry.demand := by
          simpa only [right, Term.demand_encode] using demand_of_annotations _ requested source.1
        cases same
        refine ⟨Term.checkAnnotations_encode profiles entry.checked.left entry.demand, ?_⟩
        simpa only [left, Term.erase_encode] using (Bool.and_eq_true_iff.mp entry.endpoints_checked).1
  | multiplyComm actual first second =>
      simp only [left, right, Term.checkAnnotations, Term.erase, NativeDemandTyping.check,
        Bool.and_eq_true_iff, and_assoc, and_left_comm, and_comm]
  | multiplyAssoc actual first second third =>
      simp only [left, right, Term.checkAnnotations, Term.erase, NativeDemandTyping.check,
        Bool.and_eq_true_iff, and_assoc, and_left_comm, and_comm, and_self]
  | symm inner ih => exact (ih requested).symm
  | under frame inner ih =>
      constructor
      · intro source
        have innerSource := Frame.inner_checks_of_fill frame inner.left requested source
        have innerTarget := (ih _).mp innerSource
        exact fill_checks frame inner requested (check_of_endpoints inner _ innerSource innerTarget) source
      · intro source
        have innerSource := Frame.inner_checks_of_fill frame inner.right requested source
        have innerTarget := (ih _).mpr innerSource
        exact fill_checks frame (.symm inner) requested (check_of_endpoints (.symm inner) _ innerSource innerTarget) source

/-- One valid source suffices because all primitive leaves are already
certified and every frame is recovered from that source. This is not a rule
for arbitrary raw derivations with possibly unsupported intermediate terms. -/
theorem check_iff_left (step : Step profiles) (requested : Demand profiles) :
    step.check requested = true ↔
      step.left.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles step.left.erase requested = true := by
  constructor
  · intro accepted
    have parts := Bool.and_eq_true_iff.mp accepted
    exact ⟨(Bool.and_eq_true_iff.mp parts.1).1, (Bool.and_eq_true_iff.mp parts.2).1⟩
  · intro source
    exact check_of_endpoints step requested source ((endpoints_valid_iff step requested).mp source)

theorem check_iff_right (step : Step profiles) (requested : Demand profiles) :
    step.check requested = true ↔
      step.right.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles step.right.erase requested = true :=
  (check_iff_left step requested).trans (endpoints_valid_iff step requested)

/-- Exact Boolean equality retains the explicit root request and full
source annotation tree, including masks beneath skipped zero-weight factors. -/
theorem check_eq_left (step : Step profiles) (requested : Demand profiles) :
    step.check requested = (step.left.checkAnnotations requested && NativeDemandTyping.check profiles step.left.erase requested) :=
  Bool.eq_iff_iff.mpr ((check_iff_left step requested).trans Bool.and_eq_true_iff.symm)

theorem check_eq_right (step : Step profiles) (requested : Demand profiles) :
    step.check requested = (step.right.checkAnnotations requested && NativeDemandTyping.check profiles step.right.erase requested) :=
  Bool.eq_iff_iff.mpr ((check_iff_right step requested).trans Bool.and_eq_true_iff.symm)

/-- Recover acceptance of the original recursive support checker from
the valid encoded source. No replacement semantic law is assumed. -/
theorem erase_checked_of_left (step : Step profiles) (requested : Demand profiles)
    (source : step.left.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles step.left.erase requested = true) :
    checkDerivation profiles requested step.erase.toDerivation = true :=
  step.erase_checked requested ((check_iff_left step requested).mpr source)

end Thesis.Causality.NativeDemandEncoding.Step
