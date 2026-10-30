import Thesis.CausalTransport.NativeDemandPaths
import Thesis.CausalTransport.NativeStepEncoding

namespace Thesis.Causality.NativeDemandEncoding

open Probability NativeDemandTyping

/-!
# One supported raw path has one faithful typed encoding

Every vertex is encoded canonically at the same outer demand. The step
encoder's literal endpoint equalities join adjacent cells; type or status
agreement alone is never used as a join. Reindexing transports only those
literal equalities, and erasure retains the supplied path's actual steps.

The original vertex scan supplies both endpoints of each elementary step,
including the source of an empty tail. Thus supported paths need no stronger
positivity condition. The same path and demand table serve the entire profile
family, preserving the earlier frame rules for zero-weight branches.

This is conversion of a supplied finite proof presentation, with an opt-in
support check. It is not a search for a path, a parser for untrusted external
codes, an AC normalizer, or a universal formula-coverage/stopping result.
The separate top-level `actionOne` wrapper remains outside this path grammar.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

namespace Path

theorem rawCheck_step (profiles : List (NativeTemplateInstance P)) {first middle last : ProbabilityTerm S}
    (step : DoCalculusRewriteStep P.observedGraph first middle) (tail : DoCalculusRewritePath P.observedGraph middle last)
    (requested : Demand profiles) (accepted : rawCheck profiles (.cons step tail) requested = true) :
    checkDerivation profiles requested step.toDerivation = true := by
  have both := Bool.and_eq_true_iff.mp ((rawCheck_cons profiles step tail requested).symm.trans accepted)
  rw [Step.raw_check_eq_endpoints]
  exact Bool.and_eq_true_iff.mpr ⟨both.1, rawCheck_first profiles tail requested both.2⟩

/-- Only the supplied finite path is traversed. Literal endpoint proofs
transport the tail to the encoded step's target and the head to its canonical
source; no proof is selected separately for individual profiles. -/
def encode (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles)
    (accepted : rawCheck profiles path requested = true) :
    Path profiles (Term.encode profiles first requested) (Term.encode profiles last requested) :=
  match path with
  | .nil term => .nil (Term.encode profiles term requested)
  | .cons step tail =>
      let both := Bool.and_eq_true_iff.mp ((rawCheck_cons profiles step tail requested).symm.trans accepted)
      let edgeAccepted := rawCheck_step profiles step tail requested accepted
      let encodedStep := Step.encode profiles step requested edgeAccepted
      let endpoints := Step.encode_endpoints profiles step requested edgeAccepted
      let encodedTail := encode profiles tail requested both.2
      (Path.cons encodedStep (encodedTail.reindex endpoints.2.symm rfl)).reindex endpoints.1 rfl

theorem encode_checked (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles)
    (accepted : rawCheck profiles path requested = true) : (encode profiles path requested accepted).check requested = true := by
  induction path generalizing requested with
  | nil term =>
      change ((Term.encode profiles term requested).checkAnnotations requested &&
        NativeDemandTyping.check profiles (Term.encode profiles term requested).erase requested) = true
      rw [Term.checkAnnotations_encode, Term.erase_encode, Bool.true_and]
      exact (rawCheck_nil profiles term requested).symm.trans accepted
  | cons step tail ih =>
      simp only [encode, check_reindex, check_cons, Step.encode_checked, ih, Bool.true_and]

/- The following private output packages keep endpoint transports visible
while proving the exact round-trip. They are not additional input leaves:
only `Step` supplies equations and only `Path.cons` composes them. -/
private abbrev RawStepData (projection : FiniteLatentProjection S) :=
  Σ first last : ProbabilityTerm S, DoCalculusRewriteStep projection.observedGraph first last

private abbrev RawPathData (projection : FiniteLatentProjection S) :=
  Σ first last : ProbabilityTerm S, DoCalculusRewritePath projection.observedGraph first last

private def prependData (step : RawStepData P) (tail : RawPathData P) (joined : step.2.1 = tail.1) : RawPathData P :=
  ⟨step.1, tail.2.1, .cons step.2.2
    (cast (congrArg (fun source => DoCalculusRewritePath P.observedGraph source tail.2.1) joined.symm) tail.2.2)⟩

private theorem prependData_congr {step otherStep : RawStepData P} {tail otherTail : RawPathData P}
    (step_eq : step = otherStep) (tail_eq : tail = otherTail)
    (joined : step.2.1 = tail.1) (otherJoined : otherStep.2.1 = otherTail.1) :
    prependData step tail joined = prependData otherStep otherTail otherJoined := by
  cases step_eq
  cases tail_eq
  rfl

private theorem transportedStepData {first last source target : ProbabilityTerm S}
    (step : DoCalculusRewriteStep P.observedGraph first last) (source_eq : first = source) (target_eq : last = target) :
    (⟨source, target, cast
      ((congrArg (fun term => DoCalculusRewriteStep P.observedGraph term last) source_eq).trans
        (congrArg (DoCalculusRewriteStep P.observedGraph source) target_eq)) step⟩ : RawStepData P) =
      ⟨first, last, step⟩ := by
  cases source_eq
  cases target_eq
  rfl

private theorem indexedStepData {profiles : List (NativeTemplateInstance P)} (step : Step profiles) :
    (⟨step.left.erase, step.right.erase, step.erase⟩ : RawStepData P) = step.eraseData :=
  transportedStepData step.eraseData.2.2 step.eraseData_endpoints.1 step.eraseData_endpoints.2

private theorem eraseData_cons {profiles : List (NativeTemplateInstance P)} (step : Step profiles)
    {last : Term profiles} (tail : Path profiles step.right last) :
    (Path.cons step tail).eraseData =
      prependData (⟨step.left.erase, step.right.erase, step.erase⟩ : RawStepData P) tail.eraseData rfl := rfl

/-- Erasure recovers the original finite path, including every actual step
and intermediate term. It does not merely recover a proof of the same final
equation, a path of the same length, or a path chosen per profile. -/
theorem eraseData_encode (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles)
    (accepted : rawCheck profiles path requested = true) :
    (encode profiles path requested accepted).eraseData = ⟨first, last, path⟩ := by
  induction path generalizing requested with
  | nil term =>
      let build (current : ProbabilityTerm S) : RawPathData P := ⟨current, current, .nil current⟩
      change build (Term.encode profiles term requested).erase = build term
      exact congrArg build (Term.erase_encode profiles term requested)
  | cons step tail ih =>
      have both := Bool.and_eq_true_iff.mp ((rawCheck_cons profiles step tail requested).symm.trans accepted)
      have edgeAccepted := rawCheck_step profiles step tail requested accepted
      let encodedStep := Step.encode profiles step requested edgeAccepted
      let endpoints := Step.encode_endpoints profiles step requested edgeAccepted
      let encodedTail := encode profiles tail requested both.2
      change ((Path.cons encodedStep (encodedTail.reindex endpoints.2.symm rfl)).reindex endpoints.1 rfl).eraseData = _
      rw [eraseData_reindex, eraseData_cons]
      exact prependData_congr
        ((indexedStepData encodedStep).trans (Step.eraseData_encode profiles step requested edgeAccepted))
        ((eraseData_reindex encodedTail endpoints.2.symm rfl).trans (ih requested both.2)) rfl rfl

/-- Checking a supplied raw path includes its initial vertex even when
there are no steps. `none` reports this path's support failure, not failure
of identification or failure to find some other path. -/
def encode? (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles) :
    Option (Path profiles (Term.encode profiles first requested) (Term.encode profiles last requested)) :=
  if accepted : rawCheck profiles path requested = true then some (encode profiles path requested accepted) else none

theorem encode?_isSome (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles) :
    (encode? profiles path requested).isSome = checkDerivation profiles requested path.toDerivation := by
  rw [← rawCheck_eq_toDerivation]
  unfold encode?
  split
  · next accepted => simp only [Option.isSome_some, accepted]
  · next rejected =>
      cases checked : rawCheck profiles path requested with
      | false => rfl
      | true => exact False.elim (rejected checked)

theorem encode?_checked (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles)
    (encoded : Path profiles (Term.encode profiles first requested) (Term.encode profiles last requested))
    (returned : encode? profiles path requested = some encoded) : encoded.check requested = true := by
  unfold encode? at returned
  split at returned
  · next accepted =>
      cases Option.some.inj returned
      exact encode_checked profiles path requested accepted
  · simp only [reduceCtorEq] at returned

end Path
end Thesis.Causality.NativeDemandEncoding
