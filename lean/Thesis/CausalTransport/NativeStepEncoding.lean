import Thesis.CausalTransport.NativeDemandSteps

namespace Thesis.Causality.NativeDemandEncoding

open Probability ProbabilityCode NativeDemandTyping

/-!
# Supported raw elementary steps have faithful encoded representatives

The encoder follows a supplied elementary step, rather than searching for
an equation from endpoint metadata. Its one primitive leaf is constructed
as an actual member of the finite checked catalogue; strict multiplication
uses its two existing schemas. Reversal remains explicit. Under a frame,
the original support check supplies the pulled-back inner obligation, and
the single-frame bridge gives the same literal frame at both endpoints.

One encoded step is produced for the entire supplied profile family. In
particular, changing a weight cannot pick a different fixed factor or mask
in different models. Defined zero weights suppress only factor demand, not
factor syntax. No stronger positivity or reference-support premise is added.

This correspondence concerns elementary steps in the existing proof
language. It introduces no path type, AC normalizer, formula selector or
universal search bound, and does not internalize the separate `actionOne`
wrapper as a probability/do-calculus atom.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

namespace Step

/-- Primitive codes are computed from the actual leaf. AC is the only
code-free case and keeps arbitrary literal operand trees. -/
def encodeAtom (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested leaf.toDerivation = true) : Step profiles :=
  match encoded : leaf.primitiveCode? with
  | some (kind, code) => .primitive (.ofAtom profiles requested leaf kind code encoded accepted)
  | none => by
      cases leaf with
      | doRule application => cases application <;> contradiction
      | marginalization | conditioning | chain | weightedChain => contradiction
      | multiplyComm first second => exact .multiplyComm requested (Term.encode profiles first requested) (Term.encode profiles second requested)
      | multiplyAssoc first second third =>
          exact .multiplyAssoc requested (Term.encode profiles first requested)
            (Term.encode profiles second requested) (Term.encode profiles third requested)

theorem encodeAtom_endpoints (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested leaf.toDerivation = true) :
    (encodeAtom profiles leaf requested accepted).left = Term.encode profiles left requested ∧
      (encodeAtom profiles leaf requested accepted).right = Term.encode profiles right requested := by
  cases leaf with
  | doRule application => cases application <;> exact ⟨rfl, rfl⟩
  | marginalization | conditioning | chain | weightedChain | multiplyComm | multiplyAssoc => exact ⟨rfl, rfl⟩

/-- Erasure returns the actual supplied atomic constructor and proof data,
not another equation with merely matching endpoint types. -/
theorem eraseData_encodeAtom (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested leaf.toDerivation = true) :
    (encodeAtom profiles leaf requested accepted).eraseData = ⟨left, right, .atom leaf⟩ := by
  cases leaf with
  | doRule application => cases application <;> rfl
  | marginalization | conditioning | chain | weightedChain => rfl
  | multiplyComm first second =>
      let build (a b : ProbabilityTerm S) : (Σ source target : ProbabilityTerm S, DoCalculusRewriteStep P.observedGraph source target) :=
        ⟨_, _, .atom (.multiplyComm a b)⟩
      change build (Term.encode profiles first requested).erase (Term.encode profiles second requested).erase = build first second
      rw [Term.erase_encode, Term.erase_encode]
  | multiplyAssoc first second third =>
      let build (a b c : ProbabilityTerm S) : (Σ source target : ProbabilityTerm S, DoCalculusRewriteStep P.observedGraph source target) :=
        ⟨_, _, .atom (.multiplyAssoc a b c)⟩
      change build (Term.encode profiles first requested).erase (Term.encode profiles second requested).erase
        (Term.encode profiles third requested).erase = build first second third
      rw [Term.erase_encode, Term.erase_encode, Term.erase_encode]

/-- The support proof is checked input, not a selected witness. Recursion
has one branch per actual elementary-step constructor and no transitivity. -/
def encode (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested step.toDerivation = true) : Step profiles :=
  match step with
  | .atom leaf => encodeAtom profiles leaf requested accepted
  | .symm inner => .symm (encode profiles inner requested (Bool.and_eq_true_iff.mp accepted).2)
  | @DoCalculusRewriteStep.under _ _ _ frame source _ inner => .under (Frame.encode profiles frame source requested)
      (encode profiles inner (frameDemand profiles frame requested)
        (Frame.inner_checked_of_lift profiles frame inner.toDerivation requested accepted))

/-- The complete primitive, reversal and frame tree is recovered literally.
Only the encoded annotations disappear. In particular no transitivity or
different intermediate conditional is substituted during reconstruction. -/
theorem eraseData_encode (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested step.toDerivation = true) :
    (encode profiles step requested accepted).eraseData = ⟨left, right, step⟩ := by
  induction step generalizing requested with
  | atom leaf => exact eraseData_encodeAtom profiles leaf requested accepted
  | symm inner ih =>
      let build (data : Σ source target : ProbabilityTerm S, DoCalculusRewriteStep P.observedGraph source target) :
          (Σ source target : ProbabilityTerm S, DoCalculusRewriteStep P.observedGraph source target) :=
        ⟨data.2.1, data.1, .symm data.2.2⟩
      exact congrArg build (ih requested (Bool.and_eq_true_iff.mp accepted).2)
  | under frame inner ih =>
      rename_i source target
      let build (context : ProbabilityTermFrame S)
          (data : Σ first last : ProbabilityTerm S, DoCalculusRewriteStep P.observedGraph first last) :
          (Σ first last : ProbabilityTerm S, DoCalculusRewriteStep P.observedGraph first last) :=
        ⟨_, _, .under context data.2.2⟩
      have innerChecked := Frame.inner_checked_of_lift profiles frame inner.toDerivation requested accepted
      change build (Frame.encode profiles frame source requested).erase
        (encode profiles inner (frameDemand profiles frame requested) innerChecked).eraseData = build frame ⟨source, target, inner⟩
      rw [Frame.erase_encode]
      exact congrArg (build frame) (ih (frameDemand profiles frame requested) innerChecked)

/-- Both endpoints are the canonical encodings at the application's one
outer demand. Weighted frames use native soundness only on the matching
graph to keep one common factor annotation across the two endpoints. -/
theorem encode_endpoints (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested step.toDerivation = true) :
    (encode profiles step requested accepted).left = Term.encode profiles left requested ∧
      (encode profiles step requested accepted).right = Term.encode profiles right requested := by
  induction step generalizing requested with
  | atom leaf => exact encodeAtom_endpoints profiles leaf requested accepted
  | symm inner ih =>
      have endpoints := ih requested (Bool.and_eq_true_iff.mp accepted).2
      exact ⟨endpoints.2, endpoints.1⟩
  | under frame inner ih =>
      have innerChecked := Frame.inner_checked_of_lift profiles frame inner.toDerivation requested accepted
      have endpoints := ih (frameDemand profiles frame requested) innerChecked
      change (Frame.encode profiles frame _ requested).fill _ = _ ∧ (Frame.encode profiles frame _ requested).fill _ = _
      rw [endpoints.1, endpoints.2, Frame.encode_fill, Frame.encode_fill_right profiles frame inner.toDerivation requested innerChecked]
      exact ⟨rfl, rfl⟩

/-- Forward coverage retains every original support application. It does
not replace a proof by a numerical equality of its final endpoint types. -/
theorem encode_checked (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested step.toDerivation = true) :
    (encode profiles step requested accepted).check requested = true := by
  have endpoints := encode_endpoints profiles step requested accepted
  unfold check
  rw [endpoints.1, endpoints.2, Term.checkAnnotations_encode, Term.checkAnnotations_encode,
    Term.erase_encode, Term.erase_encode]
  have supported := (raw_check_eq_endpoints profiles requested step).symm.trans accepted
  exact Bool.and_eq_true_iff.mpr ⟨rfl, supported⟩

theorem erase_encode_endpoints (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested step.toDerivation = true) :
    (encode profiles step requested accepted).left.erase = left ∧
      (encode profiles step requested accepted).right.erase = right := by
  have endpoints := encode_endpoints profiles step requested accepted
  rw [endpoints.1, endpoints.2, Term.erase_encode, Term.erase_encode]
  exact ⟨rfl, rfl⟩

/-- Opt-in conversion of one supplied elementary step. Rejection reports
its actual native support failure, rather than failure of identification or
of any unbounded search. No primitive catalogue enumeration is executed. -/
def encode? (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right)
    (requested : Demand profiles) : Option (Step profiles) :=
  if accepted : checkDerivation profiles requested step.toDerivation = true then
    some (encode profiles step requested accepted)
  else none

theorem encode?_isSome (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right)
    (requested : Demand profiles) :
    (encode? profiles step requested).isSome = checkDerivation profiles requested step.toDerivation := by
  unfold encode?
  split
  · next accepted => simp only [Option.isSome_some, accepted]
  · next rejected =>
      cases checked : checkDerivation profiles requested step.toDerivation with
      | false => rfl
      | true => exact False.elim (rejected checked)

theorem encode?_checked (profiles : List (NativeTemplateInstance P))
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right)
    (requested : Demand profiles) (encoded : Step profiles) (returned : encode? profiles step requested = some encoded) :
    encoded.check requested = true ∧ encoded.left = Term.encode profiles left requested ∧
      encoded.right = Term.encode profiles right requested := by
  unfold encode? at returned
  split at returned
  · next accepted =>
      cases Option.some.inj returned
      exact ⟨encode_checked profiles step requested accepted, encode_endpoints profiles step requested accepted⟩
  · simp only [reduceCtorEq] at returned

end Step
end Thesis.Causality.NativeDemandEncoding
