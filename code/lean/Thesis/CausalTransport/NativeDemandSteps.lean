import Thesis.CausalTransport.NativeDemandFrames
import Thesis.CausalTransport.NativePrimitiveAtoms
import Thesis.CausalTransport.NativeRewritePathSupport

namespace Thesis.Causality.NativeDemandEncoding

open Probability NativeDemandTyping

/-!
# Encoded elementary steps with literal endpoints and explicit demands

This independent grammar admits one checked primitive leaf, or one of the
two existing strict-multiplication AC schemas, beneath reversal and any
finite nesting of one-hole frames. There is no arbitrary derivation field,
transitivity constructor, or equality inferred from endpoint type tables.
The primitive entry's decoder certificate prevents a hidden structural proof
from entering through a leaf. AC operands and fixed siblings remain ordinary
encoded trees over the existing finite alphabet, not new alphabet symbols.

The application supplies its demand to `Step.check`. Both complete endpoint
trees must carry exactly the canonical annotations for that demand, even in
unused branches. Their native support is then checked at the demanded cells.
For elementary steps, the earlier endpoint-exactness theorem proves that
this is precisely the original recursive proof-support obligation. This
shortcut is deliberately unavailable for arbitrary transitivity trees.

Erasure reconstructs an actual old elementary step on the matching graph.
It preserves literal siblings, zero-weight branches and strict multiplication;
weighted multiplication has no AC constructor. These are finite step trees,
not an enumeration of all trees, paths, normalization or a stopping theorem.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

inductive Step (profiles : List (NativeTemplateInstance P)) where
  | primitive (entry : TypedPrimitive profiles)
  | multiplyComm (demand : Demand profiles) (left right : Term profiles)
  | multiplyAssoc (demand : Demand profiles) (first second third : Term profiles)
  | symm (inner : Step profiles)
  | under (frame : Frame profiles) (inner : Step profiles)

namespace Step

variable {profiles : List (NativeTemplateInstance P)}

mutual

def left : Step profiles → Term profiles
  | .primitive entry => Term.encode profiles entry.checked.left entry.demand
  | .multiplyComm requested first second => .multiply requested first second
  | .multiplyAssoc requested first second third => .multiply requested (.multiply requested first second) third
  | .symm inner => inner.right
  | .under frame inner => frame.fill inner.left

def right : Step profiles → Term profiles
  | .primitive entry => Term.encode profiles entry.checked.right entry.demand
  | .multiplyComm requested first second => .multiply requested second first
  | .multiplyAssoc requested first second third => .multiply requested first (.multiply requested second third)
  | .symm inner => inner.left
  | .under frame inner => frame.fill inner.right

end

/-- Package the output's literal endpoint indices with its raw step, so an
exact syntax round-trip can compare ordinary equalities instead of hiding
index transports. This is output data, not a new input constructor. -/
def eraseData (step : Step profiles) : (Σ first last : ProbabilityTerm S, DoCalculusRewriteStep P.observedGraph first last) :=
  match step with
  | .primitive entry => ⟨entry.checked.left, entry.checked.right, .atom entry.atom⟩
  | .multiplyComm _ first second => ⟨_, _, .atom (.multiplyComm first.erase second.erase)⟩
  | .multiplyAssoc _ first second third => ⟨_, _, .atom (.multiplyAssoc first.erase second.erase third.erase)⟩
  | .symm inner => ⟨inner.eraseData.2.1, inner.eraseData.1, .symm inner.eraseData.2.2⟩
  | .under frame inner => ⟨_, _, .under frame.erase inner.eraseData.2.2⟩

theorem eraseData_endpoints (step : Step profiles) :
    step.eraseData.1 = step.left.erase ∧ step.eraseData.2.1 = step.right.erase := by
  induction step with
  | primitive entry => exact ⟨(Term.erase_encode ..).symm, (Term.erase_encode ..).symm⟩
  | multiplyComm | multiplyAssoc => exact ⟨rfl, rfl⟩
  | symm inner ih => exact ⟨ih.2, ih.1⟩
  | under frame inner ih =>
      simp only [eraseData, left, right, Frame.erase_fill, ih.1, ih.2, and_self]

/-- Reindex the same erased step by the erased encoded endpoints. Only
proved literal endpoint equalities are used; no equation rule is added. -/
def erase (step : Step profiles) : DoCalculusRewriteStep P.observedGraph step.left.erase step.right.erase := by
  exact cast
    ((congrArg (fun first => DoCalculusRewriteStep P.observedGraph first step.eraseData.2.1)
      step.eraseData_endpoints.1).trans
        (congrArg (DoCalculusRewriteStep P.observedGraph step.left.erase) step.eraseData_endpoints.2))
    step.eraseData.2.2

/-- An explicit root request prevents an empty annotation from silently
standing for a nonempty application's demand. All annotations are checked,
including literal siblings whose numerical support is legitimately unused. -/
def check (step : Step profiles) (requested : Demand profiles) : Bool :=
  (step.left.checkAnnotations requested && step.right.checkAnnotations requested) &&
    (NativeDemandTyping.check profiles step.left.erase requested &&
      NativeDemandTyping.check profiles step.right.erase requested)

/-- Aggregate the earlier modelwise elementary-step theorem over precisely
the demanded cells of the supplied family, including declared null values. -/
theorem raw_check_eq_endpoints (profiles : List (NativeTemplateInstance P)) (requested : Demand profiles)
    {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep P.observedGraph left right) :
    checkDerivation profiles requested step.toDerivation =
      (NativeDemandTyping.check profiles left requested && NativeDemandTyping.check profiles right requested) := by
  rw [checkDerivation_exact]
  simp only [DoCalculusRewriteStep.check_eq_endpoints, allNeeded_and, ← NativeDemandTyping.check_exact]

/-- Endpoint support is exact only because erasure is an elementary step.
The annotation checks remain additional, explicit syntactic obligations. -/
theorem check_exact (step : Step profiles) (requested : Demand profiles) :
    step.check requested =
      ((step.left.checkAnnotations requested && step.right.checkAnnotations requested) &&
        checkDerivation profiles requested step.erase.toDerivation) := by
  unfold check
  rw [raw_check_eq_endpoints]

theorem endpoints_canonical (step : Step profiles) (requested : Demand profiles)
    (accepted : step.check requested = true) :
    Term.encode profiles step.left.erase requested = step.left ∧
      Term.encode profiles step.right.erase requested = step.right := by
  have annotations := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1)
  exact ⟨(Term.checkAnnotations_exact ..).mp annotations.1, (Term.checkAnnotations_exact ..).mp annotations.2⟩

theorem erase_checked (step : Step profiles) (requested : Demand profiles)
    (accepted : step.check requested = true) :
    checkDerivation profiles requested step.erase.toDerivation = true :=
  (Bool.and_eq_true_iff.mp ((step.check_exact requested).symm.trans accepted)).2

end Step
end Thesis.Causality.NativeDemandEncoding
