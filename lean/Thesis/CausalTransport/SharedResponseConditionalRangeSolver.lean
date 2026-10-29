import Thesis.CausalTransport.SharedResponseConditionalRanges

namespace Thesis.Causality.SharedResponse.ConditionalRange

open Probability

/-!
# Separate support reporting and exact conditional intervals

Only a branch with an actual positive-evidence reference starts fractional
optimization. An all-null compatible class instead returns an unsupported
report, and incompatible observations retain their original exclusion proof.
The evidence report is kept alongside the range, so mixed support is never
silently converted into universal applicability of a conditional.

This is an additional entry point. The existing conditional-value classifier
and unconditional solvers remain unchanged. Elimination and response-table
enumeration can still be large; mathematical completeness within the stated
shared-root class is not a runtime guarantee or an arbitrary-graph result.
-/

variable (S : ObservedSignature.{0})
variable (observed : FiniteProbRecord S.Assignment)
variable (intervention : HardIntervention S) (evidence event : Event S.Assignment)

inductive Report where
  | unsupported (excluded : ∀ original, NativeFits S observed original →
      ¬ (original.model.interventionalDist intervention).EventPositive evidence)
  | bounded (sharp : SharpRange S observed intervention evidence event)

inductive Kind where
  | unsupported
  | bounded
  deriving DecidableEq

def Report.kind : Report S observed intervention evidence event → Kind
  | .unsupported _ => .unsupported
  | .bounded _ => .bounded

/-- The same support answer routes both supported branches to the same
range constructor. The null branch never manufactures a conditional value. -/
def reportOfSupport (support : EvidenceSupport.Report S observed intervention evidence) :
    Report S observed intervention evidence event :=
  match support with
  | .unsupported _ nullEvidence =>
      .unsupported (fun original fitted positive => (Nat.ne_of_gt positive) (nullEvidence original fitted))
  | .allSupported reference _ => .bounded (ofReference S observed intervention evidence event reference)
  | .mixed _ reference => .bounded (ofReference S observed intervention evidence event reference)

inductive Result where
  | incompatible (excluded : ∀ original, ¬ NativeFits S observed original)
  | compatible (support : EvidenceSupport.Report S observed intervention evidence)
      (ranges : Report S observed intervention evidence event)

def ofSupportResult (answer : EvidenceSupport.Result S observed intervention evidence) :
    Result S observed intervention evidence event :=
  match answer with
  | .incompatible excluded => .incompatible excluded
  | .compatible support => .compatible support (reportOfSupport S observed intervention evidence event support)

def solve (S : ObservedSignature.{0}) (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (evidence event : Event S.Assignment) :
    Result S observed intervention evidence event :=
  ofSupportResult S observed intervention evidence event (EvidenceSupport.solve S observed intervention evidence)

variable {S observed intervention evidence event}

/-- A bounded report exists exactly when a supported fitted model exists.
Null-evidence models cannot be used to witness that conditional domain. -/
theorem Report.bounded_iff (answer : Report S observed intervention evidence event) :
    answer.kind = .bounded ↔ ∃ original, NativeFits S observed original ∧
      (original.model.interventionalDist intervention).EventPositive evidence := by
  cases answer with
  | unsupported excluded =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨original, fitted, positive⟩
        exact False.elim (excluded original fitted positive)
  | bounded sharp =>
      exact ⟨fun _ => ⟨sharp.lower.model, sharp.lower.fits, sharp.lower.positive⟩, fun _ => rfl⟩

def Result.isCompatible : Result S observed intervention evidence event → Bool
  | .incompatible _ => false
  | .compatible .. => true

theorem Result.compatible_iff (answer : Result S observed intervention evidence event) :
    answer.isCompatible = true ↔ ∃ original, NativeFits S observed original := by
  cases answer with
  | incompatible excluded =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨original, fitted⟩; exact False.elim (excluded original fitted)
  | compatible support _ => exact ⟨fun _ => support.compatible, fun _ => rfl⟩

/-- Reuse the existing meaning of conditional point identification. Only
explicit rational endpoint equality is decided in the supported branch. -/
def Report.identificationDecision (answer : Report S observed intervention evidence event) :
    Decidable (ConditionalValue.PointIdentified S observed intervention evidence event) :=
  match answer with
  | .unsupported excluded => .isFalse (fun identified => by
      rcases identified.1 with ⟨original, fitted, positive⟩
      exact excluded original fitted positive)
  | .bounded sharp =>
      if same : QProb.Equiv (ConditionalValue.supportedValue S observed intervention evidence event sharp.lower)
          (ConditionalValue.supportedValue S observed intervention evidence event sharp.upper) then
        .isTrue (sharp.identified_iff.mpr same)
      else .isFalse (fun identified => same (sharp.identified_iff.mp identified))

end Thesis.Causality.SharedResponse.ConditionalRange
