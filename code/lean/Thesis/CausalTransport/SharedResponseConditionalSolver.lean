import Thesis.CausalTransport.SharedResponseConditionalValues

namespace Thesis.Causality.SharedResponse.ConditionalValue

open Probability Probability.Distros

/-!
# Conditional support and value classification by exact linear optimization

First classify the evidence using the existing attained event bounds. If no
fitted model supports it, report that fact without optimizing a conditional
contrast. Otherwise use the returned positive-evidence model as a reference.
Its actual response law already supplies a feasible vector, so the contrast
optimizer need not repeat a compatibility search or choose from an existence
proof. Its two attained endpoints decide agreement or supply countermodels.

The final result retains the evidence report independently of the supported
values. In particular, mixed support may coexist with one common conditional
value. All statements concern the complete-bidirected original native class,
with arbitrary finite hidden alphabets and rational denominators. The finite
grid and elimination remain potentially large; there is no runtime bound or
claim of sharp conditional-probability intervals here.
-/

variable (S : ObservedSignature.{0})
variable (observed : FiniteProbRecord S.Assignment)
variable (intervention : HardIntervention S) (evidence event : Event S.Assignment)

/-- A reference model provides concrete feasible masses. This calls the
existing integer-response bound constructor, rather than a fractional solver. -/
def contrastBounds (reference : EvidenceSupport.SupportedModel S observed intervention evidence) :
    (supportedProblem S observed).SharpBounds
      (contrastResponse S intervention evidence event (supportedValue S observed intervention evidence event reference)) := by
  let law : Distro (Table S) := ⟨lawOfNative S reference.model.model⟩
  have admissible := (supportedProblem_law_iff S observed law).mpr
    (lawOfNative_fits S observed reference.model reference.fits)
  exact (supportedProblem S observed).boundsOfVector _
    (gridMasses law (supportedProblem S observed).cells (supportedProblem S observed).default)
    ((supportedProblem S observed).vectorOfLaw law admissible.1 admissible.2)

/-- Only a positive reference starts contrast optimization. Null evidence
throughout the fitted class is returned directly as an unsupported value report. -/
def reportOfSupport (support : EvidenceSupport.Report S observed intervention evidence) :
    Report S observed intervention evidence event :=
  match support with
  | .unsupported _ nullEvidence =>
      .unsupported (fun original fitted positive => (Nat.ne_of_gt positive) (nullEvidence original fitted))
  | .allSupported reference _ =>
      ofBounds reference (contrastBounds S observed intervention evidence event reference)
  | .mixed _ reference =>
      ofBounds reference (contrastBounds S observed intervention evidence event reference)

/-- Compatibility, support and supported values are separate conclusions.
The support report itself supplies fitted-model existence in every compatible
branch, including an all-null branch with no conditional value. -/
inductive Result where
  | incompatible (excluded : ∀ original, ¬ NativeFits S observed original)
  | compatible (support : EvidenceSupport.Report S observed intervention evidence)
      (values : Report S observed intervention evidence event)

variable {S observed intervention evidence event}

def Result.isCompatible : Result S observed intervention evidence event → Bool
  | .incompatible _ => false
  | .compatible .. => true

/-- Keep the existing support answer unchanged while constructing its value
report. This function introduces no support test on observational evidence. -/
def ofSupportResult (answer : EvidenceSupport.Result S observed intervention evidence) :
    Result S observed intervention evidence event :=
  match answer with
  | .incompatible excluded => .incompatible excluded
  | .compatible support => .compatible support (reportOfSupport S observed intervention evidence event support)

def solve (S : ObservedSignature.{0}) (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (evidence event : Event S.Assignment) :
    Result S observed intervention evidence event :=
  ofSupportResult (EvidenceSupport.solve S observed intervention evidence)

theorem Result.compatible_iff (answer : Result S observed intervention evidence event) :
    answer.isCompatible = true ↔ ∃ original, NativeFits S observed original := by
  cases answer with
  | incompatible excluded =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨original, fitted⟩
        exact False.elim (excluded original fitted)
  | compatible support _ => exact ⟨fun _ => support.compatible, fun _ => rfl⟩

/-- Unsupported evidence and incompatible observations both fail the
nonempty-supported-class premise of conditional identification. Other cases
use the exact value report; no global decision instance is installed. -/
def Result.identificationDecision (answer : Result S observed intervention evidence event) :
    Decidable (PointIdentified S observed intervention evidence event) :=
  match answer with
  | .incompatible excluded =>
      .isFalse (fun identified => by
        rcases identified.1 with ⟨original, fitted, _⟩
        exact excluded original fitted)
  | .compatible _ values => values.identificationDecision

end Thesis.Causality.SharedResponse.ConditionalValue
