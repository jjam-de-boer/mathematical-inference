import Thesis.CausalTransport.SharedResponseSupportedSolver

namespace Thesis.Causality.SharedResponse

open Probability

/-!
# Exact evidence-support reports in the shared-root class

Optimize the evidence event in its actual interventional distribution. The
lower and upper endpoints are attained by fitted original native models:
positive lower evidence proves support in every fitted model, while null
upper evidence proves nullness in every fitted model. Otherwise the two
endpoint models exhibit both possibilities. These tests inspect natural
event masses, rather than the denominator of the ambient probability law.

The report keeps compatibility separate, so an empty model class cannot be
presented as a usable universally supported query. Every compatible branch
contains an actual fitted witness. The class is still the complete-bidirected
projection class, with arbitrary finite hidden alphabets and rational
denominators. All hard interventions, including null factual actions, remain
allowed. This does not impose a positive lower bound on supported models.

No conditional value is formed or compared here. The endpoint transport is
separate from `solve`, allowing supplied certificates to be checked without
executing the optimizer. The solver and its existing entry points are unchanged.
-/

variable (S : ObservedSignature.{0})

private theorem num_zero_of_le {left right : QProb} (ordered : QProb.LE left right)
    (rightZero : right.num = 0) : left.num = 0 := by
  change left.num * right.den ≤ right.num * left.den at ordered
  rw [rightZero, Nat.zero_mul] at ordered
  rcases Nat.eq_zero_or_pos left.num with zero | positive
  · exact zero
  · have productPositive := Nat.mul_pos positive right.den_pos
    omega

namespace SharpBounds

variable {S} {observed : FiniteProbRecord S.Assignment}
variable {intervention : HardIntervention S} {evidence : Event S.Assignment}

/-- Attainment turns the signed lower endpoint into an inequality between
actual event probabilities. No fraction normalization is involved. -/
theorem lowerModel_value_le (sharp : SharpBounds S observed intervention evidence)
    (original : ProjectedHiddenDAGModel (graph S)) (fitted : NativeFits S observed original) :
    QProb.LE (sharp.lowerModel.model.interventionalValue intervention evidence)
      (original.model.interventionalValue intervention evidence) :=
  (SignedRatio.toSignedRatio_le_iff _ _).mp
    ((SignedRatio.le_congr (SignedRatio.equiv_symm sharp.lower_attained)
      (SignedRatio.equiv_refl _)).mp (sharp.bounds original fitted).1)

/-- The upper endpoint is likewise a genuine fitted model, rather than an
unrealized bound in a numerical relaxation. -/
theorem value_le_upperModel (sharp : SharpBounds S observed intervention evidence)
    (original : ProjectedHiddenDAGModel (graph S)) (fitted : NativeFits S observed original) :
    QProb.LE (original.model.interventionalValue intervention evidence)
      (sharp.upperModel.model.interventionalValue intervention evidence) :=
  (SignedRatio.toSignedRatio_le_iff _ _).mp
    ((SignedRatio.le_congr (SignedRatio.equiv_refl _)
      (SignedRatio.equiv_symm sharp.upper_attained)).mp (sharp.bounds original fitted).2)

/-- A positive attained minimum supplies support throughout the original
native class. The case split is only on one natural event mass. -/
theorem evidence_positive_of_lower (sharp : SharpBounds S observed intervention evidence)
    (positive : (sharp.lowerModel.model.interventionalDist intervention).EventPositive evidence)
    (original : ProjectedHiddenDAGModel (graph S)) (fitted : NativeFits S observed original) :
    (original.model.interventionalDist intervention).EventPositive evidence := by
  rcases Nat.eq_zero_or_pos (original.model.interventionalValue intervention evidence).num with zero | supported
  · exact False.elim ((Nat.ne_of_gt positive) (num_zero_of_le (sharp.lowerModel_value_le original fitted) zero))
  · exact supported

/-- A null attained maximum excludes support in every fitted model. This is
an exact zero-mass conclusion and never calls `conditionOn`. -/
theorem evidence_null_of_upper (sharp : SharpBounds S observed intervention evidence)
    (nullEvidence : (sharp.upperModel.model.interventionalValue intervention evidence).num = 0)
    (original : ProjectedHiddenDAGModel (graph S)) (fitted : NativeFits S observed original) :
    (original.model.interventionalValue intervention evidence).num = 0 :=
  num_zero_of_le (sharp.value_le_upperModel original fitted) nullEvidence

end SharpBounds

namespace EvidenceSupport

variable (observed : FiniteProbRecord S.Assignment)
variable (intervention : HardIntervention S) (evidence : Event S.Assignment)

/-- An attained positive-evidence witness in the original projection-wide
class. Its source alphabet and denominator are not supplied bounds. -/
structure SupportedModel where
  model : ProjectedHiddenDAGModel (graph S)
  fits : NativeFits S observed model
  positive : (model.model.interventionalDist intervention).EventPositive evidence

/-- A null-evidence witness remains a fitted native model. Its conditional
probability is deliberately absent from this structure. -/
structure NullModel where
  model : ProjectedHiddenDAGModel (graph S)
  fits : NativeFits S observed model
  nullEvidence : (model.model.interventionalValue intervention evidence).num = 0

/-- Three exhaustive support possibilities inside a nonempty compatible
class. Mixed support retains both models for a later supported-value analysis. -/
inductive Report where
  | unsupported (witness : NullModel S observed intervention evidence)
      (nullEvidence : ∀ original, NativeFits S observed original →
        (original.model.interventionalValue intervention evidence).num = 0)
  | allSupported (witness : SupportedModel S observed intervention evidence)
      (positive : ∀ original, NativeFits S observed original →
        (original.model.interventionalDist intervention).EventPositive evidence)
  | mixed (nullWitness : NullModel S observed intervention evidence)
      (positiveWitness : SupportedModel S observed intervention evidence)

/-- A small observable tag for the report. Keeping it separate from the
proof fields gives clients a stable comparison across module boundaries. -/
inductive Kind where
  | unsupported
  | allSupported
  | mixed
  deriving DecidableEq

inductive Result where
  | incompatible (excluded : ∀ original, ¬ NativeFits S observed original)
  | compatible (report : Report S observed intervention evidence)

variable {S observed intervention evidence}

def Report.kind : Report S observed intervention evidence → Kind
  | .unsupported .. => .unsupported
  | .allSupported .. => .allSupported
  | .mixed .. => .mixed

def Result.isCompatible : Result S observed intervention evidence → Bool
  | .incompatible _ => false
  | .compatible _ => true

/-- Only the two endpoint evidence masses are decided. If the maximum is
null, it itself witnesses compatibility; if the minimum is positive, it
witnesses support. The remaining branch retains both attained models. -/
def ofBounds (sharp : SharpBounds S observed intervention evidence) : Report S observed intervention evidence :=
  if upperPositive : (sharp.upperModel.model.interventionalDist intervention).EventPositive evidence then
    if lowerPositive : (sharp.lowerModel.model.interventionalDist intervention).EventPositive evidence then
      .allSupported ⟨sharp.lowerModel, sharp.lower_fits, lowerPositive⟩
        (sharp.evidence_positive_of_lower lowerPositive)
    else
      .mixed ⟨sharp.lowerModel, sharp.lower_fits, Nat.eq_zero_of_not_pos lowerPositive⟩
        ⟨sharp.upperModel, sharp.upper_fits, upperPositive⟩
  else
    .unsupported ⟨sharp.upperModel, sharp.upper_fits, Nat.eq_zero_of_not_pos upperPositive⟩
      (sharp.evidence_null_of_upper (Nat.eq_zero_of_not_pos upperPositive))

/-- Transport a checked result without running the optimizer. Incompatibility
is preserved as exclusion of original native models, rather than a null event. -/
def ofBoundResult (answer : BoundResult S observed intervention evidence) : Result S observed intervention evidence :=
  match answer with
  | .incompatible excluded => .incompatible excluded
  | .bounded sharp => .compatible (ofBounds sharp)

/-- Exact evidence classification using the existing filtered solver. No
conditional value or second optimization problem is introduced. -/
def solve (S : ObservedSignature.{0}) (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (evidence : Event S.Assignment) : Result S observed intervention evidence :=
  ofBoundResult (solveSupportedBounds S observed intervention evidence)

/-- Every report certifies that at least one actual native model fits. This
prevents either universal branch from relying on an empty model class. -/
theorem Report.compatible (report : Report S observed intervention evidence) :
    ∃ original, NativeFits S observed original := by
  cases report with
  | unsupported witness _ => exact ⟨witness.model, witness.fits⟩
  | allSupported witness _ => exact ⟨witness.model, witness.fits⟩
  | mixed witness _ => exact ⟨witness.model, witness.fits⟩

/-- The reported all-supported case is equivalent to universal evidence
positivity, not merely sufficient for it. A null witness refutes that case. -/
theorem Report.allSupported_iff (report : Report S observed intervention evidence) :
    report.kind = .allSupported ↔
      ∀ original, NativeFits S observed original →
        (original.model.interventionalDist intervention).EventPositive evidence := by
  cases report with
  | unsupported witness _ =>
      constructor
      · intro impossible; cases impossible
      · intro positive
        exact False.elim ((Nat.ne_of_gt (positive witness.model witness.fits)) witness.nullEvidence)
  | allSupported _ positive => exact ⟨fun _ => positive, fun _ => rfl⟩
  | mixed witness _ =>
      constructor
      · intro impossible; cases impossible
      · intro positive
        exact False.elim ((Nat.ne_of_gt (positive witness.model witness.fits)) witness.nullEvidence)

/-- The unsupported case characterizes nullness throughout the compatible
class. A positive witness refutes it even when other models have null evidence. -/
theorem Report.unsupported_iff (report : Report S observed intervention evidence) :
    report.kind = .unsupported ↔
      ∀ original, NativeFits S observed original →
        (original.model.interventionalValue intervention evidence).num = 0 := by
  cases report with
  | unsupported _ nullEvidence => exact ⟨fun _ => nullEvidence, fun _ => rfl⟩
  | allSupported witness _ =>
      constructor
      · intro impossible; cases impossible
      · intro nullEvidence
        exact False.elim ((Nat.ne_of_gt witness.positive) (nullEvidence witness.model witness.fits))
  | mixed _ witness =>
      constructor
      · intro impossible; cases impossible
      · intro nullEvidence
        exact False.elim ((Nat.ne_of_gt witness.positive) (nullEvidence witness.model witness.fits))

/-- Mixed support means actual null and positive fitted models both exist;
failure of universal positivity alone would not supply the positive model. -/
theorem Report.mixed_iff (report : Report S observed intervention evidence) :
    report.kind = .mixed ↔
      (∃ original, NativeFits S observed original ∧
        (original.model.interventionalValue intervention evidence).num = 0) ∧
      (∃ original, NativeFits S observed original ∧
        (original.model.interventionalDist intervention).EventPositive evidence) := by
  cases report with
  | unsupported _ nullEvidence =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, original, fitted, positive⟩
        exact False.elim ((Nat.ne_of_gt positive) (nullEvidence original fitted))
  | allSupported _ positive =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨⟨original, fitted, nullEvidence⟩, _⟩
        exact False.elim ((Nat.ne_of_gt (positive original fitted)) nullEvidence)
  | mixed nullWitness positiveWitness =>
      exact ⟨fun _ => ⟨⟨nullWitness.model, nullWitness.fits, nullWitness.nullEvidence⟩,
        ⟨positiveWitness.model, positiveWitness.fits, positiveWitness.positive⟩⟩, fun _ => rfl⟩

/-- Success is exactly native compatibility; the compatibility witness is
part of the returned support report, including the all-null branch. -/
theorem Result.compatible_iff (answer : Result S observed intervention evidence) :
    answer.isCompatible = true ↔
      ∃ original, NativeFits S observed original := by
  cases answer with
  | incompatible excluded =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨original, fitted⟩
        exact False.elim (excluded original fitted)
  | compatible report => exact ⟨fun _ => report.compatible, fun _ => rfl⟩

end EvidenceSupport
end Thesis.Causality.SharedResponse
