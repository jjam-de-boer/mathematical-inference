import Thesis.CausalTransport.SharedResponseConditionalContrast
import Thesis.CausalTransport.SharedResponseEvidenceSupport

namespace Thesis.Causality.SharedResponse.ConditionalValue

open Probability Probability.Distros

/-!
# Exact conditional-value certificates in the shared-root class

Evidence support and conditional agreement answer different questions. A
positive-evidence reference supplies its actual rational conditional value.
Zero contrast bounds prove agreement throughout the supported native class;
a nonzero attaining contrast supplies a second supported model with a
different value. Null-evidence models contribute zero contrast and are never
used as conditional counterexamples.

The report below contains genuine witnesses and universal native-model
proofs. It compares supported values, while allowing other fitted models to
have null evidence. Identification requires at least one supported model.
No conditional is totalized and no support cutoff, hidden alphabet bound or
rational denominator bound is added. This module routes supplied bounds;
the executable optimizer adapter is a separate layer.
-/

variable (S : ObservedSignature.{0})
variable (observed : FiniteProbRecord S.Assignment)
variable (intervention : HardIntervention S) (evidence event : Event S.Assignment)

def supportedValue (witness : EvidenceSupport.SupportedModel S observed intervention evidence) : QProb :=
  value S intervention evidence event witness.model witness.positive

/-- Identification among positive-evidence models, with a nonempty supported
class. Mixed evidence support is compatible with this property. -/
def PointIdentified : Prop :=
  (∃ original, NativeFits S observed original ∧
    (original.model.interventionalDist intervention).EventPositive evidence) ∧
  ∀ left right, NativeFits S observed left → NativeFits S observed right →
    (leftPositive : (left.model.interventionalDist intervention).EventPositive evidence) →
    (rightPositive : (right.model.interventionalDist intervention).EventPositive evidence) →
    QProb.Equiv (value S intervention evidence event left leftPositive)
      (value S intervention evidence event right rightPositive)

inductive Report where
  | unsupported (excluded : ∀ original, NativeFits S observed original →
      ¬ (original.model.interventionalDist intervention).EventPositive evidence)
  | identified (witness : EvidenceSupport.SupportedModel S observed intervention evidence)
      (constant : ∀ original, NativeFits S observed original →
        (positive : (original.model.interventionalDist intervention).EventPositive evidence) →
        QProb.Equiv (value S intervention evidence event original positive)
          (supportedValue S observed intervention evidence event witness))
  | ambiguous (left right : EvidenceSupport.SupportedModel S observed intervention evidence)
      (different : ¬ QProb.Equiv (supportedValue S observed intervention evidence event left)
        (supportedValue S observed intervention evidence event right))

inductive Kind where
  | unsupported
  | identified
  | ambiguous
  deriving DecidableEq

variable {S observed intervention evidence event}

def Report.kind : Report S observed intervention evidence event → Kind
  | .unsupported _ => .unsupported
  | .identified .. => .identified
  | .ambiguous .. => .ambiguous

/-- A nonzero attaining response law realizes a fitted original native
model whose evidence is positive. This is data transport, not witness choice. -/
def countermodelOfNonzero (proposed : QProb) (law : (supportedProblem S observed).CompatibleLaw)
    (nonzero : ¬ SignedRatio.Equiv
      (lawContrastMean S intervention evidence event proposed law.distro.record) SignedRatio.zero) :
    EvidenceSupport.SupportedModel S observed intervention evidence where
  model := supportedFittedModel S observed law
  fits := supportedFittedModel_fits S observed law
  positive := positive_of_contrastMean_nonzero S intervention evidence event proposed
    (supportedFittedModel S observed law)
    (fun zero => nonzero ((asProjectedModel_contrast_zero_iff S intervention evidence event proposed law.distro.record).mpr zero))

theorem countermodelOfNonzero_differs (proposed : QProb) (law : (supportedProblem S observed).CompatibleLaw)
    (nonzero : ¬ SignedRatio.Equiv
      (lawContrastMean S intervention evidence event proposed law.distro.record) SignedRatio.zero) :
    ¬ QProb.Equiv (supportedValue S observed intervention evidence event (countermodelOfNonzero proposed law nonzero))
      proposed := by
  intro same
  have nativeZero := (contrastMean_zero_iff S intervention evidence event proposed
    (countermodelOfNonzero proposed law nonzero).model (countermodelOfNonzero proposed law nonzero).positive).mpr same
  exact nonzero ((asProjectedModel_contrast_zero_iff S intervention evidence event proposed law.distro.record).mpr nativeZero)

/-- Coverage is used in the universal direction as well as at the endpoints.
Every fitted original model yields an admissible response law. Both zero
bounds therefore force its contrast to vanish, and supported conditioning
then gives its actual conditional value. -/
theorem constant_of_zero_bounds (proposed : QProb)
    (sharp : (supportedProblem S observed).SharpBounds (contrastResponse S intervention evidence event proposed))
    (lowerZero : SignedRatio.Equiv sharp.lower SignedRatio.zero)
    (upperZero : SignedRatio.Equiv sharp.upper SignedRatio.zero)
    (original : ProjectedHiddenDAGModel (graph S)) (fitted : NativeFits S observed original)
    (positive : (original.model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv (value S intervention evidence event original positive) proposed := by
  let law : Distro (Table S) := ⟨lawOfNative S original.model⟩
  have admissible := (supportedProblem_law_iff S observed law).mpr (lawOfNative_fits S observed original fitted)
  have bounded := sharp.bounds law admissible.1 admissible.2
  have lawZero : SignedRatio.Equiv (lawContrastMean S intervention evidence event proposed law.record) SignedRatio.zero :=
    SignedRatio.equiv_of_le_of_le
      ((SignedRatio.le_congr (SignedRatio.equiv_refl _) upperZero).mp bounded.2)
      ((SignedRatio.le_congr lowerZero (SignedRatio.equiv_refl _)).mp bounded.1)
  exact (contrastMean_zero_iff S intervention evidence event proposed original positive).mp
    ((lawOfNative_contrast_zero_iff S intervention evidence event proposed original).mp lawZero)

/-- The only tests compare explicit rational endpoints with zero. A nonzero
endpoint is converted into a supported native disagreement witness; the
reference itself is retained as the other model. -/
def ofBounds (reference : EvidenceSupport.SupportedModel S observed intervention evidence)
    (sharp : (supportedProblem S observed).SharpBounds
      (contrastResponse S intervention evidence event (supportedValue S observed intervention evidence event reference))) :
    Report S observed intervention evidence event :=
  if lowerZero : SignedRatio.Equiv sharp.lower SignedRatio.zero then
    if upperZero : SignedRatio.Equiv sharp.upper SignedRatio.zero then
      .identified reference (constant_of_zero_bounds _ sharp lowerZero upperZero)
    else
      let nonzero := fun zero => upperZero (SignedRatio.equiv_trans (SignedRatio.equiv_symm sharp.upper_attained) zero)
      .ambiguous reference (countermodelOfNonzero _ sharp.upperLaw nonzero)
        (fun same => countermodelOfNonzero_differs _ sharp.upperLaw nonzero (QProb.equiv_symm same))
  else
    let nonzero := fun zero => lowerZero (SignedRatio.equiv_trans (SignedRatio.equiv_symm sharp.lower_attained) zero)
    .ambiguous reference (countermodelOfNonzero _ sharp.lowerLaw nonzero)
      (fun same => countermodelOfNonzero_differs _ sharp.lowerLaw nonzero (QProb.equiv_symm same))

/-- The unsupported answer means that no fitted model supplies the evidence
needed for a conditional. Positive models in either other branch refute it. -/
theorem Report.unsupported_iff (report : Report S observed intervention evidence event) :
    report.kind = .unsupported ↔
      ∀ original, NativeFits S observed original →
        ¬ (original.model.interventionalDist intervention).EventPositive evidence := by
  cases report with
  | unsupported excluded => exact ⟨fun _ => excluded, fun _ => rfl⟩
  | identified witness _ =>
      constructor
      · intro impossible; cases impossible
      · intro excluded
        exact False.elim (excluded witness.model witness.fits witness.positive)
  | ambiguous left _ _ =>
      constructor
      · intro impossible; cases impossible
      · intro excluded
        exact False.elim (excluded left.model left.fits left.positive)

/-- Independent support and value reports cannot disagree about absence of
supported models. Nullness is exactly failure of positive natural event mass. -/
theorem Report.unsupported_iff_support (report : Report S observed intervention evidence event)
    (support : EvidenceSupport.Report S observed intervention evidence) :
    report.kind = .unsupported ↔ support.kind = .unsupported := by
  rw [report.unsupported_iff, support.unsupported_iff]
  constructor
  · intro excluded original fitted
    exact Nat.eq_zero_of_not_pos (excluded original fitted)
  · intro nullEvidence original fitted positive
    exact (Nat.ne_of_gt positive) (nullEvidence original fitted)

/-- Exact point-identification classification among supported original
models, rather than agreement only within the enumerated response witnesses. -/
theorem Report.identified_iff (report : Report S observed intervention evidence event) :
    report.kind = .identified ↔ PointIdentified S observed intervention evidence event := by
  cases report with
  | unsupported excluded =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨⟨original, fitted, positive⟩, _⟩
        exact False.elim (excluded original fitted positive)
  | identified witness constant =>
      constructor
      · intro _
        refine ⟨⟨witness.model, witness.fits, witness.positive⟩, ?_⟩
        intro left right leftFits rightFits leftPositive rightPositive
        exact QProb.equiv_trans (constant left leftFits leftPositive)
          (QProb.equiv_symm (constant right rightFits rightPositive))
      · intro _; rfl
  | ambiguous left right different =>
      constructor
      · intro impossible; cases impossible
      · intro identified
        exact False.elim (different (identified.2 left.model right.model left.fits right.fits left.positive right.positive))

/-- The ambiguous answer is equivalent to two actual supported native
countermodels. A null-evidence model cannot satisfy either support premise. -/
theorem Report.ambiguous_iff (report : Report S observed intervention evidence event) :
    report.kind = .ambiguous ↔
      ∃ left right, NativeFits S observed left ∧ NativeFits S observed right ∧
        ∃ leftPositive : (left.model.interventionalDist intervention).EventPositive evidence,
        ∃ rightPositive : (right.model.interventionalDist intervention).EventPositive evidence,
          ¬ QProb.Equiv (value S intervention evidence event left leftPositive)
            (value S intervention evidence event right rightPositive) := by
  cases report with
  | unsupported excluded =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨left, _, leftFits, _, leftPositive, _, _⟩
        exact False.elim (excluded left leftFits leftPositive)
  | identified _ constant =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨left, right, leftFits, rightFits, leftPositive, rightPositive, different⟩
        exact False.elim (different (QProb.equiv_trans (constant left leftFits leftPositive)
          (QProb.equiv_symm (constant right rightFits rightPositive))))
  | ambiguous left right different =>
      exact ⟨fun _ => ⟨left.model, right.model, left.fits, right.fits, left.positive, right.positive, different⟩,
        fun _ => rfl⟩

/-- An explicit decision from a checked report. It is not a global instance
that could silently invoke a large causal search during unrelated proofs. -/
def Report.identificationDecision (report : Report S observed intervention evidence event) :
    Decidable (PointIdentified S observed intervention evidence event) :=
  if identified : report.kind = .identified then
    .isTrue (report.identified_iff.mp identified)
  else .isFalse (fun proof => identified (report.identified_iff.mpr proof))

end Thesis.Causality.SharedResponse.ConditionalValue
