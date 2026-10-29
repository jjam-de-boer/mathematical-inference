import Thesis.Probability.Distros.PartialMomentBounds
import Thesis.Probability.Distros.RationalConditionalBounds

namespace Thesis.Probability.Distros.PartialMomentProblem

open RationalLinear

/-!
# Sharp supported conditional ranges for finite partial-moment laws

The fractional optimizer is connected here to actual finite probability
records. Both its evidence bound and its unit-interval objective bounds are
proved from event probabilities, rather than supplied as extra hypotheses.
Every compatible input law is covered almost surely; it need not retain all
zero cells or have the same atom presentation as the declared grid.

Conversely every returned vector constructs an actual compatible law with
positive evidence. Endpoints and every intermediate rational probability
therefore have law witnesses. Null-evidence laws stay outside the conditional
domain; this module neither assigns them a value nor imposes a positive
cutoff on the supported laws. Native causal coverage is a downstream step.
-/

variable {A : Type u}

def eventCoefficients (problem : PartialMomentProblem A) (event : Event A) : Fin problem.cells.length → Int :=
  problem.objectiveCoefficients (eventResponse event)

theorem gridMasses_event [DecidableEq A] (problem : PartialMomentProblem A) (μ : Distro A)
    (support : μ.AlmostSurely (fun cell => cell ∈ problem.cells)) (event : Event A) :
    SignedRatio.Equiv (dot problem.cells.length (problem.eventCoefficients event)
      (gridMasses μ problem.cells problem.default)) (μ.record.probVal event).toSignedRatio :=
  SignedRatio.equiv_trans
    (SignedRatio.equiv_symm (gridMasses_integer_expectation μ problem.cells problem.default problem.distinct support (eventResponse event)))
    (eventResponse_expectation μ event)

theorem lawOfVector_event (problem : PartialMomentProblem A) (values : Fin problem.cells.length → SignedRatio)
    (valid : problem.VectorHolds values) (event : Event A) :
    SignedRatio.Equiv (dot problem.cells.length (problem.eventCoefficients event) values)
      ((problem.lawOfVector values valid).distro.record.probVal event).toSignedRatio :=
  SignedRatio.equiv_trans
    (SignedRatio.equiv_symm (simplexGrid_integer_expectation problem.cells problem.default values valid.1 problem.nonempty (eventResponse event)))
    (eventResponse_expectation _ event)

private theorem event_positive_signed (record : FiniteProbRecord A) (evidence : Event A)
    (positive : record.EventPositive evidence) : 0 < (record.probVal evidence).toSignedRatio.num := by
  change 0 < (FiniteProbRecord.eventMass record.atoms evidence : Int)
  change 0 < FiniteProbRecord.eventMass record.atoms evidence at positive
  omega

private theorem fraction_eq_conditional (record : FiniteProbRecord A) (evidence event : Event A)
    (positive : record.EventPositive evidence) :
    SignedRatio.Equiv
      (SignedRatio.mul (positiveInverse (record.probVal evidence).toSignedRatio
        (event_positive_signed record evidence positive))
        (record.probVal (fun x => evidence x && event x)).toSignedRatio)
      ((record.conditionOn evidence positive).probVal event).toSignedRatio := by
  have divided : SignedRatio.Equiv
      (SignedRatio.mul (positiveInverse (record.probVal evidence).toSignedRatio
        (event_positive_signed record evidence positive))
        (record.probVal (fun x => evidence x && event x)).toSignedRatio)
      (QProb.div (record.probVal (fun x => evidence x && event x)) (record.probVal evidence) positive).toSignedRatio := by
    simp only [SignedRatio.Equiv, SignedRatio.mul, positiveInverse, QProb.toSignedRatio,
      FiniteProbRecord.probVal, QProb.div, Int.toNat_natCast, Int.natCast_mul]
    ac_rfl
  exact SignedRatio.equiv_trans divided
    (QProb.toSignedRatio_congr (QProb.equiv_symm (record.conditionOn_probVal evidence event positive)))

/-- Almost-sure grid support is enough. In particular, an arbitrary input
law is not required to retain every declared zero cell in its atom list. -/
structure ConditionalLaw (problem : PartialMomentProblem A) (evidence : Event A) where
  distro : Distro A
  support : distro.AlmostSurely (fun cell => cell ∈ problem.cells)
  moments : ∀ constraint ∈ problem.intervals, constraint.LawHolds distro
  positive : distro.record.EventPositive evidence

namespace ConditionalLaw

variable {problem : PartialMomentProblem A} {evidence : Event A}

def value (law : problem.ConditionalLaw evidence) (event : Event A) : QProb :=
  ((law.distro.record.conditionOn evidence law.positive).probVal event)

def toSupportedAssignment [DecidableEq A] (law : problem.ConditionalLaw evidence) :
    Conditional.SupportedAssignment problem.rows (problem.eventCoefficients evidence) where
  values := gridMasses law.distro problem.cells problem.default
  feasible := (problem.rows_iff _).mpr (problem.vectorOfLaw law.distro law.support law.moments)
  positive := (Conditional.num_pos_iff_of_equiv (problem.gridMasses_event law.distro law.support evidence)).mpr
    (event_positive_signed law.distro.record evidence law.positive)
  bounded := (SignedRatio.le_congr (problem.gridMasses_event law.distro law.support evidence) (SignedRatio.equiv_refl _)).mpr
    ((SignedRatio.toSignedRatio_le_iff _ _).mpr (law.distro.record.probVal_le_one evidence))

theorem toSupportedAssignment_value [DecidableEq A] (law : problem.ConditionalLaw evidence) (event : Event A) :
    SignedRatio.Equiv (law.toSupportedAssignment.conditionalValue
      (problem.eventCoefficients (fun x => evidence x && event x))) (law.value event).toSignedRatio :=
  SignedRatio.equiv_trans
    (law.toSupportedAssignment.conditionalValue_congr _ _ _
      (event_positive_signed law.distro.record evidence law.positive)
      (problem.gridMasses_event law.distro law.support evidence)
      (problem.gridMasses_event law.distro law.support (fun x => evidence x && event x)))
    (fraction_eq_conditional law.distro.record evidence event law.positive)

/-- The generic optimizer's explicit unit bounds follow from the actual
conditioned probability record, including all permitted zero probabilities. -/
def toAssignment [DecidableEq A] (law : problem.ConditionalLaw evidence) (event : Event A) :
    Conditional.UnitValueAssignment problem.rows (problem.eventCoefficients evidence)
      (problem.eventCoefficients (fun x => evidence x && event x)) where
  source := law.toSupportedAssignment
  nonnegative := (SignedRatio.le_congr (SignedRatio.equiv_refl _) (law.toSupportedAssignment_value event)).mpr
    ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le _))
  bounded := (SignedRatio.le_congr (law.toSupportedAssignment_value event) (SignedRatio.equiv_refl _)).mpr
    ((SignedRatio.toSignedRatio_le_iff _ _).mpr ((law.distro.record.conditionOn evidence law.positive).probVal_le_one event))

end ConditionalLaw

/-- Decode any feasible supported vector to an actual law. Positivity is
transported from the evidence response, not inferred from literal retention. -/
def conditionalLawOfAssignment (problem : PartialMomentProblem A) (evidence event : Event A)
    (point : Conditional.UnitValueAssignment problem.rows (problem.eventCoefficients evidence)
      (problem.eventCoefficients (fun x => evidence x && event x))) : problem.ConditionalLaw evidence := by
  let valid := (problem.rows_iff point.source.values).mp point.source.feasible
  let law := problem.lawOfVector point.source.values valid
  refine ⟨law.distro, law.support, law.moments, ?_⟩
  have positive := (Conditional.num_pos_iff_of_equiv (problem.lawOfVector_event point.source.values valid evidence)).mp point.source.positive
  change 0 < (FiniteProbRecord.eventMass law.distro.record.atoms evidence : Int) at positive
  change 0 < FiniteProbRecord.eventMass law.distro.record.atoms evidence
  omega

theorem conditionalLawOfAssignment_value (problem : PartialMomentProblem A) (evidence event : Event A)
    (point : Conditional.UnitValueAssignment problem.rows (problem.eventCoefficients evidence)
      (problem.eventCoefficients (fun x => evidence x && event x))) :
    SignedRatio.Equiv ((problem.conditionalLawOfAssignment evidence event point).value event).toSignedRatio point.value := by
  let law := problem.conditionalLawOfAssignment evidence event point
  have response := point.source.conditionalValue_congr _ _ _
    (event_positive_signed law.distro.record evidence law.positive)
    (problem.lawOfVector_event point.source.values ((problem.rows_iff _).mp point.source.feasible) evidence)
    (problem.lawOfVector_event point.source.values ((problem.rows_iff _).mp point.source.feasible) (fun x => evidence x && event x))
  exact SignedRatio.equiv_symm (SignedRatio.equiv_trans response (fraction_eq_conditional law.distro.record evidence event law.positive))

/-- Sharpness includes genuine endpoint laws and a constructive witness for
every rational probability between their supported conditional values. -/
structure ConditionalRange (problem : PartialMomentProblem A) (evidence event : Event A) where
  lower : problem.ConditionalLaw evidence
  upper : problem.ConditionalLaw evidence
  bounds : ∀ original : problem.ConditionalLaw evidence,
    QProb.LE (lower.value event) (original.value event) ∧ QProb.LE (original.value event) (upper.value event)
  pointBetween : ∀ value : QProb, QProb.LE (lower.value event) value → QProb.LE value (upper.value event) →
    {original : problem.ConditionalLaw evidence // QProb.Equiv (original.value event) value}

/-- Use a supported reference only for nonemptiness, then compute all bounds
and attaining laws. No external conditional optimization or law coverage is
assumed; both directions were proved above from the finite probability grid. -/
def conditionalRange [DecidableEq A] (problem : PartialMomentProblem A) (evidence event : Event A)
    (reference : problem.ConditionalLaw evidence) : problem.ConditionalRange evidence event := by
  let sharp := Conditional.fractionalRange (reference.toAssignment event)
  let lower := problem.conditionalLawOfAssignment evidence event sharp.lower
  let upper := problem.conditionalLawOfAssignment evidence event sharp.upper
  have lowerValue := problem.conditionalLawOfAssignment_value evidence event sharp.lower
  have upperValue := problem.conditionalLawOfAssignment_value evidence event sharp.upper
  refine ⟨lower, upper, ?_, ?_⟩
  · intro original
    have bounded := sharp.bounds (original.toAssignment event)
    have actual := original.toSupportedAssignment_value event
    exact ⟨(SignedRatio.toSignedRatio_le_iff _ _).mp ((SignedRatio.le_congr lowerValue (SignedRatio.equiv_symm actual)).mpr bounded.1),
      (SignedRatio.toSignedRatio_le_iff _ _).mp ((SignedRatio.le_congr (SignedRatio.equiv_symm actual) upperValue).mpr bounded.2)⟩
  · intro value lowerBound upperBound
    let attained := sharp.pointBetween value.toSignedRatio
      ((SignedRatio.le_congr lowerValue (SignedRatio.equiv_refl _)).mp ((SignedRatio.toSignedRatio_le_iff _ _).mpr lowerBound))
      ((SignedRatio.le_congr (SignedRatio.equiv_refl _) upperValue).mp ((SignedRatio.toSignedRatio_le_iff _ _).mpr upperBound))
    exact ⟨problem.conditionalLawOfAssignment evidence event attained.val,
      (QProb.toSignedRatio_equiv_iff _ _).mp (SignedRatio.equiv_trans
        (problem.conditionalLawOfAssignment_value evidence event attained.val) attained.property)⟩

/-- The interval is exact, including both endpoints. This is an attained
set theorem about actual laws, rather than only two numerical inequalities. -/
theorem ConditionalRange.attainable_iff_bounds {problem : PartialMomentProblem A} {evidence event : Event A}
    (sharp : problem.ConditionalRange evidence event) (value : QProb) :
    (∃ law : problem.ConditionalLaw evidence, QProb.Equiv (law.value event) value) ↔
      QProb.LE (sharp.lower.value event) value ∧ QProb.LE value (sharp.upper.value event) := by
  constructor
  · rintro ⟨law, same⟩
    have bounded := sharp.bounds law
    exact ⟨QProb.le_congr (QProb.equiv_refl _) same bounded.1,
      QProb.le_congr same (QProb.equiv_refl _) bounded.2⟩
  · rintro ⟨lower, upper⟩
    let attained := sharp.pointBetween value lower upper
    exact ⟨attained.val, attained.property⟩

end Thesis.Probability.Distros.PartialMomentProblem
