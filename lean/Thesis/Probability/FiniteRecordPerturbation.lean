import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability

/-!
# Strictly positive finite records from balanced natural perturbations

Two nonnegative weight families with equal total mass can be added to the
same strictly positive baseline.  They then define normalized records with
the same denominator, positive at every supplied value.  Their cell balance
is exact and uses no subtraction or limiting argument.

The finite value list is explicit and may contain duplicates.  Repeated
labels are accumulated by the ordinary `FiniteProbRecord` semantics in both
the records and the perturbation cells.  An explicit anchor proves nonempty
total mass; no inhabitant or supported atom is selected from an existential.
This construction produces profiles from raw weights.  Finding directions
that cancel a particular causal environment remains a separate obligation.
-/

/-- Raw balanced directions with a complete finite presentation and an
explicit positive baseline.  Equality concerns actual total atom mass, so
duplicates do not silently change the normalization condition. -/
structure FiniteRecordPerturbation (Ω : Type u) where
  values : List Ω
  complete : forall value, value ∈ values
  anchor : Ω
  baseline : Nat
  baselinePositive : 0 < baseline
  decrease : Ω → Nat
  increase : Ω → Nat
  massBalanced :
    FiniteProbRecord.totalMass (values.map fun value => (value, decrease value)) =
      FiniteProbRecord.totalMass (values.map fun value => (value, increase value))

namespace FiniteRecordPerturbation

open FiniteProbRecord

variable {Ω : Type u}

def baselineAtoms (p : FiniteRecordPerturbation Ω) : List (Ω × Nat) :=
  p.values.map fun value => (value, p.baseline)

def decreaseAtoms (p : FiniteRecordPerturbation Ω) : List (Ω × Nat) :=
  p.values.map fun value => (value, p.decrease value)

def increaseAtoms (p : FiniteRecordPerturbation Ω) : List (Ω × Nat) :=
  p.values.map fun value => (value, p.increase value)

private theorem baselineTotal_positive (values : List Ω) (baseline : Nat)
    (positive : 0 < baseline) (value : Ω) (member : value ∈ values) :
    0 < totalMass (values.map fun label => (label, baseline)) := by
  cases values with
  | nil => cases member
  | cons head rest =>
      change 0 < baseline + totalMass (rest.map fun label => (label, baseline))
      exact Nat.lt_of_lt_of_le positive (Nat.le_add_right _ _)

private theorem baselineMass_positive [DecidableEq Ω] (values : List Ω) (baseline : Nat)
    (positive : 0 < baseline) (value : Ω) (member : value ∈ values) :
    0 < eventMass (values.map fun label => (label, baseline)) (singletonEvent value) := by
  induction values with
  | nil => cases member
  | cons head rest inductionHypothesis =>
      cases List.mem_cons.mp member with
      | inl same =>
          subst head
          simp only [List.map_cons, eventMass, singletonEvent, decide_true, if_true]
          exact Nat.lt_of_lt_of_le positive (Nat.le_add_right _ _)
      | inr inRest =>
          have tailPositive := inductionHypothesis inRest
          change 0 < if singletonEvent value head then baseline +
            eventMass (rest.map fun label => (label, baseline)) (singletonEvent value)
            else eventMass (rest.map fun label => (label, baseline)) (singletonEvent value)
          cases singletonEvent value head
          · exact tailPositive
          · exact Nat.lt_of_lt_of_le tailPositive (Nat.le_add_left _ _)

/-- The denominator includes the full baseline and one direction's total.
Both final records use this same literal natural denominator. -/
def denominator (p : FiniteRecordPerturbation Ω) : Nat :=
  totalMass p.baselineAtoms + totalMass p.increaseAtoms

theorem denominator_positive (p : FiniteRecordPerturbation Ω) : 0 < p.denominator := by
  have baselinePositive : 0 < totalMass p.baselineAtoms :=
    baselineTotal_positive p.values p.baseline p.baselinePositive p.anchor (p.complete p.anchor)
  exact Nat.lt_of_lt_of_le baselinePositive (Nat.le_add_right _ _)

/-- The left profile receives the increase part; the right profile
receives the decrease part.  This convention gives `left + decrease =
right + increase` at every probability cell. -/
def leftRecord (p : FiniteRecordPerturbation Ω) : FiniteProbRecord Ω where
  atoms := p.baselineAtoms ++ p.increaseAtoms
  den := p.denominator
  den_pos := p.denominator_positive
  total_mass := totalMass_append _ _

def rightRecord (p : FiniteRecordPerturbation Ω) : FiniteProbRecord Ω where
  atoms := p.baselineAtoms ++ p.decreaseAtoms
  den := p.denominator
  den_pos := p.denominator_positive
  total_mass := by
    rw [totalMass_append]
    exact congrArg (fun mass => totalMass p.baselineAtoms + mass) p.massBalanced

variable [DecidableEq Ω]

def decreaseCell (p : FiniteRecordPerturbation Ω) (value : Ω) : QProb :=
  ⟨eventMass p.decreaseAtoms (singletonEvent value), p.denominator, p.denominator_positive⟩

def increaseCell (p : FiniteRecordPerturbation Ω) (value : Ω) : QProb :=
  ⟨eventMass p.increaseAtoms (singletonEvent value), p.denominator, p.denominator_positive⟩

/-- Normalization and positivity are proved for the actual finite
records.  This is not a claim that unnormalized perturbation parts are
themselves probability distributions. -/
theorem left_positive (p : FiniteRecordPerturbation Ω) (value : Ω) :
    p.leftRecord.EventPositive (singletonEvent value) := by
  change 0 < eventMass (p.baselineAtoms ++ p.increaseAtoms) (singletonEvent value)
  rw [eventMass_append]
  exact Nat.lt_of_lt_of_le
    (baselineMass_positive p.values p.baseline p.baselinePositive value (p.complete value))
    (Nat.le_add_right _ _)

theorem right_positive (p : FiniteRecordPerturbation Ω) (value : Ω) :
    p.rightRecord.EventPositive (singletonEvent value) := by
  change 0 < eventMass (p.baselineAtoms ++ p.decreaseAtoms) (singletonEvent value)
  rw [eventMass_append]
  exact Nat.lt_of_lt_of_le
    (baselineMass_positive p.values p.baseline p.baselinePositive value (p.complete value))
    (Nat.le_add_right _ _)

/-- The cell balance is literal rational arithmetic on the same supplied
value list, including repeated labels and zero direction weights. -/
theorem cells_balanced (p : FiniteRecordPerturbation Ω) (value : Ω) :
    QProb.Equiv
      (QProb.add (p.leftRecord.probVal (singletonEvent value)) (p.decreaseCell value))
      (QProb.add (p.rightRecord.probVal (singletonEvent value)) (p.increaseCell value)) := by
  simp only [QProb.Equiv, QProb.add, leftRecord, rightRecord, probVal,
    decreaseCell, increaseCell, eventMass_append, Nat.add_mul]
  ac_rfl

end FiniteRecordPerturbation
end Probability
end Thesis
