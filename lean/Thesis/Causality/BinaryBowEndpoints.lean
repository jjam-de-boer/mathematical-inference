import Thesis.Causality.BinaryBowModel
import Thesis.Probability.BooleanNoise

namespace Thesis
namespace Causality
namespace BinaryBow

open Probability

/-!
# Attained consistency endpoints for every rational binary bow law

The lower endpoint is the observed mass of `X = action, Y = true`.
The upper endpoint adds the observed mass of `X != action`.  The models from
`BinaryBowModel` attain these values by returning false or true precisely
off their factual treatment.  All claims quantify over the supplied whole
finite rational law; they are not tied to a hand-selected fixture.

The whole observational laws of the endpoint models agree, and their graph
compatibility is unchanged.  A positive outside-action mass strictly
separates the endpoints.  These constructive ingredients will supply the
fixed-law necessity theorem and actual native countermodels.  Attainment of
every intermediate rational value requires an additional mixture model and
is not inferred merely from having the two endpoints.
-/

/-- Observational membership in the requested treatment value. -/
def actionEvent (action : Bool) : Event signature.Assignment :=
  fun factual => decide (factual x = action)

def lowerEvent (action : Bool) : Event signature.Assignment :=
  fun factual => actionEvent action factual && factual y

def outsideEvent (action : Bool) : Event signature.Assignment :=
  fun factual => !actionEvent action factual

def lower (law : FiniteProbRecord signature.Assignment) (action : Bool) : QProb :=
  law.probVal (lowerEvent action)

def outside (law : FiniteProbRecord signature.Assignment) (action : Bool) : QProb :=
  law.probVal (outsideEvent action)

def upper (law : FiniteProbRecord signature.Assignment) (action : Bool) : QProb :=
  QProb.add (lower law action) (outside law action)

/-- Small Boolean identities handle both action values uniformly.  They
case-split supplied Boolean data, not arbitrary equality propositions. -/
private theorem lower_outcome (action factualX factualY : Bool) :
    (if action = factualX then factualY else false) =
      (decide (factualX = action) && factualY) := by
  cases action <;> cases factualX <;> cases factualY <;> rfl

private theorem upper_outcome (action factualX factualY : Bool) :
    (if action = factualX then factualY else true) =
      ((decide (factualX = action) && factualY) || !decide (factualX = action)) := by
  cases action <;> cases factualX <;> cases factualY <;> rfl

/-- The lower model attains the factual action-and-outcome mass exactly. -/
theorem lower_endpoint (law : FiniteProbRecord signature.Assignment) (action : Bool) :
    QProb.Equiv
      ((model law false).interventionalValue (intervention action).value (fun sample => sample y))
      (lower law action) :=
  QProb.equiv_trans ((model law false).interventionalValue_eq (intervention action).value _)
    (QProb.equiv_trans
      (law.map_probVal (fun factual _ => factual)
        (fun unit => (model law false).evalUnder (intervention action).value unit y))
      (law.probVal_congr _ _ (fun factual =>
        (eval_intervened_y law false action (fun _ => factual)).trans
          (lower_outcome action (factual x) (factual y)))))

/-- The factual contributing event and the other-action event are disjoint
at every label, including labels carrying zero mass. -/
private theorem lower_outside_disjoint (action : Bool) :
    disjoint (lowerEvent action) (outsideEvent action) := by
  intro factual selected excluded
  have inside := (Bool.and_eq_true_iff.mp selected).1
  simp only [outsideEvent, inside, Bool.not_true, Bool.false_eq_true] at excluded

/-- The upper model attains factual mass plus the whole other-action mass.
The sum follows from disjoint-event probability, not informal counting. -/
theorem upper_endpoint (law : FiniteProbRecord signature.Assignment) (action : Bool) :
    QProb.Equiv
      ((model law true).interventionalValue (intervention action).value (fun sample => sample y))
      (upper law action) := by
  have eventEquality : QProb.Equiv
      ((model law true).interventionalValue (intervention action).value (fun sample => sample y))
      (law.probVal (union (lowerEvent action) (outsideEvent action))) :=
    QProb.equiv_trans ((model law true).interventionalValue_eq (intervention action).value _)
      (QProb.equiv_trans
        (law.map_probVal (fun factual _ => factual)
          (fun unit => (model law true).evalUnder (intervention action).value unit y))
        (law.probVal_congr _ _ (fun factual =>
          (eval_intervened_y law true action (fun _ => factual)).trans
            (upper_outcome action (factual x) (factual y)))))
  exact QProb.equiv_trans eventEquality
    (law.probVal_union_disjoint _ _ (lower_outside_disjoint action))

/-- The two constructed models preserve the same entire observed law.
This is the observational premise needed by a genuine countermodel pair. -/
theorem endpoints_observationally_equal (law : FiniteProbRecord signature.Assignment) :
    ObservationallyEquivalent (model law false) (model law true) := by
  intro event
  exact QProb.equiv_trans (observationalValue_preserved law false event)
    (QProb.equiv_symm (observationalValue_preserved law true event))

/-- Other-action mass vanishes exactly when the requested action has
probability one.  This remains a whole-population rational equality, not an
inference from absent labels or from zero frequency in a sample. -/
theorem outside_zero_iff_action_one (law : FiniteProbRecord signature.Assignment) (action : Bool) :
    (outside law action).num = 0 ↔ QProb.Equiv (law.probVal (actionEvent action)) QProb.one := by
  have partition := (FiniteProbRecord.eventMass_add_complement law.atoms (actionEvent action)).trans law.total_mass
  change FiniteProbRecord.eventMass law.atoms (outsideEvent action) = 0 ↔ _
  simp only [QProb.Equiv, FiniteProbRecord.probVal, QProb.one, Nat.mul_one, Nat.one_mul]
  change FiniteProbRecord.eventMass law.atoms (outsideEvent action) = 0 ↔
    FiniteProbRecord.eventMass law.atoms (actionEvent action) = law.den
  change FiniteProbRecord.eventMass law.atoms (actionEvent action) +
    FiniteProbRecord.eventMass law.atoms (outsideEvent action) = law.den at partition
  omega

/-- Positive other-action mass gives a strict rational gap.  Both
observational probabilities share the supplied record's denominator, and
its positivity justifies scaling the strict natural-weight comparison. -/
theorem lower_lt_upper_of_outside_positive (law : FiniteProbRecord signature.Assignment) (action : Bool)
    (positive : 0 < (outside law action).num) : QProb.LT (lower law action) (upper law action) := by
  have increment : 0 < (outside law action).num * law.den := Nat.mul_pos positive law.den_pos
  have numerator : (lower law action).num * law.den <
      (lower law action).num * law.den + (outside law action).num * law.den :=
    Nat.lt_add_of_pos_right increment
  have scaled := Nat.mul_lt_mul_of_pos_right numerator law.den_pos
  change (lower law action).num * (law.den * law.den) <
    ((lower law action).num * law.den + (outside law action).num * law.den) * law.den
  simpa only [Nat.mul_assoc] using scaled

end BinaryBow
end Causality
end Thesis
