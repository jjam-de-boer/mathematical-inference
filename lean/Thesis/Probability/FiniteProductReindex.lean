import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Reindexing independent finite records for arbitrary events

Fresh private SCM inputs are installed noise-first, whereas probability
channels commonly keep their original source first.  Rectangular independence
alone does not identify these presentations: a conditioning event can inspect
all coordinates together.  The identities here therefore retain an arbitrary
Boolean event while explicitly swapping or reassociating the weighted products.

The proofs concern natural event masses before normalization.  Repeated labels,
zero-weight atoms, and unequal factor denominators are all allowed.  No source
enumeration, chosen coupling, or positive event is required.  The records need
only their existing positive total denominators.
-/

private theorem weightedCartesian_cons_left_mass (value : Ω) (weight : Nat)
    (left : List (Ω × Nat)) (right : List (X × Nat)) (event : Event (Ω × X)) :
    eventMass (weightedCartesian ((value, weight) :: left) right) event =
      weight * eventMass right (fun sample => event (value, sample)) +
        eventMass (weightedCartesian left right) event := by
  change eventMass
    (right.map (fun atom => ((value, atom.1), weight * atom.2)) ++
      weightedCartesian left right) event = _
  rw [eventMass_append, eventMass_map_weight]

/-- A right-hand atom contributes one whole column of the weighted product.
This local expansion is proved without imposing an order on either label type. -/
private theorem weightedCartesian_cons_right_mass (left : List (Ω × Nat))
    (value : X) (weight : Nat) (right : List (X × Nat)) (event : Event (Ω × X)) :
    eventMass (weightedCartesian left ((value, weight) :: right)) event =
      weight * eventMass left (fun sample => event (sample, value)) +
        eventMass (weightedCartesian left right) event := by
  induction left with
  | nil => simp only [weightedCartesian, List.flatMap_nil, eventMass, Nat.mul_zero, Nat.zero_add]
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨sample, mass⟩
      rw [weightedCartesian_cons_left_mass, weightedCartesian_cons_left_mass, inductionHypothesis]
      cases selected : event (sample, value) <;>
        simp only [eventMass, selected, Bool.false_eq_true, ↓reduceIte, Nat.mul_add]
      · ac_rfl
      · ac_rfl

/-- Finite Fubini at raw event-mass level.  Swapping the factors requires
swapping the event's arguments as well; the lists themselves need not be equal. -/
theorem eventMass_weightedCartesian_swap (left : List (Ω × Nat))
    (right : List (X × Nat)) (event : Event (Ω × X)) :
    eventMass (weightedCartesian left right) event =
      eventMass (weightedCartesian right left) (fun pair => event (pair.2, pair.1)) := by
  induction left with
  | nil =>
      induction right with
      | nil => rfl
      | cons _ _ inductionHypothesis => exact inductionHypothesis
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      rw [weightedCartesian_cons_left_mass, weightedCartesian_cons_right_mass,
        inductionHypothesis]

/-- Reassociation preserves the complete weighted atom list after the
displayed relabelling.  Only associativity of natural multiplication is used. -/
theorem weightedCartesian_assoc (left : List (Ω × Nat))
    (middle : List (X × Nat)) (right : List (Y × Nat)) :
    weightedCartesian (weightedCartesian left middle) right =
      (weightedCartesian left (weightedCartesian middle right)).map
        (fun atom => (((atom.1.1, atom.1.2.1), atom.1.2.2), atom.2)) := by
  simp only [weightedCartesian, List.flatMap_map, List.map_flatMap,
    List.flatMap_assoc, List.map_map, Function.comp_def, Nat.mul_assoc]

/-- Full-event probability equality under an explicit swap.  This is stronger
than the product law for rectangular events and applies to posterior evidence. -/
theorem product_swap_probVal (left : FiniteProbRecord Ω) (right : FiniteProbRecord X)
    (event : Event (Ω × X)) :
    QProb.Equiv ((left.product right).probVal event)
      ((right.product left).probVal (fun pair => event (pair.2, pair.1))) := by
  simp only [product, probVal, QProb.Equiv, eventMass_weightedCartesian_swap left.atoms right.atoms event]
  ac_rfl

/-- Full-event probability equality under the explicit reassociation map. -/
theorem product_assoc_probVal (left : FiniteProbRecord Ω)
    (middle : FiniteProbRecord X) (right : FiniteProbRecord Y)
    (event : Event ((Ω × X) × Y)) :
    QProb.Equiv (((left.product middle).product right).probVal event)
      ((left.product (middle.product right)).probVal
        (fun triple => event ((triple.1, triple.2.1), triple.2.2))) := by
  simp only [product, probVal, QProb.Equiv, weightedCartesian_assoc, Nat.mul_assoc]
  exact congrArg (fun mass => mass * (left.den * (middle.den * right.den)))
    (eventMass_map_labels (weightedCartesian left.atoms (weightedCartesian middle.atoms right.atoms))
      (fun triple => ((triple.1, triple.2.1), triple.2.2)) event)

/-- Move two newly installed independent inputs behind their original source.
The left expression has the actual nested installation order; the right
expression has the source-first channel order.  The identity holds for every
mixed event, not merely after marginalizing the two private inputs. -/
theorem product_cycle_probVal (source : FiniteProbRecord Ω)
    (noise : FiniteProbRecord X) (mask : FiniteProbRecord Y)
    (event : Event ((Ω × X) × Y)) :
    QProb.Equiv ((noise.product (mask.product source)).probVal
      (fun triple => event ((triple.2.2, triple.1), triple.2.1)))
      (((source.product noise).product mask).probVal event) := by
  have first := noise.product_swap_probVal (mask.product source)
    (fun triple => event ((triple.2.2, triple.1), triple.2.1))
  have second := mask.product_assoc_probVal source noise
    (fun triple => event ((triple.1.2, triple.2), triple.1.1))
  have third := mask.product_swap_probVal (source.product noise)
    (fun triple => event ((triple.2.1, triple.2.2), triple.1))
  exact QProb.equiv_trans first (QProb.equiv_trans second third)

end FiniteProbRecord
end Probability
end Thesis
