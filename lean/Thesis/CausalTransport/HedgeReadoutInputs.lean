import Thesis.CausalTransport.HedgeReadoutEvaluation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Independent inputs indexed by readout instructions

The earlier node-indexed encoding is useful for pivot-distinct plans, but
repeated instructions at one pivot must not be forced to share a bit.  This
module gives every occurrence its own actual input.  Its recursive tuple
type follows the list, so neither a chosen enumeration nor an arbitrary
function equality is needed to distinguish two occurrences of the same row.

The input record is the literal independent product of the instructions'
stated noise records.  The mechanism theorem respects installation order;
the probability theorem represents the entire folded SCM prior, including
every independent repeated factor.  Thus a later comparison may average over
all inputs before comparing the two models.  Equality on each fixed-input
slice is sufficient, but is not silently made a necessary requirement.

The tuple stores the tail first and the head bit second.  This follows the
actual folded prior, where later fresh factors are outside earlier factors.
It is only an encoding convention: evaluation still installs the head first.
-/

namespace HedgeReadoutInputs

/-- One Boolean per instruction occurrence, even when pivots repeat. -/
def Inputs : List (HedgeReadoutStep S) -> Type
  | [] => Unit
  | _step :: rest => Inputs rest × Bool

/-- The actual independent input law.  Each occurrence contributes its
own factor with its own weights; no support or bias condition is imposed. -/
def distribution : (steps : List (HedgeReadoutStep S)) -> FiniteProbRecord (Inputs steps)
  | [] => ⟨[((), 1)], 1, by decide, rfl⟩
  | step :: rest => (distribution rest).product step.noise

/-- Embed a node-indexed family in this more general representation.  It
is useful for comparing old APIs, but does not identify the independent
bits of a repeated-pivot plan. -/
def ofNodeBits (bits : Fin S.count -> Bool) : (steps : List (HedgeReadoutStep S)) -> Inputs steps
  | [] => ()
  | step :: rest => (ofNodeBits bits rest, bits step.pivot)

/-- Compose the installed responses using the independent occurrence
inputs.  Every response sees the final current parents at this same row. -/
def response (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (parents : S.ParentValues child) :
    (steps : List (HedgeReadoutStep S)) -> Inputs steps -> S.Value child -> S.Value child
  | [], _inputs, old => old
  | step :: rest, inputs, old => response rich child parents rest inputs.1
      (step.responseAt rich child parents inputs.2 old)

theorem response_ofNodeBits (rich : ObservedSignature.ValueRich S)
    (bits : Fin S.count -> Bool) (child : Fin S.count) (parents : S.ParentValues child)
    (steps : List (HedgeReadoutStep S)) (old : S.Value child) :
    response rich child parents steps (ofNodeBits bits steps) old =
      HedgeReadoutEvaluation.response rich bits child parents steps old := by
  induction steps generalizing old with
  | nil => rfl
  | cons step rest inductionHypothesis => exact inductionHypothesis _

/-! ## Reassociate the explicit finite products, without selecting a coupling -/

private theorem weightedCartesian_assoc (left : List (Ω × Nat))
    (middle : List (X × Nat)) (right : List (Y × Nat)) :
    FiniteProbRecord.weightedCartesian (FiniteProbRecord.weightedCartesian left middle) right =
      (FiniteProbRecord.weightedCartesian left (FiniteProbRecord.weightedCartesian middle right)).map
        (fun atom => (((atom.1.1, atom.1.2.1), atom.1.2.2), atom.2)) := by
  simp only [FiniteProbRecord.weightedCartesian, List.flatMap_map, List.map_flatMap,
    List.flatMap_assoc, List.map_map, Function.comp_def, Nat.mul_assoc]

private theorem product_assoc_probVal (left : FiniteProbRecord Ω)
    (middle : FiniteProbRecord X) (right : FiniteProbRecord Y)
    (event : Event ((Ω × X) × Y)) :
    QProb.Equiv (((left.product middle).product right).probVal event)
      ((left.product (middle.product right)).probVal
        (fun triple => event ((triple.1, triple.2.1), triple.2.2))) := by
  simp only [FiniteProbRecord.product, FiniteProbRecord.probVal, QProb.Equiv,
    weightedCartesian_assoc, Nat.mul_assoc]
  exact congrArg (fun mass => mass * (left.den * (middle.den * right.den)))
    (FiniteProbRecord.eventMass_map_labels
      (FiniteProbRecord.weightedCartesian left.atoms
        (FiniteProbRecord.weightedCartesian middle.atoms right.atoms))
      (fun triple => ((triple.1, triple.2.1), triple.2.2)) event)

end HedgeReadoutInputs

/-- Encode each supplied occurrence input in the real dependent latent
extension created by that instruction.  Repeated pivots receive independent
coordinates; the head is installed before the tail. -/
def FiniteLatentSCM.hedgeReadoutAssignmentWithInputs
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S) :
    (steps : List (HedgeReadoutStep S)) -> HedgeReadoutInputs.Inputs steps ->
      base.latent.Assignment -> (base.withHedgeReadouts rich steps).latent.Assignment
  | [], _inputs, unit => unit
  | step :: rest, inputs, unit =>
      (step.apply rich base).hedgeReadoutAssignmentWithInputs rich rest inputs.1
        (PrivateBooleanNoise.assignment base.latent inputs.2 unit)

theorem FiniteLatentSCM.hedgeReadoutAssignmentWithInputs_ofNodeBits
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S)) (bits : Fin S.count -> Bool)
    (unit : base.latent.Assignment) :
    base.hedgeReadoutAssignmentWithInputs rich steps (HedgeReadoutInputs.ofNodeBits bits steps) unit =
      base.hedgeReadoutAssignment rich bits steps unit := by
  induction steps generalizing base with
  | nil => rfl
  | cons step rest inductionHypothesis => exact inductionHypothesis (step.apply rich base) _

/-- The final mechanism is exactly the ordered occurrence-indexed
composition at arbitrary parent inputs.  This theorem requires neither
distinct pivots nor any claim about observational equality. -/
theorem FiniteLatentSCM.withHedgeReadouts_mechanism_eq_responseWithInputs
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S)) (inputs : HedgeReadoutInputs.Inputs steps)
    (unit : base.latent.Assignment) (child : Fin S.count) (parents : S.ParentValues child) :
    (base.withHedgeReadouts rich steps).mechanism child parents
        (fun root _incident => base.hedgeReadoutAssignmentWithInputs rich steps inputs unit root) =
      HedgeReadoutInputs.response rich child parents steps inputs
        (base.mechanism child parents (fun root _incident => unit root)) := by
  induction steps generalizing base with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      have head := base.withHedgeReadouts_mechanism_eq_response rich [step]
        (fun _ => inputs.2) unit child parents
      have headResponse :
          (step.apply rich base).mechanism child parents
              (fun root _incident => PrivateBooleanNoise.assignment base.latent inputs.2 unit root) =
            step.responseAt rich child parents inputs.2
              (base.mechanism child parents (fun root _incident => unit root)) := head
      exact (inductionHypothesis (step.apply rich base) inputs.1 _).trans
        (congrArg (HedgeReadoutInputs.response rich child parents rest inputs.1) headResponse)

/-- The entire real folded prior is the pushforward of the independent
instruction-input record and the original prior.  This is a full-event
identity, not only a rectangular-event law or a fixed-input sufficient
condition.  Repeated pivots, arbitrary order, repeated labels, unequal
weights, and unsupported noise values are all included. -/
theorem FiniteLatentSCM.withHedgeReadouts_prior_probVal_equiv_inputs
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (event : Event (base.withHedgeReadouts rich steps).latent.Assignment) :
    QProb.Equiv ((base.withHedgeReadouts rich steps).prior.probVal event)
      (((HedgeReadoutInputs.distribution steps).product base.prior).probVal
        (fun pair => event (base.hedgeReadoutAssignmentWithInputs rich steps pair.1 pair.2))) := by
  induction steps generalizing base with
  | nil =>
      simp only [HedgeReadoutInputs.distribution, FiniteLatentSCM.withHedgeReadouts,
        FiniteLatentSCM.hedgeReadoutAssignmentWithInputs, FiniteProbRecord.product,
        FiniteProbRecord.weightedCartesian, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Nat.one_mul, FiniteProbRecord.eventMass_map_labels,
        FiniteProbRecord.probVal, QProb.Equiv]
  | cons step rest inductionHypothesis =>
      have tail := inductionHypothesis (step.apply rich base) event
      let encodedEvent : Event (HedgeReadoutInputs.Inputs rest × (step.apply rich base).latent.Assignment) :=
        fun pair => event ((step.apply rich base).hedgeReadoutAssignmentWithInputs rich rest pair.1 pair.2)
      have encoded := (HedgeReadoutInputs.distribution rest).product_map_right_probVal
        (step.noise.product base.prior)
        (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2) encodedEvent
      have associated := HedgeReadoutInputs.product_assoc_probVal
        (HedgeReadoutInputs.distribution rest) step.noise base.prior
        (fun pair => event (base.hedgeReadoutAssignmentWithInputs rich (step :: rest) pair.1 pair.2))
      exact QProb.equiv_trans tail
        (QProb.equiv_trans encoded (QProb.equiv_symm associated))

end Causality
end Thesis
