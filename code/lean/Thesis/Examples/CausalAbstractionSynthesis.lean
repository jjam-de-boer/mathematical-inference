import Thesis.CausalTransport.CausalAbstractionSynthesis
import Thesis.Examples.CausalAbstractionExtension

/-!
# Synthesis succeeds, rejects incomplete coverage, and refutes conflicting lifts

The AND example reuses the earlier three-to-two observed-node merge but passes
only its structural aggregation and microscopic model into the new procedure.
The old macro model appears solely as an independent completeness witness: it
is not an input to the solver. The feasibility theorem ranges over every exact
rational solution and permits the zero cells in the deterministic copy law.

The second microscopic SCM copies A into Y and merges A,B by OR. Both settings
(A=true,B=false) and (A=false,B=true) force the aggregate to true, but they force
different outcomes. A single macro do(C=true) cannot have both outcome laws.
Here the protocol is structurally valid and covers its required actions, so
the procedure returns numerical infeasibility rather than a protocol error.
-/

namespace Thesis.Examples.CausalAbstractionSynthesis
open Probability Causality
open Causality.CausalAbstractionSynthesis
open CausalAbstraction

/-- The required family contains observation and the existing unique-preimage
AND=true surgery. Other defined omega entries are checked as well. -/
def andSpecification : Specification microSignature macroSignature where
  microModel := microModel
  aggregation := Aggregation.ofCoarseGraining andCoarsening
  omega := andOmega
  required := [HardIntervention.empty macroSignature, macroDoTrue]

theorem and_protocol_valid : andSpecification.Valid := by decide +kernel

/-- The previously established complete-law theorem is used as a witness
for the new solver's completeness direction, with no prefilled mass vector. -/
theorem and_existing_model_fits : andSpecification.Fits andMacro := by
  intro intervention action defined event
  exact and_intervention_exact intervention action defined event

theorem and_synthesis_succeeds :
    andSpecification.solve.IsFeasible := by
  exact (andSpecification.solve_success_iff).mpr
    ⟨and_protocol_valid, andMacro, and_existing_model_fits⟩

/-- Extract the solver's own solution. The old AND model is used only to
rule out an impossible refutation branch: the returned mass record comes
from `solve`, and is neither copied from nor chosen to equal that witness.
The branch inspection is constructive and needs no choice principle. -/
def andSolution : andSpecification.Solution :=
  match andSpecification.solve with
  | .feasible solution => solution
  | .invalid invalid => False.elim (invalid and_protocol_valid)
  | .infeasible _ certificate =>
      False.elim (andSpecification.infeasible_not_exists certificate
        ⟨andMacro, and_existing_model_fits⟩)

/-- The constructed model, rather than merely the supplied witness, has
zero mass on the impossible copy outcome. The observation component of the
solution transfers the micro law, so no assumption of a positive table is
smuggled into the linear construction. -/
theorem and_synthesized_retains_zero :
    (andSolution.macroModel.observationalValue
      (FiniteProbRecord.singletonEvent (coarseState false true))).num = 0 := by
  have exactObservation := andSolution.observation
    (FiniteProbRecord.singletonEvent (coarseState false true))
  have microZero : (andSpecification.microModel.observationalValue
      (fun state => FiniteProbRecord.singletonEvent (coarseState false true)
        (andSpecification.aggregation.assignmentMap state))).num = 0 := by
    decide +kernel
  change _ * _ = _ * _ at exactObservation
  simp only [microZero, Nat.zero_mul] at exactObservation
  exact (Nat.mul_eq_zero.mp exactObservation).resolve_right
    (Nat.ne_of_gt (andSpecification.microModel.observationalValue
      (fun state => FiniteProbRecord.singletonEvent (coarseState false true)
        (andSpecification.aggregation.assignmentMap state))).den_pos)

/-- This deterministic macro copy law contains genuine zero-probability
outcomes. Feasibility does not replace them with a positive smoothing row. -/
theorem and_witness_retains_zero :
    (andMacro.observationalValue
      (FiniteProbRecord.singletonEvent (coarseState false true))).num = 0 := by
  decide +kernel

/-- Removing required observation is a protocol error, even though all
numerical equations remain the same as in the feasible AND specification. -/
def missingObservation : Specification microSignature macroSignature :=
  { andSpecification with required := [macroDoTrue] }

theorem missing_observation_invalid : ¬ missingObservation.Valid := by
  decide +kernel

theorem missing_observation_rejected :
    missingObservation.solve.IsInvalid :=
  (missingObservation.solve_invalid_iff).mpr missing_observation_invalid

/-- Requiring an AND=false macro action without admitting a microscopic
representative is rejected as missing coverage, rather than accepted because
the remaining response equations have a solution. -/
def missingRepresentative : Specification microSignature macroSignature :=
  { andSpecification with
    required := [HardIntervention.empty macroSignature,
      coarseAction (some false) none] }

theorem missing_representative_invalid : ¬ missingRepresentative.Valid := by
  decide +kernel

theorem missing_representative_rejected :
    missingRepresentative.solve.IsInvalid :=
  (missingRepresentative.solve_invalid_iff).mpr missing_representative_invalid

/-- Keep the same independent cause sources and the same allowed DAG, but
let the response read A alone. An allowed parent need not be essential. -/
def copyFirstModel : ExactModel microSignature :=
  { microModel with
    mechanism := fun child parents inputs =>
      if response : child.val = 2 then
        parents (0 : Fin 3) (by simp [microSignature, response])
      else microModel.mechanism child parents inputs }

def firstOnly : HardIntervention microSignature :=
  fineAction (some true) (some false) none

def secondOnly : HardIntervention microSignature :=
  fineAction (some false) (some true) none

/-- This is a deliberately many-to-one action correspondence: two different
ways of realizing the same forced OR value are both required to mean do(C=1). -/
def conflictingOmega (intervention : HardIntervention microSignature) :
    Option (HardIntervention macroSignature) :=
  if intervention = HardIntervention.empty microSignature then
    some (HardIntervention.empty macroSignature)
  else if intervention = firstOnly ∨ intervention = secondOnly then
    some macroDoTrue
  else none

def conflictingSpecification : Specification microSignature macroSignature where
  microModel := copyFirstModel
  aggregation := Aggregation.ofCoarseGraining orCoarsening
  omega := conflictingOmega
  required := [HardIntervention.empty macroSignature, macroDoTrue]

theorem conflicting_protocol_valid : conflictingSpecification.Valid := by
  decide +kernel

theorem first_only_defined : conflictingSpecification.omega firstOnly = some macroDoTrue := by
  decide +kernel

theorem second_only_defined : conflictingSpecification.omega secondOnly = some macroDoTrue := by
  decide +kernel

theorem first_only_outcome : QProb.Equiv
    (copyFirstModel.interventionalValue firstOnly.value
      (fun state => yTrue (mergeAssignment Bool.or state))) QProb.one := by
  decide +kernel

theorem second_only_outcome : QProb.Equiv
    (copyFirstModel.interventionalValue secondOnly.value
      (fun state => yTrue (mergeAssignment Bool.or state))) QProb.zero := by
  decide +kernel

/-- No choice of hidden alphabet, rational denominator, or shared source
can make one macro experiment have both the sure and impossible Y event. -/
theorem conflicting_no_macro_model :
    ¬ ∃ macroModel : ExactModel macroSignature, conflictingSpecification.Fits macroModel := by
  rintro ⟨macroModel, fitted⟩
  have left := QProb.equiv_trans
    (fitted firstOnly macroDoTrue first_only_defined yTrue) first_only_outcome
  have right := QProb.equiv_trans
    (fitted secondOnly macroDoTrue second_only_defined yTrue) second_only_outcome
  have impossible : QProb.Equiv QProb.one QProb.zero :=
    QProb.equiv_trans (QProb.equiv_symm left) right
  cases impossible

theorem conflicting_synthesis_refutes :
    conflictingSpecification.solve.IsInfeasible := by
  exact (conflictingSpecification.solve_infeasible_iff).mpr
    ⟨conflicting_protocol_valid, conflicting_no_macro_model⟩

/-! ## A small instance which executes the complete solver

The preceding two-node target has eight response tables. Its existence and
failure theorems exercise the unrestricted completeness contract without
forcing a large elimination trace during every import. This one-node target
instead has exactly two response tables. It still merges the two independent
micro causes by AND, and checks both observation and the double-true surgery.
The computed success below is obtained by reducing `solve` itself: no macro
model or mass-vector witness is supplied to establish this result.
-/

/-- A single Boolean macro variable with no directed parents. -/
def compactSignature : ObservedSignature where
  count := 1
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed _ _ := false
  directed_earlier := by intro _ _ impossible; cases impossible

/-- The two-cause AND aggregation discards the already determined response
coordinate. Its one cluster is nonempty, and locality is proved explicitly. -/
def compactAggregation : Aggregation microSignature compactSignature where
  cluster _ member := decide (member.val < 2)
  cluster_nonempty := fun _ => ⟨(0 : Fin 3), rfl⟩
  cluster_disjoint := by
    intro first second different
    have firstBound : first.val < 1 := first.isLt
    have secondBound : second.val < 1 := second.isLt
    exact False.elim (different (Fin.ext (by omega)))
  assignmentMap state _ := state (0 : Fin 3) && state (1 : Fin 3)
  coordinate_local := by
    intro node first second agree
    change (first (0 : Fin 3) && first (1 : Fin 3)) =
      (second (0 : Fin 3) && second (1 : Fin 3))
    rw [agree (0 : Fin 3) rfl, agree (1 : Fin 3) rfl]

/-- Force the aggregated AND coordinate to true. -/
def compactDoTrue : HardIntervention compactSignature :=
  (HardIntervention.empty compactSignature).set (0 : Fin 1) true

/-- Only observation and the unique double-true lift are admitted here. -/
def compactOmega (intervention : HardIntervention microSignature) :
    Option (HardIntervention compactSignature) :=
  if intervention = HardIntervention.empty microSignature then
    some (HardIntervention.empty compactSignature)
  else if intervention = microDoubleTrue then some compactDoTrue
  else none

/-- All model-construction input is microscopic; the target law is unknown. -/
def compactSpecification : Specification microSignature compactSignature where
  microModel := microModel
  aggregation := compactAggregation
  omega := compactOmega
  required := [HardIntervention.empty compactSignature, compactDoTrue]

theorem compact_protocol_valid : compactSpecification.Valid := by decide +kernel

theorem compact_response_carrier_size :
    (SharedResponse.enumeration compactSignature).length = 2 := by decide +kernel

/-- A runnable summary of the actual solver branch. The main workflow can
include this result without evaluating the larger eight-table example. -/
def compactSynthesisOutcome : String :=
  match compactSpecification.solve with
  | .invalid _ => "invalid protocol"
  | .feasible _ => "constructed AND abstraction"
  | .infeasible _ _ => "infeasible abstraction"

/-- This checked reduction runs the feasibility algorithm on the actual
constraints, instead of deducing success from a supplied macro witness. -/
theorem compact_synthesis_executes :
    compactSynthesisOutcome = "constructed AND abstraction" := by decide +kernel

/-- Extract the computed solution using the checked execution result to
exclude refutation. Unlike `andSolution`, this extraction uses no independently
supplied macro model even to establish that the successful branch is reached. -/
def compactSolution : compactSpecification.Solution :=
  match outcome : compactSpecification.solve with
  | .feasible solution => solution
  | .invalid invalid => False.elim (invalid compact_protocol_valid)
  | .infeasible _ _ => False.elim (by
      have branch := compact_synthesis_executes
      simp only [compactSynthesisOutcome, outcome] at branch
      exact (by decide : "infeasible abstraction" ≠ "constructed AND abstraction") branch)

/-- The solver's actual model retains the impossible false outcome after
forcing the AND aggregate true. This is a defined zero, not a missing law. -/
theorem compact_constructed_zero :
    (compactSolution.macroModel.interventionalValue compactDoTrue.value
      (fun state => !(state (0 : Fin 1)))).num = 0 := by
  have agreement := compactSolution.fits microDoubleTrue compactDoTrue
    (by decide +kernel) (fun state => !(state (0 : Fin 1)))
  have microZero : (compactSpecification.microModel.interventionalValue microDoubleTrue.value
      (fun state => !(compactSpecification.aggregation.assignmentMap state (0 : Fin 1)))).num = 0 := by
    decide +kernel
  change _ * _ = _ * _ at agreement
  simp only [microZero, Nat.zero_mul] at agreement
  exact (Nat.mul_eq_zero.mp agreement).resolve_right
    (Nat.ne_of_gt (compactSpecification.microModel.interventionalValue microDoubleTrue.value
      (fun state => !(compactSpecification.aggregation.assignmentMap state (0 : Fin 1)))).den_pos)

end Thesis.Examples.CausalAbstractionSynthesis
