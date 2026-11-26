import Thesis.Examples.CatalogueSampling
import Thesis.Examples.CausalAbstractionSynthesis

/-!
# Synthesizing an outcome-only abstraction of the actual posterior catalogue

The input SCMs are exactly `CatalogueSampling.twoModels`: the copy-chain
and independent-outcome hypotheses used for the finite-sample posterior.
The target retains only Y. Its cluster is the singleton Y, and its protocol
admits observation and the two direct interventions on Y. Every macro action
has a declared micro representative, and observation is explicitly required.

The original do(X=true) experiment is deliberately excluded by this protocol.
This is a loss of the original causal query when X is discarded, rather than
a missing representative for one of the required macro actions. The output
does not answer that original query through an invented macro intervention.

For each actual catalogue model the exhaustive target response carrier has
two atoms. The checked success theorem reduces the rational solver itself;
neither a preselected macro SCM nor a supplied feasible mass vector is used.
An extractable `Solution` exposes the constructed SCM and exactness/coverage
certificates. The runtime report also inspects the actual solver result.
-/

namespace Thesis.Examples.InferenceWorkflowAbstraction

open Probability Causality
open Causality.BinaryBow
open Causality.CausalAbstractionSynthesis
open Causality.Examples.CatalogueSampling
open Causality.Examples.CatalogueInference
open Thesis.Examples.CausalAbstractionSynthesis

/-- Directly force the retained micro outcome, leaving X unforced. -/
def doY (value : Bool) : HardIntervention signature :=
  (HardIntervention.empty signature).set y value

/-- The corresponding direct setting of the sole target coordinate. -/
def macroDo (value : Bool) : HardIntervention compactSignature :=
  (HardIntervention.empty compactSignature).set (0 : Fin 1) value

/-- The aggregation retains precisely Y and discards X. Its locality proof
uses agreement on that singleton cluster, with no probability assumption. -/
def aggregation : Aggregation signature compactSignature where
  cluster _ := NodeSet.singleton y
  cluster_nonempty := fun _ => ⟨y, (NodeSet.singleton_eq_true_iff y y).mpr rfl⟩
  cluster_disjoint := by
    intro first second different
    have firstBound : first.val < 1 := first.isLt
    have secondBound : second.val < 1 := second.isLt
    exact False.elim (different (Fin.ext (by omega)))
  assignmentMap state _ := state y
  coordinate_local := by
    intro _node first second agree
    exact agree y ((NodeSet.singleton_eq_true_iff y y).mpr rfl)

/-- A literal three-experiment protocol. Setting X, alone or together with
other targets, has no entry; it is not silently mapped to observation. -/
def omega (intervention : HardIntervention signature) :
    Option (HardIntervention compactSignature) :=
  if intervention = HardIntervention.empty signature then
    some (HardIntervention.empty compactSignature)
  else if intervention = doY false then some (macroDo false)
  else if intervention = doY true then some (macroDo true)
  else none

/-- Synthesize the coarse law of the very same generative catalogue atom.
Only the micro model varies with the hypothesis index. -/
def specification (i : Fin 2) : Specification signature compactSignature where
  microModel := twoModels i
  aggregation := aggregation
  omega := omega
  required := [HardIntervention.empty compactSignature, macroDo false, macroDo true]

/-- Observation is an explicit correspondence entry. -/
theorem observation_defined :
    omega (HardIntervention.empty signature) = some (HardIntervention.empty compactSignature) := by
  decide +kernel

/-- Both direct Y settings have their stated, distinct macro actions. -/
theorem intervention_defined (value : Bool) : omega (doY value) = some (macroDo value) := by
  cases value <;> decide +kernel

/-- The original experiment is excluded by the declared map. This does not
say that a required macro action lacks a micro representative. -/
theorem original_doX_excluded : omega doX = none := by decide +kernel

/-- Forced-value compatibility and required-action coverage hold before
any numerical model feasibility is considered. -/
theorem protocol_valid (i : Fin 2) : (specification i).Valid := by
  change (specification (0 : Fin 2)).Valid
  decide +kernel

/-- Execute the complete two-response-table linear problem for each actual
SCM in the posterior catalogue. No separate macro witness proves success. -/
theorem synthesis_succeeds (i : Fin 2) : (specification i).solve.IsFeasible := by
  have bound : i.val < 2 := i.isLt
  have casesIndex : i.val = 0 ∨ i.val = 1 := by omega
  rcases casesIndex with first | second
  · have same : i = (0 : Fin 2) := Fin.ext first
    subst i
    decide +kernel
  · have same : i = (1 : Fin 2) := Fin.ext second
    subst i
    decide +kernel

/-- Extract the solver's computed mass law. The checked execution theorem
eliminates the impossible refutation branch without selecting a macro model
from an existential proposition or assuming a feasible weight vector. -/
def solution (i : Fin 2) : (specification i).Solution :=
  match outcome : (specification i).solve with
  | .feasible computed => computed
  | .invalid invalid => False.elim (invalid (protocol_valid i))
  | .infeasible _ _ => False.elim (by
      have success := synthesis_succeeds i
      rw [outcome] at success
      exact success)

/-- The synthesized observation law is the original catalogue model's Y
marginal, for every event on the retained coordinate and including zeros. -/
theorem observation_exact (i : Fin 2) (event : Event compactSignature.Assignment) :
    QProb.Equiv ((solution i).macroModel.observationalValue event)
      ((twoModels i).observationalValue (fun state => event (fun _ => state y))) :=
  (solution i).observation event

/-- Both admitted surgeries preserve complete event laws, rather than
only one chosen outcome probability. -/
theorem intervention_exact (i : Fin 2) (value : Bool)
    (event : Event compactSignature.Assignment) :
    QProb.Equiv ((solution i).macroModel.interventionalValue (macroDo value).value event)
      ((twoModels i).interventionalValue (doY value).value
        (fun state => event (fun _ => state y))) :=
  (solution i).fits (doY value) (macroDo value) (intervention_defined value) event

/-- Each required macro action has an actual admitted micro surgery.
This coverage certificate does not include the excluded original do(X). -/
theorem required_coverage (i : Fin 2) (action : HardIntervention compactSignature)
    (required : action ∈ (specification i).required) :
    ∃ intervention, omega intervention = some action :=
  (solution i).covered action required

/-- The constructed model assigns defined zero probability to Y=false
after forcing Y=true. Effectiveness proves this directly for its actual SCM. -/
theorem constructed_zero (i : Fin 2) :
    ((solution i).macroModel.interventionalValue (macroDo true).value
      (fun state => !(state (0 : Fin 1)))).num = 0 := by
  let model := (solution i).macroModel
  have zero : QProb.Equiv
      (model.interventionalValue (macroDo true).value (fun state => !(state (0 : Fin 1))))
      QProb.zero := by
    refine QProb.equiv_trans (model.interventionalValue_eq _ _) ?_
    refine QProb.equiv_trans (model.prior.probVal_congr _ (fun _ => false) ?_)
      model.prior.probVal_false
    intro unit
    rw [model.evalUnder_effectiveness (macroDo true).value unit (0 : Fin 1) true
      (HardIntervention.set_at_target _ _ _)]
    rfl
  exact (QProb.equiv_num_zero_iff zero).mpr rfl

/-- A report from the actual solver branch and its constructed model. The
display names the retained experiments and the original excluded query.
The caller supplies the same fraction formatting used for its other results. -/
def report (fraction : QProb → String) (i : Fin 2) : String :=
  match (specification i).solve with
  | .invalid _ => "Y-only abstraction: invalid intervention protocol"
  | .infeasible _ _ => "Y-only abstraction: no macro SCM fits the valid protocol"
  | .feasible computed =>
    let observed := computed.macroModel.observationalValue (fun state => state (0 : Fin 1))
    let impossible := computed.macroModel.interventionalValue (macroDo true).value
      (fun state => !(state (0 : Fin 1)))
    s!"Y-only abstraction constructed. It covers observation, do(Y=false), and do(Y=true). P(Y=true)={fraction observed} and P(Y=false | do(Y=true))={fraction impossible}. The protocol excludes the original do(X=true)."

end Thesis.Examples.InferenceWorkflowAbstraction
