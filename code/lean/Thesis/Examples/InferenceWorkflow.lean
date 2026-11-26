import Thesis.CausalTransport.CertifiedModeComputation
import Thesis.Examples.CatalogueSampling
import Thesis.Examples.InferenceWorkflowSymmetry
import Thesis.Examples.InferenceWorkflowAbstraction

namespace Thesis.Examples.InferenceWorkflow
open Probability Probability.Distros Causality Causality.BinaryBow
open Causality.CatalogueInference
open Causality.Examples.CatalogueInference (doX query reference)
open Causality.Examples.CatalogueSampling
  (twoModels twoCatalogue twoLikelihoods twoLikelihoods_sampling successExperiment
    modelPolicy chainOnlyCatalogue impossibleExperiment)
open Causality.Examples.InferenceWorkflowSymmetry (complexityScore modelFamily)
open Causality.CausalAbstractionSynthesis (Specification interventionDecidableEq)
open Thesis.Examples.CausalAbstractionSynthesis (compactSignature)
open Thesis.Examples.InferenceWorkflowAbstraction (specification macroDo omega)

/-!
# One finite causal-inference workflow, from samples to a coarse model

The catalogue contains two fully specified generative SCMs on X,Y: a fair
copy-chain and an independent fair pair. A declared complexity score gives
them prior odds 2:1. The observation is an IID cohort of six Y=true outcomes
under do(X=true), not an exact population table. Its likelihoods are 1 and
1/64, so updating retains both hypotheses with posterior odds 128:1.

Each model supplies a population causal risk and an applied graph-class
identification certificate. The posterior retains uncertainty over these
risks; class-wide identification of the functional does not imply that
finite data determine its numerical value. The executable projection is
proved equal to the certificate-backed interface in CertifiedModeComputation.

The symmetry and abstraction clients use these same two actual models.
Both models are coherent under simultaneous bit flip, with the intervention
and data transformed too. Coarse synthesis retains Y with explicit coverage
of observation and the two do(Y) settings. The original do(X) experiment
is deliberately outside that projection protocol. The constructed macro
model therefore cannot answer the original experimental query by that map.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A supplied description-length preference, not a likelihood or an
empirical property inferred from the six observed outcomes. -/
def score (i : Fin 2) : Nat :=
  complexityScore i

/-- The description score is unchanged by the coherent relabelling of
these actual model hypotheses. The same action also transforms values,
latent inputs and interventions in the companion module. -/
theorem score_respects_symmetry :
    modelFamily.hypotheses.ScoreInvariant score :=
  Causality.Examples.InferenceWorkflowSymmetry.complexityScore_invariant

/-- Apply the declared budget-one complexity preference to the reference
uniform catalogue. Both models retain positive mass. -/
def catalogue : Catalogue 2 (ExactModel signature) where
  item := twoModels
  prior := twoCatalogue.prior.reweightNat
    (fun i => complexityWeight 1 (score i)) (by decide +kernel)

/-- Unequal prior masses are compatible with this action because each
physical model is individually symmetric and its index remains fixed. -/
theorem prior_respects_symmetry :
    FiniteSymmetry.PriorInvariant
      modelFamily.hypotheses catalogue.prior :=
  Causality.Examples.InferenceWorkflowSymmetry.prior_invariant _

/-- This prior favours the deterministic copy mechanism by a factor two;
its numerical preference remains separate from the sampled likelihood. -/
theorem complexity_prior_odds :
    QProb.Equiv (catalogue.prior.pmf (0 : Fin 2)) ⟨2, 3, by decide⟩ ∧
      QProb.Equiv (catalogue.prior.pmf (1 : Fin 2)) ⟨1, 3, by decide⟩ := by
  constructor <;> decide +kernel

/-- Small exact representatives of the likelihoods of the actual IID
experiment. The imported theorem ties every representative to sampling
from the corresponding SCM, rather than to empirical frequencies. -/
def likelihood (i : Fin 2) : QProb := twoLikelihoods i

/-- The single observed object and sampling model are shared by every
hypothesis. Arithmetic simplification has not changed the data event. -/
theorem likelihood_is_actual_sampling (i : Fin 2) :
    QProb.Equiv (iidModelCountLikelihood (catalogue.item i) successExperiment)
      (likelihood i) := twoLikelihoods_sampling i

/-- A common scale clears the rational likelihood denominators without
changing posterior odds. The supported normalizer is checked explicitly. -/
def weights : Fin 2 → Nat := qprobWeights 2 likelihood

/-- Bayesian normalization retains the two-model support. There is no
fallback prior in an absent-evidence branch. -/
def posterior : Distro (Fin 2) :=
  catalogue.prior.reweightNat weights (by decide +kernel)

/-- The runner invokes the public sampling update on the actual cohort.
The compact `posterior` above uses proved equivalent likelihoods for
kernel arithmetic, avoiding repeated history traversal in its proofs. -/
def posteriorFromCounts : Option (Distro (Fin 2)) :=
  iidModelPosterior? catalogue [successExperiment]

/-- Both hypotheses remain possible after six successes. The complexity
preference changes the earlier equal-prior example's posterior odds. -/
theorem posterior_odds :
    QProb.Equiv (posterior.pmf (0 : Fin 2)) ⟨128, 129, by decide⟩ ∧
      QProb.Equiv (posterior.pmf (1 : Fin 2)) ⟨1, 129, by decide⟩ := by
  constructor <;> decide +kernel

/-- Conditional on an actual model, calculate its population intervention
risk. This operation uses its mechanisms and generative prior. -/
def risk (i : Fin 2) : QProb :=
  (catalogue.item i).interventionalValue doX.value (fun state => state y)

/-- The posterior is a law on distinct model-conditional causal answers,
not a point assertion about the population. -/
def risks : Distro QProb :=
  posteriorCausalValues catalogue.item posterior doX (fun state => state y)

/-- A posterior average is useful for prediction but does not replace the
uncertainty distribution or either model's certified functional. -/
def meanRisk : QProb :=
  posteriorMeanCausalPrediction catalogue.item posterior doX (fun state => state y)

/-- These arithmetic checks concern different quantities: two risks,
posterior mass on each risk, and their posterior-weighted mean. -/
theorem uncertainty_retained :
    QProb.Equiv (risk 0) QProb.one ∧
      QProb.Equiv (risk 1) ⟨1, 2, by decide⟩ ∧
      QProb.Equiv (risks.record.probVal
        (fun value => decide (QProb.Equiv value QProb.one))) ⟨128, 129, by decide⟩ ∧
      QProb.Equiv meanRisk ⟨257, 258, by decide⟩ := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

/-- The full certificate report keeps the common query and reference,
actual model at each index, and statistical posterior together. -/
noncomputable def certified :
    CertifiedPosteriorQuery catalogue.item query.sourceTerm reference where
  posterior := posterior
  answers i := (modelPolicy (catalogue.item i)).identifyJoint
    query reference none none

/-- Run the executable projection of those same indexed answers. The
generic projection theorem retains the connection to the full certificates. -/
def answer (i : Fin 2) : ModeIndexedAnswer signature :=
  (modelPolicy (catalogue.item i)).jointPresentation query reference

theorem answer_is_certified_projection (i : Fin 2) :
    ModeQueryPolicy.displayAnswer (certified.answers i) = answer i :=
  ModeQueryPolicy.jointPresentation_certified (modelPolicy (catalogue.item i)) query reference

/-- Check a defined certified presentation against its actual model's
population risk. This is stronger than recognizing an identified tag:
an absent numerical value cannot satisfy the test. -/
def answerMatchesRisk (i : Fin 2) : Bool :=
  match answer i with
  | .identified _ (some value) => decide (QProb.Equiv value (risk i))
  | _ => false

theorem answers_are_defined_and_correct : ∀ i : Fin 2, answerMatchesRisk i = true := by
  decide +kernel

/-- Print a reduced fraction so repeated exact denominator clearing does
not obscure an otherwise small probability. This affects display only. -/
def fraction (value : QProb) : String :=
  let divisor := Nat.gcd value.num value.den
  toString (value.num / divisor) ++ "/" ++ toString (value.den / divisor)

/-- Keep mathematical failure, lack of access and undefined conditioning
visibly separate from a certified defined zero or a numerical value. -/
def status : ModeIndexedAnswer signature → String
  | .identified _ (some value) => "identified functional; value " ++ fraction value
  | .identified _ none => "undefined formula"
  | .bounded lower upper => "certified bounds [" ++ fraction lower ++ ", " ++ fraction upper ++ "]"
  | .undefined => "undefined conditioner/formula"
  | .failed _ => "graph identification failed"
  | .unfinished => "identification unfinished"
  | .modeUnsupported => "intervention outside declared access"

/-- An actual impossible sample exhausts its one-model catalogue. The
workflow displays absence rather than treating likelihood zero as a risk. -/
def unsupportedEvidence : Bool :=
  (iidModelPosterior? chainOnlyCatalogue [impossibleExperiment]).isNone

/-- A policy may deny the causal experiment even when its model admits
the same graphical formula. Exercise this branch in the report. -/
def restrictedAnswer : ModeIndexedAnswer signature :=
  let withoutAccess : ModeQueryPolicy signature :=
    { modelPolicy (catalogue.item 0) with intervenable := NodeSet.empty }
  withoutAccess.jointPresentation query reference

theorem restricted_query_is_unsupported : restrictedAnswer.isModeUnsupported = true := by
  decide +kernel

/-- Forbid vacuous agreement by testing a proposed report that omits
observation from its required macro experiments. -/
def missingObservation : Specification signature compactSignature :=
  { specification 0 with required := [macroDo false, macroDo true] }

theorem missing_observation_rejected : missingObservation.solve.IsInvalid := by
  decide +kernel

/-- Treating the discarded X intervention as macro observation is
structurally admissible, but violates the copy model's law. The same macro
observation would need to encode both a fair and a certain Y outcome. -/
def conflictingObservation : Specification signature compactSignature :=
  { specification 0 with
    omega := fun action => if action = doX then
      some (HardIntervention.empty compactSignature) else omega action }

theorem conflicting_observation_infeasible : conflictingObservation.solve.IsInfeasible := by
  decide +kernel

/-- Report the solver's actual diagnostic branch for each attempted
projection. The detail comes from the corresponding finite fixture. -/
def projectionDiagnostic (spec : Specification signature compactSignature)
    (detail : String) : String :=
  match spec.solve with
  | .invalid _ => "Abstraction protocol rejected. " ++ detail
  | .infeasible _ _ => "No macro SCM satisfies the valid protocol. " ++ detail
  | .feasible _ => "Abstraction constructed. " ++ detail

/-- Produce the report from computed posterior masses, causal values,
certificate projections, structural transformations and solver branches.
The standalone runner prints these lines after the ordinary library build. -/
def lines : List String :=
  let inputs :=
    ["Data: six IID Y=true outcomes under do(X=true).",
     "Models: fair copy-chain, independent fair pair. Complexity prior " ++
       fraction (catalogue.prior.pmf 0) ++ ", " ++ fraction (catalogue.prior.pmf 1) ++ ".",
     "Sample likelihoods: " ++ fraction (likelihood 0) ++ ", " ++ fraction (likelihood 1) ++ "."]
  let inference := match posteriorFromCounts with
    | none => ["No posterior is supported by the catalogue."]
    | some updated =>
        let mean := posteriorMeanCausalPrediction catalogue.item updated doX (fun state => state y)
        ["Posterior model probabilities: " ++ fraction (updated.pmf 0) ++ ", " ++ fraction (updated.pmf 1) ++ ".",
         "Model-conditional population risks: " ++ fraction (risk 0) ++ ", " ++ fraction (risk 1) ++ ".",
         "Copy model: " ++ status (answer 0),
         "Independent model: " ++ status (answer 1),
         "Posterior mean risk: " ++ fraction mean ++ ". Both causal predictions retain posterior mass."]
  inputs ++ inference ++
    ["Same query with experimental access closed: " ++ status restrictedAnswer,
     "Impossible evidence is unsupported: " ++ toString unsupportedEvidence,
     Causality.Examples.InferenceWorkflowSymmetry.report,
     "Copy model coarse synthesis: " ++ Thesis.Examples.InferenceWorkflowAbstraction.report fraction 0,
     "Independent model coarse synthesis: " ++ Thesis.Examples.InferenceWorkflowAbstraction.report fraction 1,
     projectionDiagnostic missingObservation "The required experiments omitted observation.",
     projectionDiagnostic conflictingObservation "The copy model gives different laws for observation and do(X=true)."]

end Thesis.Examples.InferenceWorkflow
