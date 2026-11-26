import Thesis.CausalTransport.CatalogueInference
import Thesis.CausalTransport.CataloguePartition
import Thesis.CausalTransport.HiddenDAGNativeTemplates
import Thesis.Causality.BinaryBowEndpoints
import Thesis.Probability.Distros.PairedCountSampling

namespace Thesis
namespace Causality
namespace Examples
namespace CatalogueInference

open Probability Probability.Distros FiniteProduct
open BinaryBow
open Causality.CatalogueInference
open Causality.CataloguePartition

/-!
# Two-graph Bayesian catalogue: chain vs bow, plus an independence restriction

Shared host signature is `BinaryBow.signature` (directed `X → Y`). The three
atoms are:

* independence: mechanism restriction `X ⊥ Y`, formula `P(Y)` (not ID on a
  different directed graph — competing directed edges would need another
  signature);
* chain: bidirected-free host graph, ID of `P(Y | do(X))`;
* bow: the native bow graph, sharp bounds.

Correlated observational data zero the independence atom in Regime A.
The count model keeps a positive integrated likelihood on every atom. Its
empirical plug-in displays remain candidates and cannot certify a causal
point. A separate actual-model example supplies a class-indexed certificate.
Layer 3 is a depth-capped Boolean `W` tree on four cells that computes pooled
conditional-difference estimates; its Boolean flag is not a causal proof.
-/

/-- Construct a binary assignment in the signature's fixed node order. -/
def xy (xv yv : Bool) : signature.Assignment :=
  fun i => if i.val = 0 then xv else yv

/-- The exact observational law puts equal mass on the two diagonal assignments and zero
mass off the diagonal. -/
def correlated : FiniteProbRecord signature.Assignment where
  atoms := [(xy false false, 1), (xy true true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- The host arrow with no declared common cause. This is graph data, not a fully
parameterized SCM. -/
def chainGraph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ h; cases h
  bidirected_irreflexive := fun _ => rfl

/-- Ask for the Y singleton risk under intervention on X, with disjoint action and
outcome sets checked explicitly. -/
def query : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  action_outcome_disjoint := by
    intro i hx
    have : i = x := (NodeSet.singleton_eq_true_iff x i).mp hx
    subst this
    simp [NodeSet.singleton, x, y]

/-- The proposed observational marginal for the additional independence restriction. Its
syntax alone carries no causal certificate. -/
def independenceFormula : ProbabilityTerm signature :=
  .kernel ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.empty⟩

/-- Check every binary joint singleton against the product of its marginals, retaining
zero cells. -/
def productCompatible (law : FiniteProbRecord signature.Assignment) : Bool :=
  [false, true].all fun xv =>
    [false, true].all fun yv =>
      let joint := law.probVal (fun a => decide (a x = xv) && decide (a y = yv))
      let px := law.probVal (fun a => decide (a x = xv))
      let py := law.probVal (fun a => decide (a y = yv))
      decide (QProb.Equiv joint (QProb.mul px py))

/-- Legacy display metadata. The override and Boolean restrictions are candidates only;
they cannot construct a certified answer. -/
structure Item where
  graph : ObservedGraph signature
  override : Option (ProbabilityTerm signature)
  bow : Bool
  product : Bool

/-- Declare the product-law restriction and its proposed marginal formula. -/
def independenceItem : Item :=
  ⟨chainGraph, some independenceFormula, false, true⟩

/-- Declare the unconfounded graph without a manual formula proposal. -/
def chainItem : Item :=
  ⟨chainGraph, none, false, false⟩

/-- Declare the confounded-arrow graph and request display of its proposed endpoints. -/
def bowItem : Item :=
  ⟨graph, none, true, false⟩

/-- The fixed three-index display catalogue. Model-family declarations are supplied
rather than discovered. -/
def items : List Item := [independenceItem, chainItem, bowItem]

/-- The catalogue has exactly three positional atoms. -/
theorem items_length : items.length = 3 := rfl

/-- Assign equal prior mass to the three declared display atoms. -/
def catalogue : Catalogue items.length Item :=
  uniformOfList items (by decide)

/-- Choose the queried action value and outcome value simultaneously as true. -/
def reference : signature.Assignment := xy true true

/-- Reject the product-law restriction when the supplied exact observational law
violates it. Other metadata restrictions add no extra compatibility gate here. -/
def lawWeight (item : Item) : Nat :=
  boolWeight (if item.product then productCompatible correlated else true)

/-- Index the exact-law compatibility weights in catalogue order. -/
def lawWeights : Fin 3 → Nat :=
  fun i => lawWeight (catalogue.item i)

/-- Display bow endpoints from the existing endpoint construction. Acceptance as bounds
requires separate class-indexed evidence. -/
def lawBounds (item : Item) : Option (QProb × QProb) :=
  if item.bow then some (BinaryBow.lower correlated true, BinaryBow.upper correlated true)
  else none

/-- Evaluate only candidate syntax or proposed endpoints on the exact record. No model
application certificate is supplied by this display fixture. -/
def lawAnswer (i : Fin 3) : TemplateAnswer signature :=
  let item := catalogue.item i
  candidateAnswerOf item.graph query (.law correlated) reference (lawBounds item) item.override

/-- Normalize the supported compatibility weights without a fallback prior; retain
candidate answers in the presentation summary. -/
def lawReport : Report 3 Item signature :=
  reportOf catalogue (catalogue.prior.reweightNat lawWeights (by decide +kernel))
    lawWeights lawAnswer

/-- The exact correlated population law refutes the product restriction. -/
theorem independence_law_weight_zero : lawWeights ⟨0, by decide⟩ = 0 := by
  decide +kernel

/-- The display fixture imposes no additional exact-law restriction on the chain atom. -/
theorem chain_law_weight_one : lawWeights ⟨1, by decide⟩ = 1 := by
  decide +kernel

/-- The display fixture imposes no additional exact-law restriction on the bow atom. -/
theorem bow_law_weight_one : lawWeights ⟨2, by decide⟩ = 1 := by
  decide +kernel

set_option maxRecDepth 100000

/-- Store the expression returned by the unguarded graph program for this concrete graph
and query. -/
def chainFormula : ProbabilityTerm signature :=
  match identifyJointKernel chainGraph query with
  | .identified term => term
  | _ => .zero

/-- The program really returns the stored expression. This syntactic success is distinct
from an applied numerical certificate. -/
theorem chain_identified :
    identifyJointKernel chainGraph query = .identified chainFormula := by
  rfl

/-- Recognize graph-program failure without supplying a numerical answer for the failed query. -/
def bowFailed : Bool :=
  match identifyJointKernel graph query with
  | .failed _ => true
  | _ => false

/-- The bow graph does fail this identification request. -/
theorem bow_failed : bowFailed = true := by
  rfl

/-- At least one compatibility-surviving atom has positive prior mass. -/
theorem law_posterior_exists :
    (posterior? catalogue.prior lawWeights).isSome = true := by
  decide +kernel

/-- Normalize the supported exact-law weights directly; no absent-posterior branch
restarts the prior. -/
def lawPosterior : Distro (Fin 3) :=
  catalogue.prior.reweightNat lawWeights (by decide +kernel)

/-- Exact-law evidence removes all mass from the incompatible product restriction. -/
theorem independence_posterior_zero :
    (lawPosterior.pmf ⟨0, by decide⟩).num = 0 := by
  decide +kernel

/-- The chain display atom survives the observational compatibility update. -/
theorem chain_posterior_pos :
    0 < (lawPosterior.pmf ⟨1, by decide⟩).num := by
  decide +kernel

/-- The bow display atom also survives, so exact observational compatibility does not
select one graph. -/
theorem bow_posterior_pos :
    0 < (lawPosterior.pmf ⟨2, by decide⟩).num := by
  decide +kernel

/-- Read the candidate numerical expression while preserving its partial-result type. -/
def chainValue : ProbabilityResult.Result :=
  match lawAnswer ⟨1, by decide⟩ with
  | .candidate _ value => value
  | _ => none

/-- Read displayed candidate endpoints without promoting them to certified bounds. -/
def bowInterval : Option (QProb × QProb) :=
  match lawAnswer ⟨2, by decide⟩ with
  | .candidateBounds lo hi => some (lo, hi)
  | _ => none

/-- Recognize only the constructor carrying an applied formula certificate. -/
def isIdentified : TemplateAnswer signature → Bool
  | .identified _ => true
  | _ => false

/-- Recognize only the constructor carrying proved, supported bounds. -/
def isBounded : TemplateAnswer signature → Bool
  | .bounded _ => true
  | _ => false

/-- Recognize a graph/table calculation lacking an applied certificate. -/
def isCandidate : TemplateAnswer signature → Bool
  | .candidate _ _ => true
  | _ => false

/-- Recognize proposed endpoints that have not entered the certified interval adapter. -/
def isCandidateBounds : TemplateAnswer signature → Bool
  | .candidateBounds _ _ => true
  | _ => false

/-- Recognize a presentation retaining unresolved atom-level answers. -/
def isSpread {S : ObservedSignature} : Mixture S → Bool
  | .spread _ => true
  | _ => false

/-- Accept a display that retains disagreement or unresolved alternatives, and reject a
collapsed point summary. -/
def keepsDisagreement {S : ObservedSignature} : Mixture S → Bool
  | .disagree _ _ _ _ => true
  | .spread _ => true
  | _ => false

/-- Recognize a computed conditional-difference statistic without claiming causal identification. -/
def isEstimatedLeaf : LeafAnswer → Bool
  | .estimated _ => true
  | _ => false

/-- The graph program still identifies its functional (`chain_identified`),
but a graph/table display does not certify its application to a model. -/
theorem chain_candidate_answer : isCandidate (lawAnswer ⟨1, by decide⟩) = true := by
  decide +kernel

/-- Raw endpoint input remains a candidate even when the underlying graph program fails. -/
theorem bow_candidate_bounds : isCandidateBounds (lawAnswer ⟨2, by decide⟩) = true := by
  decide +kernel

/-- A mixture of uncertified graph/table displays does not become a certified point. -/
theorem law_mixture_spread : isSpread lawReport.mixture = true := by
  decide +kernel

/-- Existing bow endpoint models are the bound witnesses. -/
def bowLowerModel := BinaryBow.model correlated false
/-- The existing upper endpoint SCM complements the lower endpoint witness. -/
def bowUpperModel := BinaryBow.model correlated true

/-- Use a prior-odds sensitivity factor of two in this concrete diagnostic. -/
def C : Nat := 2

/-- Compute the sensitivity interval from the equal observational likelihoods and the
declared prior-odds bound. -/
def lawOddsChainBow : Option (QProb × QProb) :=
  posteriorOddsInterval C (by decide)
    ⟨lawWeights ⟨1, by decide⟩, 1, Nat.succ_pos 0⟩
    ⟨lawWeights ⟨2, by decide⟩, 1, Nat.succ_pos 0⟩

/-- The denominator hypothesis has positive likelihood, so its likelihood ratio is defined. -/
theorem law_odds_defined : lawOddsChainBow.isSome = true := by
  decide +kernel

/-! ## Generative atoms and `do(X)` experiments

Observational \(P(V)\) already zeros independence and leaves chain vs bow
tied (same factual law). Graphs are not generative, so interventional
scoring uses realized SCMs: a copy-chain, an independent pair, and the
bow *lower* endpoint (one SCM that realizes the same \(P(V)\)). A
`do(X{=}true)` table equal to the chain's interventional law then excludes
independence and that bow model. The bow *class* is not confirmed by
landing inside `[lo, hi]`.
-/

def fairBit : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- One fair latent bit feeds X only; Y receives X through the directed mechanism. -/
def chainLatent : LatentExtension signature where
  count := 1
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun _ child => decide (child.val = 0)

/-- The actual unconfounded copy-chain has equations X = its fair source and Y = X. Hard
interventions override exactly their targeted equations. -/
def chainModel : ExactModel signature where
  latent := chainLatent
  factor := fun _ => fairBit
  prior := record 1 (fun _ => Bool) (fun _ => fairBit)
  product_law := record_rectangular_probVal 1 (fun _ => Bool) (fun _ => fairBit)
  mechanism := fun child parents inputs =>
    if hx : child = x then
      inputs ⟨0, by decide⟩ (by simp [chainLatent, hx, x])
    else
      parents x (by
        rcases node_cases child with same | same
        · exact (hx same).elim
        · simp [signature, x, y, same])

/-- Two private source coordinates, one incident to each observed node. -/
def indepLatent : LatentExtension signature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun l child => decide (l.val = child.val)

/-- The actual independent fair pair ignores the allowed directed edge. Its product
source law is proved explicitly. -/
def independenceModel : ExactModel signature where
  latent := indepLatent
  factor := fun _ => fairBit
  prior := record 2 (fun _ => Bool) (fun _ => fairBit)
  product_law := record_rectangular_probVal 2 (fun _ => Bool) (fun _ => fairBit)
  mechanism := fun child _parents inputs =>
    inputs ⟨child.val, child.isLt⟩ (by simp [indepLatent])

/-- Choose the actual lower-endpoint bow SCM, rather than treating its graph as a predictive law. -/
def bowLowerModelGen : ExactModel signature :=
  BinaryBow.model correlated false

/-- Set X to true while leaving Y's mechanism unchanged. -/
def doX : HardIntervention signature :=
  (HardIntervention.empty signature).set x true

/-- Chain interventional law under `do(X = true)`: point mass on `(true, true)`. -/
def chainDoLaw : FiniteProbRecord signature.Assignment :=
  chainModel.interventionalDist doX.value

/-- Supply exact observational and interventional laws from the copy-chain. These are
population-law data, not sampled counts. -/
def experiments : List (Experiment signature) :=
  [observationalExperiment (.law correlated),
    interveneExperiment doX (.law chainDoLaw)]

/-- Complexity is prior mass only: independence 0, chain 1, bow 2. -/
def itemComplexity : Fin 3 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2

/-- With budget two, the chain's declared prior weight is twice the bow's. This
comparison is independent of data likelihoods. -/
theorem complexity_prefers_chain :
    complexityWeight 2 (itemComplexity ⟨1, by decide⟩) =
      2 * complexityWeight 2 (itemComplexity ⟨2, by decide⟩) := by
  decide

/-- Score each actual generative SCM against the same tagged exact-law experiments. -/
def expWeights : Fin 3 → Nat
  | ⟨0, _⟩ => regimeAModelWeight independenceModel experiments
  | ⟨1, _⟩ => regimeAModelWeight chainModel experiments
  | ⟨2, _⟩ => regimeAModelWeight bowLowerModelGen experiments

/-- Normalize the supported generative compatibility update and retain the separate
legacy display answers. -/
def experimentReport : Report 3 Item signature :=
  reportOf catalogue (catalogue.prior.reweightNat expWeights (by decide +kernel))
    expWeights lawAnswer

/-- The independent fair SCM fails the combined exact-law requirements. -/
theorem experiment_independence_weight_zero : expWeights ⟨0, by decide⟩ = 0 := by
  decide +kernel

/-- The copy-chain realizes both of its supplied exact laws. -/
theorem experiment_chain_weight_one : expWeights ⟨1, by decide⟩ = 1 := by
  decide +kernel

/-- The selected bow endpoint fails the copy-chain intervention law, despite matching
observation. -/
theorem experiment_bow_weight_zero : expWeights ⟨2, by decide⟩ = 0 := by
  decide +kernel

/-- The chain supplies positive supported evidence for normalization. -/
theorem experiment_posterior_exists :
    (posterior? catalogue.prior expWeights).isSome = true := by
  decide +kernel

/-- The exact-law experimental catalogue retains a compatible atom. -/
theorem experiment_not_exhausted :
    catalogueExhausted catalogue.prior expWeights = false := by
  decide +kernel

/-- Construct the supported exact-law posterior directly, without a fallback distribution. -/
def experimentPosterior : Distro (Fin 3) :=
  catalogue.prior.reweightNat expWeights (by decide +kernel)

/-- The incompatible independent SCM receives zero posterior mass. -/
theorem experiment_independence_posterior_zero :
    (experimentPosterior.pmf ⟨0, by decide⟩).num = 0 := by
  decide +kernel

/-- The realizing copy-chain retains positive posterior mass. -/
theorem experiment_chain_posterior_pos :
    0 < (experimentPosterior.pmf ⟨1, by decide⟩).num := by
  decide +kernel

/-- The incompatible selected bow endpoint receives zero posterior mass. -/
theorem experiment_bow_posterior_zero :
    (experimentPosterior.pmf ⟨2, by decide⟩).num = 0 := by
  decide +kernel

/-- Align the three actual SCMs with the display catalogue's fixed index order. -/
def generators : Fin 3 → ExactModel signature
  | ⟨0, _⟩ => independenceModel
  | ⟨1, _⟩ => chainModel
  | ⟨2, _⟩ => bowLowerModelGen

/-- The finite executable check singles out the chain within this supplied list. -/
theorem experiment_uniquely_realizes_bool :
    uniquelyRealizesBool generators experiments ⟨1, by decide⟩ = true := by
  decide +kernel

/-- Turn the checked finite test into a unique-realizer proposition. -/
theorem experiment_uniquely_realizes_chain :
    uniquelyRealizes generators experiments ⟨1, by decide⟩ :=
  uniquelyRealizes_of_bool generators experiments ⟨1, by decide⟩
    experiment_uniquely_realizes_bool

/-- The selected realizer had positive prior mass before seeing the laws. -/
theorem experiment_prior_chain_pos :
    0 < (catalogue.prior.pmf ⟨1, by decide⟩).num := by
  decide +kernel

/-- Apply the general posterior theorem: only the listed chain index survives. The
conclusion makes no claim of global DAG uniqueness. -/
theorem experiment_list_separated :
    catalogueExhausted catalogue.prior
        (fun j => regimeAModelWeight (generators j) experiments) = false ∧
      ∃ μ, posterior? catalogue.prior
          (fun j => regimeAModelWeight (generators j) experiments) = some μ ∧
        0 < (μ.pmf ⟨1, by decide⟩).num ∧
        ∀ j : Fin 3, j ≠ ⟨1, by decide⟩ → (μ.pmf j).num = 0 :=
  posterior_of_unique_realizer catalogue.prior generators experiments
    ⟨1, by decide⟩ experiment_uniquely_realizes_chain experiment_prior_chain_pos

/-- Flip the `Y` label. The chain's observational law is supported on
`X = Y`, so this supplied permutation is not an invariance of the
hypothesis; the filter is not inferred from data. -/
def flipYAssign (a : signature.Assignment) : signature.Assignment :=
  fun i => if i.val = 1 then !a i else a i

/-- The chain matches the declared experiments before an additional invariance
restriction is imposed. -/
theorem chain_matches_without_invariance :
    regimeAModelWeight chainModel experiments = 1 :=
  experiment_chain_weight_one

/-- Flipping only Y changes the copy-chain's observational law. -/
theorem chain_not_flipY_invariant :
    assignmentLawInvariant (predictedTable chainModel .observational) flipYAssign =
      false := by
  decide +kernel

/-- A caller-imposed invariance gate may reject a model that otherwise exactly matches
the data; the gate is extra prior knowledge. -/
theorem invariance_zeros_matching_chain :
    regimeAInvariantModelWeight chainModel flipYAssign experiments = 0 := by
  decide +kernel

/-- Embed the unconfounded two-node host in the native finite hidden-DAG representation
with no hidden nodes. -/
def tinyHidden : FiniteHiddenDAG signature where
  count := 2
  observedNode := id
  observedNode_injective := fun _ _ same => same
  hidden := fun _ => false
  observed_not_hidden := fun _ => rfl
  node_classified := fun node => Or.inr ⟨node, rfl⟩
  edge := signature.directed
  rank := Fin.val
  edge_rank_lt := fun selected => signature.directed_earlier selected

/-- Exchange the two node indices. This raw function is used only by the graph-table checks here. -/
def swapNodes (i : Fin signature.count) : Fin signature.count :=
  if i.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

/-- Identity preserves every bounded native template of the fixed graph. -/
theorem native_filter_id :
    filterInvariantTemplates chainGraph (fun i => i)
      (tinyHidden.nativeTemplateCatalogue 1 1) =
      tinyHidden.nativeTemplateCatalogue 1 1 :=
  filterInvariantTemplates_id _ _

/-- Exchanging source and child fails directed-edge invariance and drops the fixed-graph
template list. -/
theorem native_filter_swap_empty :
    filterInvariantTemplates chainGraph swapNodes
      (tinyHidden.nativeTemplateCatalogue 1 1) = [] := by
  refine filterInvariantTemplates_not _ _ _ ?_
  decide +kernel

/-- A `do(X{=}true)` table the chain cannot realize. All listed atoms then
fail, so the catalogue is exhausted rather than replaced by a fallback. -/
def impossibleDoLaw : FiniteProbRecord signature.Assignment where
  atoms := [(xy true false, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

/-- Combine the diagonal population law with an intervention law incompatible with all
three supplied generators. -/
def exhaustedExperiments : List (Experiment signature) :=
  [observationalExperiment (.law correlated),
    interveneExperiment doX (.law impossibleDoLaw)]

/-- Evaluate the same incompatible experiment family at each generative hypothesis. -/
def exhaustedWeights : Fin 3 → Nat
  | ⟨0, _⟩ => regimeAModelWeight independenceModel exhaustedExperiments
  | ⟨1, _⟩ => regimeAModelWeight chainModel exhaustedExperiments
  | ⟨2, _⟩ => regimeAModelWeight bowLowerModelGen exhaustedExperiments

/-- No positive-prior atom survives the contradictory exact-law requirements. -/
theorem exhausted_catalogue :
    catalogueExhausted catalogue.prior exhaustedWeights = true := by
  decide +kernel

/-- An exhausted catalogue returns no report; it does not substitute a prior or a fallback graph. -/
theorem exhausted_infer_none :
    (infer catalogue exhaustedWeights lawAnswer).isNone = true := by
  decide +kernel

/-- Regime B on the chain's `do` table, using each SCM's predicted masses.
This is callable; it does not by itself zero the bow the way Regime A does. -/
def chainDoBins : List Nat :=
  signature.assignmentEnumeration.map fun a =>
    if decide (a x = true) && decide (a y = true) then 6 else 0

/-- The legacy extra table-prior construction supports this intervention sample. This
differs from the fixed-SCM IID likelihood checked in CatalogueSampling. -/
theorem chain_do_regimeB_pos :
    0 < (regimeBModelMass chainModel (.intervene doX) chainDoBins).num := by
  decide +kernel

/-! ## Regime B: Dirichlet–multinomial on the observed table -/

def labels : List signature.Assignment := signature.assignmentEnumeration

/-- Give each diagonal joint cell count three and each off-diagonal cell count zero. -/
def countOf (a : signature.Assignment) : Nat :=
  if decide (a x = a y) then 3 else 0

/-- Store the common complete joint histogram in the signature's assignment order. -/
def bins : List Nat := labels.map countOf

/-- Declare Dirichlet(1,1,1,1) on the saturated joint alphabet. -/
def uniformAlphas : List QProb := [QProb.one, QProb.one, QProb.one, QProb.one]

/-- The saturated prior has positive total parameter mass. -/
theorem uniformAlphas_pos : 0 < (QProb.listSum uniformAlphas).num := by
  decide

/-- Score the complete joint histogram under the saturated Dirichlet-multinomial law. -/
def saturatedMass : QProb :=
  dirichletMultinomialMass bins.sum uniformAlphas uniformAlphas_pos bins

/-- Sum the common joint counts over assignments with the selected node false. -/
def marginFalse (node : Fin signature.count) : Nat :=
  (labels.zip bins).foldl (fun acc p =>
    acc + if decide (p.1 node = false) then p.2 else 0) 0

/-- Sum the same joint counts over assignments with the selected node true. -/
def marginTrue (node : Fin signature.count) : Nat :=
  (labels.zip bins).foldl (fun acc p =>
    acc + if decide (p.1 node = true) then p.2 else 0) 0

/-- Declare the uniform Beta(1,1) prior for one binary parameter. -/
def twoAlphas : List QProb := [QProb.one, QProb.one]

/-- Each binary prior has positive total parameter mass. -/
theorem twoAlphas_pos : 0 < (QProb.listSum twoAlphas).num := by
  decide

/-- The former score is retained only as a regression witness. It is the
probability of two marginal histograms, an event that forgets their pairing.
It must not be compared against a saturated *joint*-histogram likelihood. -/
def marginalHistogramsMass : QProb :=
  QProb.mul
    (dirichletMultinomialMass (marginFalse x + marginTrue x) twoAlphas twoAlphas_pos
      [marginFalse x, marginTrue x])
    (dirichletMultinomialMass (marginFalse y + marginTrue y) twoAlphas twoAlphas_pos
      [marginFalse y, marginTrue y])

/-- Independent uniform Beta parameters generate two independent Pólya
histories, which are paired by trial before counting. This scores exactly
the same joint table as `saturatedMass`, including which X and Y observations
occurred together. The generic construction is a normalized sampling law;
no numerical correction constant is inserted in this example. -/
def independenceMass : QProb :=
  pairedDirichletCountMass twoAlphas twoAlphas twoAlphas_pos twoAlphas_pos bins

set_option maxHeartbeats 2000000 in
/-- Three `00` and three `11` records constrain the pairing as well as both
margins. The missing pairing event has probability `1/20`; omitting it
would multiply this hypothesis's Bayes factor by twenty. -/
theorem independence_joint_likelihood :
    QProb.Equiv independenceMass ⟨1, 980, by decide⟩ := by decide +kernel

/-- The historical product scores the two margins and equals 1/49, demonstrating the
different observed event. -/
theorem marginal_histogram_score :
    QProb.Equiv marginalHistogramsMass ⟨1, 49, by decide⟩ := by decide +kernel

/-- The saturated model scores the complete six-record joint histogram with probability 1/84. -/
theorem saturated_joint_likelihood :
    QProb.Equiv saturatedMass ⟨1, 84, by decide⟩ := by decide +kernel

/-- Assign each hypothesis a law for the same joint count observation. The independence
restriction uses paired Beta priors; the other two indices share a saturated table
prior. -/
def countLikelihood : Fin 3 → QProb
  | ⟨0, _⟩ => independenceMass
  | ⟨1, _⟩ => saturatedMass
  | ⟨2, _⟩ => saturatedMass

/-- Clear denominators with one shared positive scale before reweighting the catalogue. -/
def countWeights : Fin 3 → Nat :=
  qprobWeights 3 countLikelihood

/-- Construct empirical frequencies only for display. This table is not a
posterior-predictive law or a population-law observation. -/
def countLaw : FiniteProbRecord signature.Assignment :=
  recordOfCounts labels bins
    (by simp [bins, labels, List.length_map])
    (by decide +kernel)

/-- Display plug-in candidate formulas and endpoints on empirical frequencies, without
manufacturing numerical causal certificates. -/
def countAnswer (i : Fin 3) : TemplateAnswer signature :=
  let item := catalogue.item i
  candidateAnswerOf item.graph query (.law countLaw) reference (lawBounds item) item.override

/-- Normalize the supported common-histogram likelihoods directly while leaving
empirical plug-in answers visibly uncertified. -/
def countReport : Report 3 Item signature :=
  reportOf catalogue (catalogue.prior.reweightNat countWeights (by decide +kernel))
    countWeights countAnswer

/-- The common finite sample has positive prior-predictive mass. -/
theorem count_posterior_exists :
    (posterior? catalogue.prior countWeights).isSome = true := by
  decide +kernel

/-- Finite diagonal data retain a nonzero likelihood for the independent-parameter hypothesis. -/
theorem count_independence_pos :
    0 < (countReport.mass ⟨0, by decide⟩).num := by
  decide +kernel

/-- The numerical display does not collapse uncertified plug-in alternatives into an
accepted causal point. -/
theorem count_mixture_keeps_disagreement :
    keepsDisagreement countReport.mixture = true := by
  decide +kernel

/-! ## Layer 3: depth-capped Boolean `W`, empirical leaf estimate -/

def pooled : TyTable :=
  addCount (addCount emptyTable true true 3) false false 3

/-- Compute the pooled empirical conditional-difference statistic; the Boolean flag
requests computation only. -/
def leafEstimated : LeafAnswer :=
  leafAnswer true pooled none

/-- Both treatment rows have empirical support, so the conditional-difference estimate exists. -/
theorem leaf_tau_defined : isEstimatedLeaf leafEstimated = true := by
  decide +kernel

/-- Enumerate recipes with at most one split along each branch. -/
def cap1Trees : List SplitTree := treesUpTo 1

/-- The unsplit recipe witnesses nonemptiness of this concrete tree catalogue. -/
theorem cap1_nonempty : 0 < cap1Trees.length :=
  treesUpTo_length_pos 1

/-- Supply a repeated pooled table for this score-only example. It is not a common
modifier-labelled dataset model. -/
def stumpTables (_idx : Nat) : TyTable := pooled

/-- Compute the callback-based product of pooled leaf probabilities. Different pooling
summaries make this a score rather than a Bayesian tree likelihood. -/
def stumpScore (tree : SplitTree) : QProb :=
  pooledCountScore tree stumpTables uniformAlphas uniformAlphas_pos

/-- Clear score denominators before normalizing the recipe weights. -/
def stumpWeights : Fin (treesUpTo 1).length → Nat :=
  qprobWeights (treesUpTo 1).length (fun i =>
    stumpScore ((treesUpTo 1).get i))

/-- At least one recipe has positive prior weight and score, so score normalization is supported. -/
theorem stump_score_distribution_exists :
    (posterior? (treePrior 1) stumpWeights).isSome = true := by
  decide +kernel

/-- Normalize supported recipe scores directly, without claiming that the scores are a
common-data likelihood. -/
def stumpScoreDistribution : Distro (Fin (treesUpTo 1).length) :=
  (treePrior 1).reweightNat stumpWeights (by decide +kernel)

/-- Mix the supplied empirical leaf estimates under the score distribution, retaining
undefinedness when a positive-mass estimate is missing. -/
def stumpTau (cell : Cell) : Option SignedRatio :=
  mixTau 1 stumpScoreDistribution (fun _ _ => leafEstimated) cell

/-- The concrete cell-zero mixture has defined empirical treatment rows throughout this fixture. -/
theorem stump_tau_cell0 :
    (stumpTau ⟨0, by decide⟩).isSome = true := by
  decide +kernel

/-- The first modifier bit gives a two-stage observation refinement of the uniform four-cell law. -/
def refinement : ObservationChain (discreteUniformDistro 4 (by decide)) 1 :=
  firstBitChain _

/-- Flip both observed bits. The copy-chain observational law is supported
on `X = Y`, so this supplied map preserves `P(V)` and fails on `do(X{=}true)`. -/
def flipXYAssign (a : signature.Assignment) : signature.Assignment :=
  fun i => !a i

/-- A simultaneous bit flip preserves the diagonal observational law. -/
theorem chain_obs_flipXY_invariant :
    assignmentLawInvariant (predictedTable chainModel .observational) flipXYAssign =
      true := by
  decide +kernel

/-- Keeping do(X=true) fixed while flipping outcomes changes its predicted law.
Transforming the intervention is required for coherent equivariance. -/
theorem chain_do_flipXY_not_invariant :
    assignmentLawInvariant (predictedTable chainModel (.intervene doX)) flipXYAssign =
      false := by
  decide +kernel

/-- An observational-only invariance gate retains the chain after matching the exact-law
experiments. -/
theorem observational_invariance_keeps_chain :
    regimeAInvariantModelWeight chainModel flipXYAssign experiments = 1 := by
  decide +kernel

/-- Requiring invariance of every fixed experiment rejects the chain's asymmetric do(X=true) law. -/
theorem per_experiment_invariance_zeros_do :
    regimeAInvariantExperimentWeight chainModel flipXYAssign experiments = 0 := by
  decide +kernel

/-- A three-node acyclic host has two interchangeable parent nodes pointing to one outcome. -/
def twoCauseSig : ObservedSignature where
  count := 3
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val < 2 ∧ child.val = 2)
  directed_earlier := by decide +kernel

/-- Exchange the two parent indices while fixing the outcome. -/
def swapCauses : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨n + 2, h⟩ => ⟨n + 2, h⟩

/-- An explicit symmetric bidirected edge table between two supplied nodes. -/
def pairEdge (a b i j : Fin 3) : Bool :=
  decide ((i = a ∧ j = b) ∨ (i = b ∧ j = a))

/-- The pair-edge relation is symmetric by finite disjunction analysis. -/
theorem pairEdge_symm (a b i j : Fin 3)
    (h : pairEdge a b i j = true) : pairEdge a b j i = true := by
  simp only [pairEdge, decide_eq_true_eq] at h ⊢
  rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact Or.inr ⟨hj, hi⟩
  · exact Or.inl ⟨hj, hi⟩

/-- Distinct supplied endpoints make the symmetric edge table irreflexive. -/
theorem pairEdge_irrefl (a b i : Fin 3) (hne : a ≠ b) :
    pairEdge a b i i = false := by
  refine decide_eq_false ?_
  intro h
  rcases h with ⟨sameA, sameB⟩ | ⟨sameB, sameA⟩
  · exact hne (sameA.symm.trans sameB)
  · exact hne (sameA.symm.trans sameB)

/-- Construct one observed graph with the supplied confounded pair and the common directed host. -/
def graphPair (a b : Fin 3) (hne : a ≠ b) : ObservedGraph twoCauseSig where
  bidirected := pairEdge a b
  bidirected_symmetric := fun {_ _} h => pairEdge_symm a b _ _ h
  bidirected_irreflexive := fun i => pairEdge_irrefl a b i hne

/-- The same three-node host with no bidirected edges. -/
def graphNone : ObservedGraph twoCauseSig where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ h; cases h
  bidirected_irreflexive := fun _ => rfl

/-- Name the first parent index. -/
def n0 : Fin 3 := ⟨0, by decide⟩
/-- Name the second parent index. -/
def n1 : Fin 3 := ⟨1, by decide⟩
/-- Name the shared outcome index. -/
def n2 : Fin 3 := ⟨2, by decide⟩

/-- Confound the first parent with the outcome. -/
def graphX1Y : ObservedGraph twoCauseSig := graphPair n0 n2 (by decide)
/-- Confound the second parent with the outcome. -/
def graphX2Y : ObservedGraph twoCauseSig := graphPair n1 n2 (by decide)

/-- Keep the two asymmetric confounding graphs and the symmetric unconfounded graph as
distinct catalogue atoms. -/
def graphAtoms : List (ObservedGraph twoCauseSig × Nat) :=
  [(graphX1Y, 0), (graphX2Y, 1), (graphNone, 2)]

/-- Identity preserves every graph-tagged atom. -/
theorem multi_graph_filter_id :
    filterInvariantGraphItems (fun i : Fin 3 => i) graphAtoms = graphAtoms :=
  filterInvariantGraphItems_id graphAtoms

/-- The first asymmetric confounding graph is not fixed by exchanging the two parents. -/
theorem swap_drops_x1y :
    observedGraphInvariant graphX1Y swapCauses = false := by decide +kernel
/-- The second asymmetric confounding graph is also not individually fixed by the exchange. -/
theorem swap_drops_x2y :
    observedGraphInvariant graphX2Y swapCauses = false := by decide +kernel
/-- The unconfounded host is individually fixed by exchanging its two parents. -/
theorem swap_keeps_none :
    observedGraphInvariant graphNone swapCauses = true := by decide +kernel

/-- A fixed-graph invariance filter keeps only the individually invariant atom. This
differs from closure under a group action that exchanges the other two graphs. -/
theorem multi_graph_filter_swap :
    filterInvariantGraphItems swapCauses graphAtoms = [(graphNone, 2)] := by
  rw [graphAtoms]
  rw [filterInvariantGraphItems_dropped swapCauses graphX1Y 0
    [(graphX2Y, 1), (graphNone, 2)] swap_drops_x1y]
  rw [filterInvariantGraphItems_dropped swapCauses graphX2Y 1
    [(graphNone, 2)] swap_drops_x2y]
  rw [filterInvariantGraphItems_kept swapCauses graphNone 2 [] swap_keeps_none]
  rfl

/-- The supplied experiment family contains observation and do(X=true). -/
def tinyTags : List (ExperimentTag signature) :=
  [.observational, .intervene doX]

/-- Every finite optional coordinate setting occurs in its declared enumeration,
including the unset case. -/
private theorem optionValues_complete (i : Fin signature.count)
    (v : Option (signature.Value i)) :
    v ∈ optionValues signature i := by
  cases v with
  | none => simp [optionValues]
  | some b =>
      simp [optionValues]
      exact signature.value_complete i b

/-- Observation is included independently of the intervention-target cap. -/
theorem observational_mem_candidateTags :
    ExperimentTag.observational ∈ candidateTags signature 1 :=
  List.mem_cons_self

/-- The specified hard intervention sets X to true. -/
theorem doX_value_x : doX.value x = some true :=
  HardIntervention.set_at_target _ _ _

/-- The same intervention leaves Y unset, preserving its mechanism. -/
theorem doX_value_y : doX.value y = none := by
  unfold doX
  have hne : y ≠ x := by
    intro h
    cases congrArg Fin.val h
  rw [HardIntervention.set_away_from_target _ x y true hne]
  rfl

/-- The X assignment makes this a proper intervention rather than observation. -/
theorem doX_not_empty : interventionIsEmpty doX = false := by
  unfold interventionIsEmpty
  cases h : finAll signature.count (fun i => (doX.value i).isNone) with
  | false => rfl
  | true =>
      have hx := (finAll_eq_true_iff _).mp h x
      simp [doX_value_x] at hx

/-- Exactly one coordinate is targeted. -/
theorem doX_target_count : interventionTargetCount doX = 1 := by
  have hfin : List.finRange signature.count = [x, y] := rfl
  have hx : (doX.value x).isSome = true := by rw [doX_value_x]; rfl
  have hy : (doX.value y).isSome = false := by rw [doX_value_y]; rfl
  simp [interventionTargetCount, hfin, List.filter, hx, hy]

/-- The finite intervention enumeration contains this concrete hard intervention. -/
theorem doX_mem_hardInterventionEnumeration :
    doX ∈ hardInterventionEnumeration signature := by
  have hmk : ({ value := doX.value } : HardIntervention signature) = doX := by
    cases doX
    rfl
  rw [← hmk]
  refine List.mem_map.mpr ⟨doX.value, ?_, rfl⟩
  exact FiniteProduct.enumeration_complete
    signature.count
    (fun i => Option (signature.Value i))
    (fun i => optionValues signature i)
    (fun i v => optionValues_complete i v)
    doX.value

/-- The one-target experiment survives the declared target-count cap. -/
theorem doX_mem_candidateTags :
    ExperimentTag.intervene doX ∈ candidateTags signature 1 := by
  refine List.mem_cons_of_mem _ ?_
  refine List.mem_map.mpr ⟨doX, ?_, rfl⟩
  refine List.mem_filter.mpr ⟨doX_mem_hardInterventionEnumeration, ?_⟩
  change (!interventionIsEmpty doX &&
      decide (interventionTargetCount doX ≤ 1)) = true
  rw [doX_not_empty, doX_target_count]
  rfl

/-- The independent SCM's exact interventional table, used as a common comparison record. -/
def indepDoLaw : FiniteProbRecord signature.Assignment where
  atoms := [(xy true false, 1), (xy true true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- Recover a failed Boolean gate from its zero natural weight. -/
theorem boolWeight_eq_zero {b : Bool} (h : boolWeight b = 0) : b = false := by
  cases b with
  | false => rfl
  | true => cases h

/-- Recover a successful Boolean gate from its unit natural weight. -/
theorem boolWeight_eq_one {b : Bool} (h : boolWeight b = 1) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-- Read a failed exact-law agreement from a zero compatibility weight. -/
theorem recordsAgree_of_weight_zero
    (predicted observed : FiniteProbRecord signature.Assignment)
    (h : regimeAWeight predicted (.law observed) = 0) :
    recordsAgree predicted observed = false := by
  simp only [regimeAWeight, dataAsRecord] at h
  exact boolWeight_eq_zero h

/-- Read successful exact-law agreement from a unit compatibility weight. -/
theorem recordsAgree_of_weight_one
    (predicted observed : FiniteProbRecord signature.Assignment)
    (h : regimeAWeight predicted (.law observed) = 1) :
    recordsAgree predicted observed = true := by
  simp only [regimeAWeight, dataAsRecord] at h
  exact boolWeight_eq_one h

/-- The chain agrees with its own do(X=true) prediction. -/
theorem chain_do_agrees_self :
    recordsAgree (predictedTable chainModel (.intervene doX)) chainDoLaw = true :=
  recordsAgree_self _

/-- The independent model fails the chain's do(X=true) population law. -/
theorem indep_do_weight_zero :
    regimeAWeight (predictedTable independenceModel (.intervene doX))
      (.law chainDoLaw) = 0 := by decide +kernel

/-- The selected bow endpoint also fails the chain's intervention law. -/
theorem bow_do_weight_zero :
    regimeAWeight (predictedTable bowLowerModelGen (.intervene doX))
      (.law chainDoLaw) = 0 := by decide +kernel

/-- The independent model agrees with its own intervention table. -/
theorem indep_do_weight_one :
    regimeAWeight (predictedTable independenceModel (.intervene doX))
      (.law indepDoLaw) = 1 := by decide +kernel

/-- Check each singleton of the selected bow endpoint under the intervention, retaining
zero cells. -/
theorem bow_do_cell (xv yv : Bool) :
    QProb.Equiv
      ((predictedTable bowLowerModelGen (.intervene doX)).probVal
        (FiniteProbRecord.singletonEvent (xy xv yv)))
      (indepDoLaw.probVal (FiniteProbRecord.singletonEvent (xy xv yv))) := by
  cases xv <;> cases yv <;> decide +kernel

/-- Every binary assignment equals its two-coordinate reconstruction; this avoids
assuming function extensionality beyond the allowed proof machinery. -/
private theorem assignment_eq_xy (assignment : signature.Assignment)
    {xv yv : Bool} (hx : assignment x = xv) (hy : assignment y = yv) :
    assignment = xy xv yv := by
  funext i
  rcases node_cases i with hi | hi
  · rw [hi]; simp [xy, x]; exact hx
  · rw [hi]; simp [xy, y]; exact hy

/-- The selected bow endpoint and the independent SCM predict the same complete intervention law. -/
theorem bow_do_agrees_indep_table :
    recordsAgree (predictedTable bowLowerModelGen (.intervene doX)) indepDoLaw =
      true := by
  refine List.all_eq_true.mpr ?_
  intro assignment _
  have hx : assignment x = false ∨ assignment x = true := by cases assignment x <;> simp
  have hy : assignment y = false ∨ assignment y = true := by cases assignment y <;> simp
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have := assignment_eq_xy assignment hx hy
    subst this
    exact decide_eq_true (bow_do_cell false false)
  · have := assignment_eq_xy assignment hx hy
    subst this
    exact decide_eq_true (bow_do_cell false true)
  · have := assignment_eq_xy assignment hx hy
    subst this
    exact decide_eq_true (bow_do_cell true false)
  · have := assignment_eq_xy assignment hx hy
    subst this
    exact decide_eq_true (bow_do_cell true true)

/-- The independent interventional law disagrees with the chain's intervention law. -/
theorem indep_do_misses_chain :
    recordsAgree (predictedTable independenceModel (.intervene doX)) chainDoLaw =
      false :=
  recordsAgree_of_weight_zero _ _ indep_do_weight_zero

/-- The bow endpoint's interventional law also disagrees with the chain's intervention law. -/
theorem bow_do_misses_chain :
    recordsAgree (predictedTable bowLowerModelGen (.intervene doX)) chainDoLaw =
      false :=
  recordsAgree_of_weight_zero _ _ bow_do_weight_zero

/-- Whole-law agreement recognizes the independent SCM's own intervention prediction. -/
theorem indep_do_agrees_self :
    recordsAgree (predictedTable independenceModel (.intervene doX)) indepDoLaw =
      true :=
  recordsAgree_of_weight_one _ _ indep_do_weight_one

/-- One experiment alone cannot distinguish the independent SCM from the selected bow endpoint. -/
theorem indep_bow_agree_doX :
    recordsAgree (predictedTable independenceModel (.intervene doX))
      (predictedTable bowLowerModelGen (.intervene doX)) = true :=
  recordsAgree_trans
    (predictedTable independenceModel (.intervene doX))
    indepDoLaw
    (predictedTable bowLowerModelGen (.intervene doX))
    indep_do_agrees_self
    (by
      rw [recordsAgree_comm]
      exact bow_do_agrees_indep_table)

/-- The independent fair model fails the exact correlated observational law. -/
theorem indep_obs_weight_zero :
    regimeAWeight (predictedTable independenceModel .observational)
      (.law correlated) = 0 := by decide +kernel

/-- Read the corresponding observational-law disagreement. -/
theorem indep_obs_misses_correlated :
    recordsAgree (predictedTable independenceModel .observational) correlated =
      false :=
  recordsAgree_of_weight_zero _ _ indep_obs_weight_zero

/-- The copy-chain realizes the exact diagonal observational law. -/
theorem chain_obs_weight_one :
    regimeAWeight (predictedTable chainModel .observational) (.law correlated) = 1 := by
  decide +kernel

/-- The chosen bow endpoint realizes the same diagonal observational law. -/
theorem bow_obs_weight_one :
    regimeAWeight (predictedTable bowLowerModelGen .observational) (.law correlated) =
      1 := by decide +kernel

/-- Observation alone cannot distinguish the chain and selected bow endpoint. -/
theorem observational_chain_bow_agree :
    recordsAgree (predictedTable chainModel .observational)
      (predictedTable bowLowerModelGen .observational) = true :=
  recordsAgree_trans
    (predictedTable chainModel .observational)
    correlated
    (predictedTable bowLowerModelGen .observational)
    (recordsAgree_of_weight_one
      (predictedTable chainModel .observational) correlated chain_obs_weight_one)
    (by
      rw [recordsAgree_comm]
      exact recordsAgree_of_weight_one
        (predictedTable bowLowerModelGen .observational) correlated bow_obs_weight_one)

/-- A supplied distinct inseparable pair refutes the all-pairs separation test. -/
private theorem not_allPairsSeparated_of_pair
    (tags : List (ExperimentTag signature)) (i j : Fin 3) (hne : i ≠ j)
    (hpair : pairSeparated generators tags i j = false) :
    allPairsSeparated generators tags = false := by
  cases h : allPairsSeparated generators tags with
  | false => rfl
  | true =>
    have pair :
        (decide (i = j) || pairSeparated generators tags i j) = true :=
      List.all_eq_true.mp
        (List.all_eq_true.mp h i (List.mem_finRange i))
        j (List.mem_finRange j)
    have : pairSeparated generators tags i j = true := by
      simpa [decide_eq_false hne] using pair
    rw [hpair] at this
    cases this

/-- Without experiments the distinct catalogue indices remain inseparable. -/
theorem empty_tags_do_not_separate :
    allPairsSeparated generators [] = false :=
  not_allPairsSeparated_of_pair [] (0 : Fin 3) (1 : Fin 3) (by decide) rfl

/-- Observation leaves the chain and selected bow endpoint tied. -/
theorem observational_tags_do_not_separate :
    allPairsSeparated generators [.observational] = false :=
  not_allPairsSeparated_of_pair [.observational] (1 : Fin 3) (2 : Fin 3)
    (by decide) <| by
    simp [pairSeparated, modelsDisagreeOn, generators, List.any_cons, List.any_nil,
      observational_chain_bow_agree]

/-- The intervention alone leaves the independent model and selected bow endpoint tied. -/
theorem doX_tags_do_not_separate :
    allPairsSeparated generators [.intervene doX] = false :=
  not_allPairsSeparated_of_pair [.intervene doX] (0 : Fin 3) (2 : Fin 3)
    (by decide) <| by
    simp [pairSeparated, modelsDisagreeOn, generators, List.any_cons, List.any_nil,
      indep_bow_agree_doX]

/-- The two-experiment family distinguishes the independent SCM from the chain. -/
theorem tiny_separates_indep_chain :
    pairSeparated generators tinyTags (0 : Fin 3) (1 : Fin 3) = true := by
  have hobs :
      recordsAgree (predictedTable independenceModel .observational)
        (predictedTable chainModel .observational) = false :=
    Eq.trans (recordsAgree_comm _ _)
      (recordsAgree_neq_of_unique correlated
        (predictedTable chainModel .observational)
        (predictedTable independenceModel .observational)
        (by
          rw [recordsAgree_comm]
          exact recordsAgree_of_weight_one
            (predictedTable chainModel .observational) correlated
            chain_obs_weight_one)
        (Eq.trans (recordsAgree_comm _ _) indep_obs_misses_correlated))
  simp [pairSeparated, modelsDisagreeOn, generators, tinyTags, List.any_cons,
    List.any_nil, hobs]

/-- Observation distinguishes the independent SCM from the selected bow endpoint. -/
theorem tiny_separates_indep_bow :
    pairSeparated generators tinyTags (0 : Fin 3) (2 : Fin 3) = true := by
  have hobs :
      recordsAgree (predictedTable independenceModel .observational)
        (predictedTable bowLowerModelGen .observational) = false :=
    Eq.trans (recordsAgree_comm _ _)
      (recordsAgree_neq_of_unique correlated
        (predictedTable bowLowerModelGen .observational)
        (predictedTable independenceModel .observational)
        (by
          rw [recordsAgree_comm]
          exact recordsAgree_of_weight_one
            (predictedTable bowLowerModelGen .observational) correlated
            bow_obs_weight_one)
        (Eq.trans (recordsAgree_comm _ _) indep_obs_misses_correlated))
  simp [pairSeparated, modelsDisagreeOn, generators, tinyTags, List.any_cons,
    List.any_nil, hobs]

/-- The hard intervention distinguishes the chain from the selected bow endpoint. -/
theorem tiny_separates_chain_bow :
    pairSeparated generators tinyTags (1 : Fin 3) (2 : Fin 3) = true := by
  have hdo :
      recordsAgree (predictedTable chainModel (.intervene doX))
        (predictedTable bowLowerModelGen (.intervene doX)) = false :=
    recordsAgree_neq_of_unique chainDoLaw
      (predictedTable chainModel (.intervene doX))
      (predictedTable bowLowerModelGen (.intervene doX))
      (Eq.trans (recordsAgree_comm _ _) chain_do_agrees_self)
      (Eq.trans (recordsAgree_comm _ _) bow_do_misses_chain)
  simp [pairSeparated, modelsDisagreeOn, generators, tinyTags, List.any_cons,
    List.any_nil, hdo]

/-- Law disagreement is symmetric, so pair separation does not depend on the order of indices. -/
private theorem pairSeparated_comm {n : Nat}
    (models : Fin n → ExactModel signature)
    (tags : List (ExperimentTag signature)) (i j : Fin n) :
    pairSeparated models tags i j = pairSeparated models tags j i := by
  induction tags with
  | nil => rfl
  | cons tag rest ih =>
      simp only [pairSeparated, List.any_cons] at ih ⊢
      have htag :
          modelsDisagreeOn models i j tag = modelsDisagreeOn models j i tag := by
        simp [modelsDisagreeOn, recordsAgree_comm]
      rw [htag, ih]

/-- Recover equality of finite indices from their natural coordinates for the concrete
three-model case split. -/
private theorem fin3_eq_of_val (i : Fin 3) :
    i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) := by
  have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases this with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- Observation together with do(X=true) separates every distinct pair in this supplied
catalogue. -/
theorem tinyTags_separate :
    allPairsSeparated generators tinyTags = true := by
  refine List.all_eq_true.mpr ?_
  intro i _
  refine List.all_eq_true.mpr ?_
  intro j _
  rcases fin3_eq_of_val i with hi | hi | hi <;>
    rcases fin3_eq_of_val j with hj | hj | hj
  · simp [hi, hj]
  · rw [hi, hj]; simp [tiny_separates_indep_chain]
  · rw [hi, hj]; simp [tiny_separates_indep_bow]
  · rw [hi, hj, pairSeparated_comm]; simp [tiny_separates_indep_chain]
  · simp [hi, hj]
  · rw [hi, hj]; simp [tiny_separates_chain_bow]
  · rw [hi, hj, pairSeparated_comm]; simp [tiny_separates_indep_bow]
  · rw [hi, hj, pairSeparated_comm]; simp [tiny_separates_chain_bow]
  · simp [hi, hj]

/-- The zero-size positional candidate family contains only the empty list. -/
theorem combinations_tiny_zero : combinations tinyTags 0 = [[]] := rfl

/-- Enumerate both one-experiment sublists in candidate order. -/
theorem combinations_tiny_one :
    combinations tinyTags 1 = [[.observational], [.intervene doX]] := rfl

/-- The only full-size combination is the complete two-experiment family. -/
theorem combinations_tiny_two : combinations tinyTags 2 = [tinyTags] := rfl

/-- Expose the exact increasing-cardinality search order for this fixture. -/
theorem combinationsBySize_tiny :
    combinationsBySize tinyTags =
      [[], [.observational], [.intervene doX], tinyTags] := by
  have hlen : tinyTags.length = 2 := rfl
  have hrange : List.range 3 = [0, 1, 2] := rfl
  unfold combinationsBySize
  rw [hlen, hrange]
  change
      combinations tinyTags 0 ++ combinations tinyTags 1 ++ combinations tinyTags 2 =
        [[], [.observational], [.intervene doX], tinyTags]
  rw [combinations_tiny_zero, combinations_tiny_one, combinations_tiny_two]
  rfl

/-- The finite search returns both experiments: neither singleton separates all three models. -/
theorem shortest_separator_is_obs_and_doX :
    shortestSeparatingTags generators tinyTags = some tinyTags := by
  simp [shortestSeparatingTags, combinationsBySize_tiny, firstSatisfying,
    empty_tags_do_not_separate, observational_tags_do_not_separate,
    doX_tags_do_not_separate, tinyTags_separate]

/-- The general minimality theorem proves that no smaller sublist of the supplied
candidates separates the catalogue. -/
theorem shortest_separator_minimal :
    noShorterSeparator generators tinyTags 2 = true := by
  have hlen : tinyTags.length = 2 := rfl
  have h := shortestSeparatingTags_minimal generators tinyTags tinyTags
    shortest_separator_is_obs_and_doX
  rwa [hlen] at h

/-- Exact-law data generated by the chain under the selected separating family select
its catalogue index uniquely. -/
theorem shortest_separator_realizes_chain :
    uniquelyRealizes generators (predictedExperiments chainModel tinyTags)
      ⟨1, by decide⟩ :=
  uniquelyRealizes_of_allPairsSeparated generators tinyTags
    ⟨1, by decide⟩ tinyTags_separate

/-- A two-index family containing the same actual chain SCM twice. -/
def twinChain : Fin 2 → ExactModel signature
  | ⟨0, _⟩ => chainModel
  | ⟨1, _⟩ => chainModel

/-- Repeated model representations predict identical laws for every supplied tag and
therefore cannot be separated. -/
private theorem not_twins_separated (tags : List (ExperimentTag signature)) :
    allPairsSeparated twinChain tags = false := by
  have hpair : pairSeparated twinChain tags (0 : Fin 2) (1 : Fin 2) = false := by
    simp [pairSeparated, modelsDisagreeOn, twinChain, recordsAgree_self]
  cases h : allPairsSeparated twinChain tags with
  | false => rfl
  | true =>
    have pair :
        (decide ((0 : Fin 2) = (1 : Fin 2)) ||
          pairSeparated twinChain tags (0 : Fin 2) (1 : Fin 2)) = true :=
      List.all_eq_true.mp
        (List.all_eq_true.mp h (0 : Fin 2) (List.mem_finRange _))
        (1 : Fin 2) (List.mem_finRange _)
    have : pairSeparated twinChain tags (0 : Fin 2) (1 : Fin 2) = true := by
      simpa using pair
    rw [hpair] at this
    cases this

/-- The shortest-separator search reports failure for the duplicated model family. -/
theorem twins_inseparable_search :
    shortestSeparatingTags twinChain tinyTags = none := by
  simp [shortestSeparatingTags, combinationsBySize_tiny, firstSatisfying,
    not_twins_separated]

/-- The companion pair search explicitly returns the duplicate index pair. -/
theorem twins_inseparable_pair :
    inseparablePair? twinChain tinyTags =
      some ((0 : Fin 2), (1 : Fin 2)) := by
  simp [inseparablePair?, twinChain, tinyTags, pairSeparated, modelsDisagreeOn,
    List.finRange, recordsAgree_self]

end CatalogueInference
end Examples
end Causality
end Thesis
