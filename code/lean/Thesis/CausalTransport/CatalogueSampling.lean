import Thesis.CausalTransport.CatalogueInference
import Thesis.Probability.Distros.PairedCountSampling

namespace Thesis.Causality.CatalogueInference
open Probability Probability.Distros

/-!
# Explicit finite-sample likelihoods and posterior causal uncertainty

An exact probability table, a histogram sampled from a fixed SCM, and a
histogram integrated over a table prior are different inputs. The old
exact-law compatibility gate now rejects count data. This module supplies
the statistical alternatives and gives each an actual normalized sampling
law before extracting a singleton likelihood.

`CountSample` fixes the complete observed-assignment order, including cells
whose count is zero. `CountSamplingLaw.iid` samples a supplied true table;
`CountSamplingLaw.dirichlet` samples the existing rational Pólya process with
explicit prior parameters. `CountSamplingLaw.pairedDirichlet` pairs two
independently parameterized histories before counting, so a factorized and a
saturated parameter model score the same joint sample. These are table-level
parameter priors, not a claim that separately chosen interventional table
priors arise from one
common structural model. Fixed-SCM experiments may be multiplied when their
sampled units are independent. Repeated data about one shared unknown table
must instead update its parameters before scoring a continuation.

The final pushforwards retain posterior uncertainty over *model-conditional*
causal values. They do not identify a unique graph, equate an empirical table
with the population law, or upgrade a posterior mean into an identified
population effect. Conditional targets retain `none` as an actual possible
posterior outcome whenever their conditioner is unsupported in a hypothesis.
-/

universe u
variable {S : ObservedSignature.{0}}

/-- One complete joint count table, in the signature's declared enumeration
order. Its shape is evidence, rather than a comment asking callers to align
an untyped list. An empty sample is legitimate and has likelihood one at the
all-zero histogram. Zero counts are retained and do not remove labels. -/
structure CountSample (S : ObservedSignature.{0}) where
  bins : List Nat
  dimension : bins.length = S.assignmentEnumeration.length

/-- An explicitly declared rational Dirichlet/Pólya prior on the complete
observational alphabet. Individual zero parameters are allowed by the finite
urn semantics, but their unsupported observations cannot produce a posterior. -/
structure DirichletTablePrior (S : ObservedSignature.{0}) where
  parameters : List QProb
  dimension : parameters.length = S.assignmentEnumeration.length
  positive : 0 < (QProb.listSum parameters).num

/-- Independent parameter priors on a row-major coding of the observed
alphabet: pair `(i,j)` means assignment index `i * columns + j` in
`S.assignmentEnumeration`. The product dimension checks that no joint cell
is omitted. Clients whose factors denote particular observed nodes must
check that this coding has their intended interpretation. Pairing is
retained when sampling, so these priors score the
same complete joint histogram as a saturated table prior. The independence
assumption concerns the two parameter families, not integrated-out trials. -/
structure PairedDirichletTablePrior (S : ObservedSignature.{0}) where
  rowParameters : List QProb
  columnParameters : List QProb
  dimension : rowParameters.length * columnParameters.length =
    S.assignmentEnumeration.length
  rowPositive : 0 < (QProb.listSum rowParameters).num
  columnPositive : 0 < (QProb.listSum columnParameters).num

/-- The sampling assumptions belong to the likelihood's input. A fixed law
has independent repeated draws; a table prior has exchangeable Pólya draws.
Neither constructor converts sample frequencies into a claimed true law. -/
inductive CountSamplingLaw (S : ObservedSignature.{0}) where
  | iid (population : FiniteProbRecord S.Assignment)
  | dirichlet (prior : DirichletTablePrior S)
  | pairedDirichlet (prior : PairedDirichletTablePrior S)

namespace CountSamplingLaw

/-- A probability law on the common observed object: the full joint count
table. Every branch therefore scores the same finite statistical experiment. -/
def distribution (sampling : CountSamplingLaw S) (trials : Nat) : Distro (List Nat) :=
  match sampling with
  | .iid population => iidCountDistro ⟨population⟩ S.assignmentEnumeration trials
  | .dirichlet prior =>
      rationalDirichletMultinomialDistro trials prior.parameters prior.positive
  | .pairedDirichlet prior =>
      pairedDirichletCountDistro trials prior.rowParameters prior.columnParameters
        prior.rowPositive prior.columnPositive

/-- The likelihood is an event probability under the declared sampling law,
including likelihood zero for structural impossibilities. -/
def likelihood (sampling : CountSamplingLaw S) (sample : CountSample S) : QProb :=
  (sampling.distribution sample.bins.sum).pmf sample.bins

/-- Each likelihood family is normalized on histograms. This is stronger
than merely giving a nonnegative weight to each catalogue hypothesis. -/
theorem normalization (sampling : CountSamplingLaw S) (trials : Nat) :
    QProb.Equiv ((sampling.distribution trials).record.probVal topEvent) QProb.one :=
  Distro.normalization _

end CountSamplingLaw

/-- Bayesian updating on one common count sample. Each hypothesis supplies
an explicit normalized law on exactly the same histogram space. Rational
likelihoods are converted to common-scale natural weights by the existing
denominator-clearing construction; unsupported evidence keeps the posterior
absent rather than restarting a uniform prior. -/
def countPosterior? {n : Nat} {α : Type u} (catalogue : Catalogue n α)
    (sampling : Fin n → CountSamplingLaw S) (sample : CountSample S) :
    Option (Distro (Fin n)) :=
  posterior? catalogue.prior (qprobWeights n (fun i => (sampling i).likelihood sample))

/-- A sampled cohort generated observationally or by one specified hard
intervention. The same signature order is used for every hypothesis. -/
structure CountExperiment (S : ObservedSignature.{0}) where
  tag : ExperimentTag S
  sample : CountSample S

/-- Ordinary multinomial likelihood of counts from a fully specified SCM.
The prediction is fixed; no concentration-one Dirichlet prior is silently
placed around it. The underlying `iidCountDistro` is the histogram of actual
independent repetitions of this model's interventional finite law. -/
def iidModelCountLikelihood (model : ExactModel S) (experiment : CountExperiment S) : QProb :=
  (CountSamplingLaw.iid (predictedTable model experiment.tag)).likelihood experiment.sample

/-- Independent sampled units in separate fixed-model experiments give a
product likelihood. This conditional-on-model independence does not license
restarting a shared unknown-parameter prior separately for each dataset. -/
def iidExperimentLikelihood (model : ExactModel S) (experiments : List (CountExperiment S)) : QProb :=
  independentQProb (experiments.map (iidModelCountLikelihood model))

/-- Posterior over actual SCMs after conditionally independent cohorts.
Every cohort has a tag identifying the experiment that generated its sample.
This wrapper uses fixed-SCM likelihoods throughout; no parameter-prior reset
is hidden inside the experiment fold. -/
def iidModelPosterior? {n : Nat} (catalogue : Catalogue n (ExactModel S))
    (experiments : List (CountExperiment S)) : Option (Distro (Fin n)) :=
  posterior? catalogue.prior
    (qprobWeights n (fun i => iidExperimentLikelihood (catalogue.item i) experiments))

/-- Update a table prior only when the actually observed histogram has
positive probability. Impossible evidence stays `none`; no smoothing fallback
changes a declared structural zero into an admissible observation. The
sufficient-count law computes only one future draw. The conditioning theorem
below identifies it with the potentially much larger explicit history filter. -/
def DirichletTablePrior.predictive? (prior : DirichletTablePrior S)
    (sample : CountSample S) : Option (Distro S.Assignment) :=
  if supported : rationalCountsSupported sample.bins.sum prior.parameters sample.bins then
    some ((rationalPolyaDistro 1 (updateRationalParameters prior.parameters sample.bins)
      (updateRationalParameters_positive prior.parameters sample.bins prior.positive
        (rationalCountsSupported_shape sample.bins.sum prior.parameters sample.bins supported).1)).map fun word =>
        S.assignmentEnumeration.getD (word.headD 0) S.defaultValue)
  else none

/-- The supported predictive law is precisely the existing Pólya continuation
with sufficient-count parameters `alpha + counts`. This reuses the actual
conditioning theorem rather than declaring empirical frequencies predictive. -/
theorem DirichletTablePrior.predictive_updated (prior : DirichletTablePrior S)
    (sample : CountSample S)
    (supported : rationalCountsSupported sample.bins.sum prior.parameters sample.bins) :
    ((rationalCountsContinuation sample.bins.sum 1 prior.parameters sample.bins
      prior.positive supported).map (fun word =>
        S.assignmentEnumeration.getD (word.headD 0) S.defaultValue)).SameLaw
      ((rationalPolyaDistro 1 (updateRationalParameters prior.parameters sample.bins)
        (updateRationalParameters_positive prior.parameters sample.bins prior.positive
          (rationalCountsSupported_shape sample.bins.sum prior.parameters sample.bins supported).1)).map
        (fun word => S.assignmentEnumeration.getD (word.headD 0) S.defaultValue)) :=
  (rationalCountsContinuation_updated sample.bins.sum 1 prior.parameters sample.bins
    prior.positive supported).map _

/-- Successful prediction uses exactly the sufficient-count law whose
conditioning interpretation was proved above. This equation also documents
that the runtime path need not enumerate all previously observed histories. -/
theorem DirichletTablePrior.predictive_of_supported (prior : DirichletTablePrior S)
    (sample : CountSample S)
    (supported : rationalCountsSupported sample.bins.sum prior.parameters sample.bins) :
    prior.predictive? sample = some
      ((rationalPolyaDistro 1 (updateRationalParameters prior.parameters sample.bins)
        (updateRationalParameters_positive prior.parameters sample.bins prior.positive
          (rationalCountsSupported_shape sample.bins.sum prior.parameters sample.bins supported).1)).map
        (fun word => S.assignmentEnumeration.getD (word.headD 0) S.defaultValue)) := by
  simp only [DirichletTablePrior.predictive?, dif_pos supported]

/-- Unsupported evidence has no posterior prediction. The rejection is
about the actual observed count vector, not a demand that every possible
outcome have positive prior probability. -/
theorem DirichletTablePrior.predictive_none_of_unsupported (prior : DirichletTablePrior S)
    (sample : CountSample S)
    (unsupported : ¬ rationalCountsSupported sample.bins.sum prior.parameters sample.bins) :
    prior.predictive? sample = none := by
  simp only [DirichletTablePrior.predictive?, dif_neg unsupported]

/-- Posterior uncertainty over unconditional model-conditional causal
predictions. Every atom is an actual model; disagreeing values remain distinct
outcomes. A point mass is not asserted merely because a weighted mean exists. -/
def posteriorCausalValues {n : Nat} (models : Fin n → ExactModel S)
    (posterior : Distro (Fin n)) (action : HardIntervention S)
    (event : Event S.Assignment) : Distro QProb :=
  posterior.map fun i => (models i).interventionalValue action.value event

/-- All posterior events on causal predictions are pushforwards of their
actual hypothesis masses. This retains uncertainty without a unique-DAG or
graph-class identification claim. -/
theorem posteriorCausalValues_event {n : Nat} (models : Fin n → ExactModel S)
    (posterior : Distro (Fin n)) (action : HardIntervention S)
    (event : Event S.Assignment) (values : Event QProb) :
    QProb.Equiv ((posteriorCausalValues models posterior action event).record.probVal values)
      (posterior.record.probVal fun i => values ((models i).interventionalValue action.value event)) :=
  Distro.map_probVal _ _ _

/-- A separate posterior mean is a model-averaged prediction, not an
identification certificate. Its name makes that interpretation explicit. -/
def posteriorMeanCausalPrediction {n : Nat} (models : Fin n → ExactModel S)
    (posterior : Distro (Fin n)) (action : HardIntervention S)
    (event : Event S.Assignment) : QProb :=
  posterior.expectation fun i => (models i).interventionalValue action.value event

/-- General partial queries retain an unsupported conditioner as `none` in
the posterior distribution. Discarding such hypotheses and renormalizing
would be an extra inference rule, so this constructor does neither. -/
def posteriorQueryValues {n : Nat} (models : Fin n → ExactModel S)
    (posterior : Distro (Fin n)) (query : ProbabilityTerm S)
    (reference : S.Assignment) : Distro ProbabilityResult.Result :=
  posterior.map fun i => query.denote (models i) reference

/-! ## One shared target across the posterior model family

The historical display catalogue permits differently typed answers to be
placed beside one another. Its agreement summary is useful for presentation,
but two equal numbers for unrelated queries do not certify one causal effect.
The following report makes the missing coherence requirement a type index:
every hypothesis asks the same source term at the same reference, and its
answer is certified against that hypothesis's actual generative SCM.
-/

/-- A posterior and a family of answers for one fixed causal query. The SCM
may vary with the hypothesis; the source term and assignment cannot. Failed
identification, unsupported conditioning, and denied access remain possible
outcomes rather than being silently removed from the posterior support. -/
structure CertifiedPosteriorQuery {n : Nat} (models : Fin n → ExactModel S)
    (source : ProbabilityTerm S) (reference : S.Assignment) where
  posterior : Distro (Fin n)
  answers : (i : Fin n) → CertifiedQuery.Answer source (models i) reference

/-- A display outcome preserves which guarantee was established. In
particular a failed certificate is not the same outcome as a mathematically
undefined conditioner, and neither is represented by the numerical zero. -/
inductive PosteriorAnswerStatus where
  | identified (value : ProbabilityResult.Result)
  | bounded (lower upper : QProb)
  | undefined
  | failed
  | unfinished
  | modeUnsupported

namespace CertifiedPosteriorQuery

/-- Erase proof payloads only after the shared-query and actual-model
indices have been checked. The indexed evidence remains in `report.answers`.
This map is used solely to present posterior uncertainty over the outcomes. -/
def status {n : Nat} {models : Fin n → ExactModel S}
    {source : ProbabilityTerm S} {reference : S.Assignment}
    (report : CertifiedPosteriorQuery models source reference) (i : Fin n) :
    PosteriorAnswerStatus :=
  match report.answers i with
  | .identified evidence => .identified evidence.value
  | .bounded evidence => .bounded evidence.certificate.lower evidence.certificate.upper
  | .undefined => .undefined
  | .failed _ => .failed
  | .unfinished => .unfinished
  | .modeUnsupported => .modeUnsupported

/-- Posterior uncertainty is an actual pushforward of the hypothesis law.
It retains every diagnostic outcome with its original probability mass. -/
def statusLaw {n : Nat} {models : Fin n → ExactModel S}
    {source : ProbabilityTerm S} {reference : S.Assignment}
    (report : CertifiedPosteriorQuery models source reference) :
    Distro PosteriorAnswerStatus :=
  report.posterior.map report.status

/-- All events on the displayed outcomes retain the probability of their
preimage in the model catalogue. No missing certificate is conditioned away. -/
theorem statusLaw_event {n : Nat} {models : Fin n → ExactModel S}
    {source : ProbabilityTerm S} {reference : S.Assignment}
    (report : CertifiedPosteriorQuery models source reference)
    (event : Event PosteriorAnswerStatus) :
    QProb.Equiv (report.statusLaw.record.probVal event)
      (report.posterior.record.probVal (fun i => event (report.status i))) :=
  Distro.map_probVal _ _ _

/-- An identified branch computes this report's common query in the actual
model indexed by `i`. The branch equation links the evidence to the report;
the certificate's own theorem supplies class-wide validity and local support. -/
noncomputable def source_correct_of_identified {n : Nat}
    {models : Fin n → ExactModel S} {source : ProbabilityTerm S}
    {reference : S.Assignment}
    (report : CertifiedPosteriorQuery models source reference) (i : Fin n)
    (evidence : CertifiedQuery.FormulaCertificate.At source (models i) reference)
    (_identified : report.answers i = .identified evidence) :
    ProbabilityResult.Equivalent (source.denote (models i) reference) evidence.value :=
  evidence.correct

/-- A bounded branch encloses the actual supported value of this same
posterior target in its actual model. As with formula branches, the report
retains the class and application premises instead of treating displayed
endpoint numbers as sufficient evidence. -/
theorem source_enclosed_of_bounded {n : Nat}
    {models : Fin n → ExactModel S} {source : ProbabilityTerm S}
    {reference : S.Assignment}
    (report : CertifiedPosteriorQuery models source reference) (i : Fin n)
    (evidence : CertifiedQuery.BoundsCertificate.At source (models i) reference)
    (_bounded : report.answers i = .bounded evidence) :
    QProb.LE evidence.certificate.lower evidence.supported.1 ∧
      QProb.LE evidence.supported.1 evidence.certificate.upper :=
  evidence.correct

end CertifiedPosteriorQuery

end Thesis.Causality.CatalogueInference
