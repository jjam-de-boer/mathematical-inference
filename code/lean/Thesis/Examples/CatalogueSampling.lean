import Thesis.CausalTransport.CatalogueSampling
import Thesis.CausalTransport.CertifiedModeInference
import Thesis.Examples.CatalogueInference

namespace Thesis.Causality.Examples.CatalogueSampling
open Probability Probability.Distros BinaryBow
open Causality.CatalogueInference
open Examples.CatalogueInference

-- The six-observation fixtures reduce finite histograms inside the kernel.
-- These are the existing example-level recursion/heartbeat allowances; the
-- compiler's memory ceiling and single-family build policy are unchanged.
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# Sampling uncertainty and an actually certified catalogue answer

The older graph-tagged catalogue remains useful for displaying proposed
formulas, but a graph and a numerical table do not establish the application
premises of a causal identification theorem.  This regression instead uses
actual SCMs and the supported guarded-ID certificate.  Its accepted answer
therefore carries the precise source query, projected graph class and local
support data, while the sample likelihood is an independently specified
statistical experiment.

The examples deliberately separate three uses of a table.  A fully known
copy-chain predicts six repeated successes with probability one.  A fixed
independent fair outcome predicts the same sample with probability `1/64`.
A uniform table prior updated by the diagonal observational sample produces
posterior predictions with positive off-diagonal mass, even though those
cells have empirical count zero.  Impossible observations under a structural
zero remain unsupported rather than receiving invented smoothing mass.
-/

/-- The complete six-observation `do(X=true)` histogram from the catalogue
fixture. The count order is the signature's actual assignment enumeration. -/
def sixSuccesses : CountSample signature where
  bins := chainDoBins
  dimension := by decide +kernel

/-- Declare that the six observations came from one fixed intervention cohort rather
than from an exact population law. -/
def successExperiment : CountExperiment signature :=
  ⟨.intervene doX, sixSuccesses⟩

/-- The deterministic copy-chain makes every repeated outcome certain. This
is an IID likelihood at a fixed SCM, with no table prior inserted around it. -/
theorem deterministic_sample_likelihood :
    QProb.Equiv (iidModelCountLikelihood chainModel successExperiment) QProb.one := by
  decide +kernel

/-- Six independent fair outcomes all succeeding have probability `2^-6`.
This distinguishes a fixed-SCM sampling law from a reinforced urn model. -/
theorem fair_sample_likelihood :
    QProb.Equiv (iidModelCountLikelihood independenceModel successExperiment)
      ⟨1, 64, by decide⟩ := by
  decide +kernel

/-! ## Finite-sample posterior uncertainty over causal predictions

Six successes strongly favour the copy-chain, but the independent fair
outcome model still has nonzero likelihood. Both actual SCMs therefore keep
posterior mass. Their causal predictions differ, which must remain visible
even though a posterior-weighted mean can also be computed.
-/

def twoModels (i : Fin 2) : ExactModel signature :=
  if i.val = 0 then chainModel else independenceModel

/-- Exact representatives of the two likelihoods proved above. Keeping
these small representatives makes subsequent posterior arithmetic cheap;
the theorem immediately below ties them to the actual sampling programs. -/
def twoLikelihoods (i : Fin 2) : QProb :=
  if i.val = 0 then QProb.one else ⟨1, 64, by decide⟩

/-- The small rational likelihood representatives equal the actual IID sampling
probabilities at both model indices. -/
theorem twoLikelihoods_sampling (i : Fin 2) :
    QProb.Equiv (iidModelCountLikelihood (twoModels i) successExperiment)
      (twoLikelihoods i) := by
  by_cases first : i.val = 0
  · simpa only [twoModels, twoLikelihoods, if_pos first] using deterministic_sample_likelihood
  · simpa only [twoModels, twoLikelihoods, if_neg first] using fair_sample_likelihood

/-- Give the two generative SCMs equal prior mass before seeing the cohort. -/
def twoCatalogue : Catalogue 2 (ExactModel signature) :=
  Catalogue.uniform 2 twoModels (by decide)

/-- Clear both likelihood denominators with a single common scale, preserving their
Bayesian odds. -/
def twoWeights : Fin 2 → Nat := qprobWeights 2 twoLikelihoods

/-- The observed cohort has positive prior-predictive probability, so Bayesian
normalization is supported. -/
private theorem twoEvidencePositive :
    0 < natIntegral twoCatalogue.prior.record.atoms twoWeights := by decide +kernel

/-- Normalize the actual model likelihoods, using the supported small representatives
proved above. No fallback distribution is supplied. -/
def twoPosterior : Distro (Fin 2) :=
  twoCatalogue.prior.reweightNat twoWeights twoEvidencePositive

/-- The posterior probabilities are `64/65` and `1/65`. A finite observed
sample does not become a proof that the less probable hypothesis is false. -/
theorem both_models_remain :
    QProb.Equiv (twoPosterior.pmf (0 : Fin 2)) ⟨64, 65, by decide⟩ ∧
      QProb.Equiv (twoPosterior.pmf (1 : Fin 2)) ⟨1, 65, by decide⟩ := by
  constructor <;> decide +kernel

/-- Push the posterior onto each model's population intervention risk. Different model
predictions remain distinct outcomes. -/
def causalValues : Distro QProb :=
  posteriorCausalValues twoModels twoPosterior doX (fun assignment => assignment y)

/-- Numerical-value events compare rational magnitudes, not arbitrary
unreduced presentations. The posterior keeps the two causal predictions
separate with their respective hypothesis probabilities. -/
theorem posterior_keeps_causal_disagreement :
    QProb.Equiv (causalValues.record.probVal (fun value => decide (QProb.Equiv value QProb.one)))
      ⟨64, 65, by decide⟩ ∧
    QProb.Equiv (causalValues.record.probVal (fun value => decide (QProb.Equiv value ⟨1, 2, by decide⟩)))
      ⟨1, 65, by decide⟩ := by
  constructor <;> decide +kernel

/-- The model-averaged prediction is a third number, `129/130`. Its name
and separate result type prevent confusing that average with either model's
causal value or with a class-wide identification certificate. -/
theorem posterior_mean_is_an_average :
    QProb.Equiv (posteriorMeanCausalPrediction twoModels twoPosterior doX
      (fun assignment => assignment y)) ⟨129, 130, by decide⟩ := by
  decide +kernel

/-- Each actual generative hypothesis asks the same causal source at the
same reference. The mode's belief is its population prior here; a separate
current-belief query would require the representation supplied by that API. -/
def modelPolicy (model : ExactModel signature) : ModeQueryPolicy signature where
  mode := ⟨model, model.prior⟩
  intervenable := NodeSet.full

/-- Apply the same guarded identification target to each actual model while retaining
its source, reference and application evidence. -/
noncomputable def certifiedPosterior :
    CertifiedPosteriorQuery twoModels query.sourceTerm reference where
  posterior := twoPosterior
  answers i := (modelPolicy (twoModels i)).identifyJoint query reference none none

/-- Recognize a defined certified formula result. Undefined or uncertified outcomes do
not pass this display test. -/
def statusIdentified : PosteriorAnswerStatus → Bool
  | .identified (some _) => true
  | _ => false

/-- Both hypotheses have a supported graph-class certificate, even though
their numerical answers disagree. Certification concerns the shared causal
functional; posterior concentration and agreement are separate questions. -/
theorem all_posterior_answers_certified :
    QProb.Equiv (certifiedPosterior.statusLaw.record.probVal statusIdentified) QProb.one := by
  decide +kernel

/-- The original observational histogram is a finite sample, not a supplied
exact population law. Its dimension is checked against the full alphabet. -/
def diagonalSample : CountSample signature where
  bins := bins
  dimension := by simp [Examples.CatalogueInference.bins, labels, List.length_map]

/-- Declare one unit of Pólya/Dirichlet parameter mass for every joint assignment,
including empirically unobserved cells. -/
def uniformTablePrior : DirichletTablePrior signature where
  parameters := uniformAlphas
  dimension := by decide +kernel
  positive := uniformAlphas_pos

/-- Two independent uniform Beta priors, encoded in the same complete
four-cell alphabet as the saturated table prior. The observed histogram
retains the association between the two Bernoulli coordinates. -/
def independentBetaPrior : PairedDirichletTablePrior signature where
  rowParameters := twoAlphas
  columnParameters := twoAlphas
  dimension := by decide +kernel
  rowPositive := twoAlphas_pos
  columnPositive := twoAlphas_pos

/-- The imposed row-major code really uses the two observed Bernoulli
coordinates: rows encode Y and columns encode X in this signature's actual
enumeration. Thus the two independent parameter families are the intended
node margins, rather than an arbitrary four-state recoding. -/
theorem paired_coding_coordinates :
    ∀ row column : Fin 2,
      let assignment := signature.assignmentEnumeration.getD
        (row.val * 2 + column.val) signature.defaultValue
      assignment x = decide (column.val = 1) ∧
        assignment y = decide (row.val = 1) := by
  decide +kernel

/-- The typed sampling interface gives the repaired joint-count likelihood;
it never replaces paired counts by the two marginal count events. -/
theorem typed_independence_likelihood :
    QProb.Equiv ((CountSamplingLaw.pairedDirichlet independentBetaPrior).likelihood
      diagonalSample) ⟨1, 980, by decide⟩ :=
  independence_joint_likelihood

/-- The saturated parameter model scores the identical count sample. The
difference in likelihood therefore reflects model assumptions rather than
a change in what data are regarded as observed. -/
theorem typed_saturated_likelihood :
    QProb.Equiv ((CountSamplingLaw.dirichlet uniformTablePrior).likelihood
      diagonalSample) ⟨1, 84, by decide⟩ :=
  saturated_joint_likelihood

/-- A prior-conditioned predictive table exists for this observed sample.
The definition never falls back to empirical frequencies when support fails. -/
theorem diagonal_predictive_supported :
    (uniformTablePrior.predictive? diagonalSample).isSome = true := by
  decide +kernel

/-- Inspect one posterior event without choosing a distribution from an
existential proposition. A missing supported prediction stays `none`. -/
def predictiveOffDiagonal : Option QProb :=
  (uniformTablePrior.predictive? diagonalSample).map fun law =>
    law.record.probVal (fun assignment => !assignment x && assignment y)

/-- Check a partial numerical output against an expected rational magnitude. Missing
support cannot equal a supplied number. -/
def optionMassIs (value : Option QProb) (expected : QProb) : Bool :=
  match value with
  | none => false
  | some actual => decide (QProb.Equiv actual expected)

/-- Recover the data-valued partial-result equality from a checked Boolean
test. Only the explicit `some` branch supplies a value; no existential
support proof is eliminated into computational data. -/
def equivalentOfMassTest (actual : ProbabilityResult.Result) (expected : QProb)
    (checked : optionMassIs actual expected = true) :
    ProbabilityResult.Equivalent actual (some expected) := by
  cases actual with
  | none => cases checked
  | some value => exact .value (of_decide_eq_true checked)

/-- The updated parameters are `(4,1,1,4)` in a suitable binary order.
The unobserved off-diagonal cell therefore has predictive mass `1/10`. -/
theorem predictive_is_not_empirical :
    optionMassIs predictiveOffDiagonal ⟨1, 10, by decide⟩ = true ∧
      QProb.Equiv (countLaw.probVal (fun assignment => !assignment x && assignment y))
        QProb.zero := by
  constructor <;> decide +kernel

/-- A structural-zero prior supports only the first declared assignment.
The finite Pólya semantics permits zero parameters but does not permit an
observation in a colour that can never be drawn. -/
def pointTablePrior : DirichletTablePrior signature where
  parameters := [QProb.one, QProb.zero, QProb.zero, QProb.zero]
  dimension := by decide +kernel
  positive := by decide

/-- Observe a cell forbidden by the point-supported parameter prior, keeping the full
table dimension. -/
def impossibleSample : CountSample signature where
  bins := [0, 1, 0, 0]
  dimension := by decide +kernel

/-- Impossible evidence returns no predictive distribution instead of erasing a
structural zero by smoothing. -/
theorem structural_zero_prediction_unsupported :
    (pointTablePrior.predictive? impossibleSample).isNone = true := by
  decide +kernel

/-- One impossible observation from the fixed copy-chain intervention law.
The same full count object is retained; its likelihood is not estimated
from its empirical frequency table. -/
def impossibleExperiment : CountExperiment signature :=
  ⟨.intervene doX, impossibleSample⟩

/-- Fixed-SCM sampling preserves a deterministic structural zero exactly,
just as the parameter-prior predictive path preserves its own support. -/
theorem iid_structural_zero_likelihood :
    QProb.Equiv (iidModelCountLikelihood chainModel impossibleExperiment) QProb.zero := by
  decide +kernel

/-- A one-model catalogue makes the unsupported-evidence boundary explicit:
there is no other generative hypothesis to which mass could be transferred. -/
def chainOnlyCatalogue : Catalogue 1 (ExactModel signature) :=
  Catalogue.uniform 1 (fun _ => chainModel) (by decide)

/-- An impossible fixed-model sample exhausts its catalogue. The public
posterior interface returns absence rather than a normalized fallback. -/
theorem impossible_iid_posterior_unsupported :
    (iidModelPosterior? chainOnlyCatalogue [impossibleExperiment]).isNone = true := by
  decide +kernel

/-- A successful graph program supplies actual syntax. Its replacement
certificate below is still a theorem of the projected model class, not a
manual formula override or a check that one numerical table looks plausible. -/
def guardedChainFormula : ProbabilityTerm signature :=
  match identifyGuardedJointKernel chainModel.observedGraph query with
  | .identified formula => formula
  | _ => .zero

/-- The guarded graph program really returned the stored expression; the fallback syntax
branch is not the observed outcome. -/
theorem guarded_chain_success :
    identifyGuardedJointKernel chainModel.observedGraph query =
      .identified guardedChainFormula := by
  rfl

/-- Explicit positive local support of this printed expression. The copy
model has observational zeros, so global positivity is deliberately absent. -/
def chainPrintedSupport : guardedChainFormula.SupportedAt chainModel reference :=
  ⟨QProb.one, equivalentOfMassTest _ _ (by decide +kernel)⟩

/-- Apply the graph-class soundness theorem to the actual copy-chain with explicit local
support. Observational zeros remain permitted. -/
noncomputable def chainCertificate :
    CertifiedQuery.FormulaCertificate.At query.sourceTerm chainModel reference where
  certificate := jointFormulaCertificate chainModel.observedGraph query guarded_chain_success
  member := fun _ _ => rfl
  sourceSupported := ⟨QProb.one, equivalentOfMassTest _ _ (by decide +kernel)⟩
  formulaSupported := chainPrintedSupport

/-- Enter the public certified adapter using the full applied certificate, rather than a
caller-proposed numerical formula. -/
noncomputable def certifiedChainAnswer : TemplateAnswer signature :=
  answerOf chainCertificate

/-- The certified number is the actual causal value, while its proof records
the whole graph class and the used-conditional application domain. -/
theorem certified_chain_value :
    optionMassIs certifiedChainAnswer.identifiedValue QProb.one = true := by
  decide +kernel

/-- Raw syntax remains a candidate, including an arbitrary proposed zero.
It cannot enter the certified point-mixture path. -/
theorem zero_proposal_is_not_a_certificate :
    (candidateAnswerOf chainGraph query (.law correlated) reference none (some .zero)).identifiedValue =
      none :=
  candidateAnswerOf_not_certified _ _ _ _ _ _

/-! ## A pointwise fact cannot stand in for projected-graph certification -/

/-- The fair independent model shares the declared graph with the copy
model, but evaluates the requested intervention to one half. -/
private theorem independentInCopyClass :
    HasProjectedGraph independenceModel chainModel.observedGraph := by
  unfold HasProjectedGraph
  decide +kernel

private def independentQuerySupport :
    query.sourceTerm.SupportedAt independenceModel reference :=
  ⟨⟨1, 2, by decide⟩, equivalentOfMassTest _ _ (by decide +kernel)⟩

/-- The value one is correct in the copy model at the requested reference.
It cannot certify a constant replacement over the policy's supported domain. -/
theorem no_constant_one_replacement :
    ¬ ∃ replacement : CertifiedQuery.FormulaCertificate.Total query.sourceTerm
        (fun model => HasProjectedGraph model chainModel.observedGraph),
      replacement.certificate.formula = .one := by
  rintro ⟨replacement, constant⟩
  have agreement := replacement.certificate.sound independenceModel independentInCopyClass
    reference independentQuerySupport
    (replacement.defined independenceModel independentInCopyClass reference independentQuerySupport)
  have impossible := ProbabilityResult.trans (ProbabilityResult.symm independentQuerySupport.2) agreement
  rw [constant] at impossible
  change ProbabilityResult.Equivalent (some ⟨1, 2, by decide⟩) (some QProb.one) at impossible
  cases impossible with
  | value falseEquality => cases falseEquality

/-- The same scope applies to enclosures. The correct singleton interval at
the copy model cannot be supplied as a bound for the entire class. -/
theorem no_point_one_bound :
    ¬ ∃ bounds : CertifiedQuery.BoundsCertificate query.sourceTerm
        (fun model => HasProjectedGraph model chainModel.observedGraph),
      bounds.lower = QProb.one ∧ bounds.upper = QProb.one := by
  rintro ⟨bounds, lower, _⟩
  have impossible := (bounds.valid independenceModel independentInCopyClass reference
    independentQuerySupport.1 independentQuerySupport.2).1
  rw [lower] at impossible
  change 2 ≤ 1 at impossible
  omega

end Thesis.Causality.Examples.CatalogueSampling
