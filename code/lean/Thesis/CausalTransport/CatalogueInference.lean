import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ObservationalEvaluation
import Thesis.Causality.HardIntervention
import Thesis.Probability.Distros.Categorical
import Thesis.Probability.Distros.Reweight
import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.Distros.Moments
import Thesis.Probability.QProbOrder
import Thesis.Causality.CertifiedQuery
import Thesis.Probability.Distros.PairedCountSampling

namespace Thesis
namespace Causality
namespace CatalogueInference

open Probability Probability.Distros Probability.Combinatorics

/-!
# Bayesian posterior on a finite catalogue, with kernel ID or bounds

Layer 1 places a `Distro` prior on a finite list of hypotheses and updates
it by supported reweighting. Layer 2 can display syntax from `identifyJointKernel`
and proposed bounds, but a displayed graph/table candidate has no causal
certificate. Accepted numerical identification and bounds instead retain
`CertifiedQuery` evidence for the actual source, model class and application.
The query-indexed statistical interface lives in `CatalogueSampling`.

Hypotheses are caller-declared, or any already enumerated finite list
including `nativeTemplateCatalogue` at explicit node/source bounds. Templates
of one hidden DAG share that DAG's observed graph, so Layer 2 is constant
on such a list; Regime A/B still distinguish mechanism shapes.

Regime A is a 0/1 whole-law likelihood: whether the hypothesis realizes the
supplied record, including zeros, on each independent dataset. A dataset is
observational (`do` empty) or a `HardIntervention`. Graphs-only atoms cannot
generate \(P(\cdot\mid do(x))\); scoring an interventional table requires a
realized SCM (or an explicit predicted table). Bounds-only atoms may
**exclude** a query margin outside `[lo, hi]`; data inside the interval does
not confirm the atom. Exact-law compatibility accepts only exact-law data.
Statistical counts use the explicit IID or Dirichlet/Pólya sampling interfaces
in `CatalogueSampling`; empirical frequencies are not substituted for the
unknown true table. The legacy `regimeBMass` is an explicitly concentration-one
table-prior construction around predicted masses, not a fixed-SCM IID law.

Independent experiments multiply natural weights. If every positive-prior
atom then has likelihood 0, `posterior?` / `infer` return `none` and the
mixture is `empty`: the catalogue is **exhausted**, not replaced by a
silent fallback graph. Complexity scores belong only as prior weights.

A finite list of mutually disagreeing generative SCMs is **separated** by
those experiments: Regime A is then a point mass on the unique realizer,
not a unique DAG of the world. A supplied assignment self-map may be
ANDed into Regime A as an invariance constraint on the **hypothesis**
(not inferred from data, not PC). `nativeTemplateCatalogue` may be
filtered by a supplied node self-map of the host observed graph;
templates of one hidden DAG share that graph, so that filter is
all-or-nothing. Observational-only gating remains
`regimeAInvariantModelWeight`; per-experiment gating also requires the
predicted `do` table to be invariant. A list of graph-tagged atoms may
keep some graphs and drop others. A bounded search of this signature's
finite hard interventions returns a shortest separating experiment list,
or an inseparable pair; it does not claim a unique DAG. These raw self-map
checks establish neither invertibility nor coherent symmetry. The typed
finite-group interface in `CatalogueSymmetry` supplies those guarantees.

Defined-zero and undefined formula values stay distinct. No `0/0`
completion. Identified formulas remain action-free observational terms
evaluated on observational tables. Interventional scoring is likelihood,
not a second ID engine. Graph-query Shannon entropy remains a separate
diagnostic.
-/

universe u
variable {α : Type u} {S : ObservedSignature.{0}}

/-- One finite table: a whole law or a count word on observed assignments. -/
inductive CatalogueData (S : ObservedSignature) where
  | law (record : FiniteProbRecord S.Assignment)
  | counts (labels : List S.Assignment) (bins : List Nat)

/-- Empty `do` is observation; a nonempty `HardIntervention` is an experiment. -/
inductive ExperimentTag (S : ObservedSignature) where
  | observational
  | intervene (action : HardIntervention S)

/-- One independent dataset: a tag plus a law or count table. -/
structure Experiment (S : ObservedSignature) where
  tag : ExperimentTag S
  data : CatalogueData S

/-- Attach the observation tag without changing the supplied data object. -/
def observationalExperiment (data : CatalogueData S) : Experiment S :=
  ⟨.observational, data⟩

/-- Record which hard intervention generated this dataset. Every hypothesis is scored
using the same tag. -/
def interveneExperiment (action : HardIntervention S) (data : CatalogueData S) :
    Experiment S :=
  ⟨.intervene action, data⟩

/-- The action used to generate a predictive table. Empty `do` is
`HardIntervention.empty`. -/
def ExperimentTag.action : ExperimentTag S → HardIntervention S
  | .observational => HardIntervention.empty S
  | .intervene action => action

/-- Finite labelled catalogue with a categorical prior on its indices.
The item universe is independent of the finite index universe, so atoms may
be full generative SCM records as well as small graph or template labels. -/
structure Catalogue (n : Nat) (α : Type u) where
  item : Fin n → α
  prior : Distro (Fin n)

/-- Wrap any finite list, including `nativeTemplateCatalogue` at given bounds. -/
def ofList (items : List α) (weights : Fin items.length → Nat)
    (positive : 0 < natSum items.length (finWeight weights)) :
    Catalogue items.length α where
  item := fun i => items.get i
  prior := categoricalDistro items.length weights positive

/-- Uniform prior on a nonempty list. Caller-supplied weights remain the
general case; this is the special case of equal natural weights. -/
def uniformOfList (items : List α) (nonempty : 0 < items.length) :
    Catalogue items.length α :=
  ofList items (fun _ => 1) (by
    have h : natSum items.length (finWeight (fun _ : Fin items.length => 1)) =
        items.length := finWeight_one items.length
    simpa [h] using nonempty)

/-- Equip an explicitly indexed nonempty family with equal prior mass. Duplicate indices
remain separate atoms. -/
def Catalogue.uniform (n : Nat) (item : Fin n → α) (nonempty : 0 < n) :
    Catalogue n α where
  item := item
  prior := discreteUniformDistro n nonempty

/-- Boolean 0/1 Regime A weight. -/
def boolWeight : Bool → Nat
  | false => 0
  | true => 1

/-- Simpler atoms get more prior mass: `budget + 1 - complexity`, zero if
complexity exceeds the budget. This is a prior, not a data score. After
observational likelihoods are equal, posterior odds equal these prior odds. -/
def complexityWeight (budget complexity : Nat) : Nat :=
  if complexity ≤ budget then budget + 1 - complexity else 0

/-- Normalize the declared complexity weights. Supplied positivity prevents an all-zero prior. -/
def ofListByComplexity (items : List α) (complexity : Fin items.length → Nat)
    (budget : Nat)
    (positive : 0 < natSum items.length
      (finWeight (fun i => complexityWeight budget (complexity i)))) :
    Catalogue items.length α :=
  ofList items (fun i => complexityWeight budget (complexity i)) positive

/-- Product of independent natural experiment weights. The empty list is
likelihood 1 (no data). -/
def mulNatList : List Nat → Nat
  | [] => 1
  | w :: rest => w * mulNatList rest

/-- Combine independent experiment weights, with neutral weight one for no experiments. -/
def independentWeights (perExperiment : List Nat) : Nat :=
  mulNatList perExperiment

/-- Product of independent rational masses (Regime B across experiments). -/
def mulQProbList : List QProb → QProb
  | [] => QProb.one
  | w :: rest => QProb.mul w (mulQProbList rest)

/-- Combine rational experiment probabilities under conditional independence. Shared
unknown parameters instead need a joint sampling model. -/
def independentQProb (masses : List QProb) : QProb :=
  mulQProbList masses

/-- Product of natural coordinates, used to clear rational likelihood dens. -/
def natProduct : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 1
  | n + 1, values =>
      values (Fin.last n) * natProduct n (fun i => values i.castSucc)

/-- Positive factors give a positive common scale, including the empty product. -/
theorem natProduct_pos (n : Nat) (values : Fin n → Nat)
    (positive : ∀ i, 0 < values i) : 0 < natProduct n values := by
  induction n with
  | zero => exact Nat.succ_pos 0
  | succ n ih =>
      exact Nat.mul_pos (positive (Fin.last n))
        (ih (fun i => values i.castSucc) (fun i => positive i.castSucc))

/-- Changing the presentation of each factor without changing its value
does not change the common scale. This helper uses only finite recursion. -/
theorem natProduct_congr (n : Nat) (left right : Fin n → Nat)
    (same : ∀ i, left i = right i) : natProduct n left = natProduct n right := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [natProduct]
      rw [same (Fin.last n), ih (fun i => left i.castSucc)
        (fun i => right i.castSucc) (fun i => same i.castSucc)]

/-- Removing a supplied coordinate and multiplying it back restores the
full product. The identity needs no division and therefore preserves zeros
in general natural families; likelihood denominators are positive separately. -/
theorem natProduct_remove (n : Nat) (values : Fin n → Nat) (chosen : Fin n) :
    values chosen * natProduct n (fun i => if i = chosen then 1 else values i) =
      natProduct n values := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      refine Fin.lastCases ?_ (fun earlier => ?_) chosen
      · simp only [natProduct, ite_true, Nat.one_mul]
        congr 1
        apply natProduct_congr
        intro i
        have different : i.castSucc ≠ Fin.last n := by
          intro same
          have coordinate := congrArg Fin.val same
          exact Nat.ne_of_lt i.isLt coordinate
        exact if_neg different
      · change values earlier.castSucc *
          ((if Fin.last n = earlier.castSucc then 1 else values (Fin.last n)) *
            natProduct n (fun i => if i.castSucc = earlier.castSucc then 1
              else values i.castSucc)) =
          values (Fin.last n) * natProduct n (fun i => values i.castSucc)
        have different : Fin.last n ≠ earlier.castSucc := by
          intro same
          have coordinate := congrArg Fin.val same
          exact Nat.ne_of_lt earlier.isLt coordinate.symm
        rw [if_neg different]
        have precedingProduct := natProduct_congr n
          (fun i => if i.castSucc = earlier.castSucc then 1 else values i.castSucc)
          (fun i => if i = earlier then 1 else values i.castSucc)
          (fun i => by simp only [Fin.castSucc_inj])
        rw [precedingProduct]
        calc
          _ = values (Fin.last n) *
              (values earlier.castSucc * natProduct n
                (fun i => if i = earlier then 1 else values i.castSucc)) := by ac_rfl
          _ = _ := by rw [ih (fun i => values i.castSucc) earlier]

/-- Exact natural weights for a tuple of rational likelihoods: atom `i`
receives `num_i * ∏_{j ≠ i} den_j`. -/
def qprobWeights (n : Nat) (like : Fin n → QProb) : Fin n → Nat :=
  fun i =>
    (like i).num * natProduct n (fun j => if j = i then 1 else (like j).den)

/-- Denominator clearing preserves every likelihood with one common scale.
This is the mathematical reason that natural reweighting performs the same
Bayesian update as the supplied rational probabilities; the scale is shared
by every hypothesis, rather than chosen independently for each atom. -/
theorem qprobWeights_represents (n : Nat) (like : Fin n → QProb) (i : Fin n) :
    QProb.Equiv
      ⟨qprobWeights n like i, natProduct n (fun j => (like j).den),
        natProduct_pos n _ (fun j => (like j).den_pos)⟩
      (like i) := by
  change ((like i).num * natProduct n (fun j => if j = i then 1 else (like j).den)) *
      (like i).den = (like i).num * natProduct n (fun j => (like j).den)
  calc
    _ = (like i).num * ((like i).den *
        natProduct n (fun j => if j = i then 1 else (like j).den)) := by ac_rfl
    _ = _ := by rw [natProduct_remove n (fun j => (like j).den) i]

/-- Denominator clearing preserves zero likelihoods exactly: its positive factors
neither create nor remove support. -/
theorem qprobWeights_eq_zero_iff (n : Nat) (like : Fin n → QProb) (i : Fin n) :
    qprobWeights n like i = 0 ↔ (like i).num = 0 := by
  simp only [qprobWeights, Nat.mul_eq_zero]
  constructor
  · intro h
    rcases h with hnum | hprod
    · exact hnum
    · have pos : 0 < natProduct n (fun j => if j = i then 1 else (like j).den) :=
        natProduct_pos n _ (fun j => by
          by_cases same : j = i
          · simp [same]
          · simp [same]
            exact (like j).den_pos)
      exact False.elim (Nat.ne_of_gt pos hprod)
  · intro hnum
    exact Or.inl hnum

/-- Dirichlet–multinomial mass of a count word (Regime B, observed table). -/
def dirichletMultinomialMass (trials : Nat) (alphas : List QProb)
    (positive : 0 < (QProb.listSum alphas).num) (counts : List Nat) : QProb :=
  (rationalDirichletMultinomialDistro trials alphas positive).pmf counts

/-- Probability of the union of the supplied complete-count events.
Duplicate completion entries do not count an event twice. Each completion
is a full count word in the declared parameter alphabet; using this event
as a hidden-data marginal additionally requires that the list contain
exactly the completions of the observed object under every hypothesis.
This constructor does not certify such a coverage claim or impose a hidden
alphabet bound on a larger causal model class. -/
def sumHiddenCompletions (trials : Nat) (alphas : List QProb)
    (positive : 0 < (QProb.listSum alphas).num)
    (completions : List (List Nat)) : QProb :=
  (rationalDirichletMultinomialDistro trials alphas positive).record.probVal
    (fun counts => decide (counts ∈ completions))

/-- Bayes update: reweight the prior by a natural likelihood. `none` when
every atom with positive prior mass has likelihood zero: the catalogue is
exhausted, and no fallback graph is invented. -/
def posterior? (prior : Distro (Fin n)) (weight : Fin n → Nat) :
    Option (Distro (Fin n)) :=
  if h : 0 < natIntegral prior.record.atoms weight then
    some (prior.reweightNat weight h)
  else
    none

/-- `true` when `posterior?` is `none`. The listed hypotheses are exhausted. -/
def catalogueExhausted (prior : Distro (Fin n)) (weight : Fin n → Nat) : Bool :=
  (posterior? prior weight).isNone

/-- A zero likelihood at a label gives zero restricted integral, even when the record
repeats that label. -/
theorem natIntegral_singleton_weight_zero [DecidableEq Ω]
    (atoms : List (Ω × Nat)) (weight : Ω → Nat) (x : Ω) (hx : weight x = 0) :
    natIntegral atoms
      (fun y => if FiniteProbRecord.singletonEvent x y then weight y else 0) = 0 := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [natIntegral]
      by_cases h : atom.1 = x
      · have hit : FiniteProbRecord.singletonEvent x atom.1 = true := by
          simp [FiniteProbRecord.singletonEvent, h]
        simp [h, hx, ih]
      · have miss : FiniteProbRecord.singletonEvent x atom.1 = false := by
          simp [FiniteProbRecord.singletonEvent, h]
        simp [miss, ih]

/-- A zero likelihood kills posterior mass, even when another hypothesis
has positive likelihood and the prior put mass on that other atom. -/
theorem posterior_pmf_zero_of_likelihood_zero [DecidableEq Ω]
    (μ : Distro Ω) (weight : Ω → Nat)
    (positive : 0 < natIntegral μ.record.atoms weight) (x : Ω)
    (hx : weight x = 0) :
    ((μ.reweightNat weight positive).pmf x).num = 0 := by
  have mass :=
    eventMass_reweight μ.record.atoms weight (FiniteProbRecord.singletonEvent x)
  have vanishing := natIntegral_singleton_weight_zero μ.record.atoms weight x hx
  simp only [Distro.pmf, FiniteProbRecord.probVal, Distro.reweightNat,
    ofWeightedAtoms, mass, vanishing]

/-- Likelihood ratio `like_i / like_j` when the latter is positive. -/
def likelihoodRatio (like_i like_j : QProb) : Option QProb :=
  if hj : 0 < like_j.num then some (QProb.div like_i like_j hj) else none

/-- Odds-bounded robustness: if prior odds lie in `[1/C, C]`, posterior
odds lie in `[Λ/C, Λ C]` for Bayes factor `Λ`. This reports that interval
from the likelihood ratio; it does not assume the actual prior odds. -/
def posteriorOddsInterval (C : Nat) (Cpos : 0 < C)
    (like_i like_j : QProb) : Option (QProb × QProb) :=
  match likelihoodRatio like_i like_j with
  | none => none
  | some lr =>
      let bound : QProb := ⟨C, 1, Nat.succ_pos 0⟩
      some (QProb.div lr bound Cpos, QProb.mul lr bound)

/-- Posterior odds are the Bayes factor times the prior odds. -/
theorem posterior_odds_mul (like_i like_j prior_i prior_j : QProb)
    (hj : 0 < like_j.num) (hpj : 0 < prior_j.num) :
    let hpost : 0 < (QProb.mul like_j prior_j).num :=
      Nat.mul_pos hj hpj
    QProb.Equiv
      (QProb.div (QProb.mul like_i prior_i) (QProb.mul like_j prior_j) hpost)
      (QProb.mul (QProb.div like_i like_j hj) (QProb.div prior_i prior_j hpj)) := by
  simp only [QProb.Equiv, QProb.mul, QProb.div]
  ac_rfl

/-- Multiplication on the left preserves cross-multiplication order. -/
theorem mul_le_of_le (factor left right : QProb) (h : QProb.LE left right) :
    QProb.LE (QProb.mul factor left) (QProb.mul factor right) := by
  simp only [QProb.LE, QProb.mul]
  calc
    factor.num * left.num * (factor.den * right.den)
        = (factor.num * factor.den) * (left.num * right.den) := by ac_rfl
    _ ≤ (factor.num * factor.den) * (right.num * left.den) :=
      Nat.mul_le_mul_left _ h
    _ = factor.num * right.num * (factor.den * left.den) := by ac_rfl

/-- If prior odds are at most `C`, posterior odds are at most `Λ C`. -/
theorem posterior_odds_le_scaled (C : Nat) (like_i like_j prior_i prior_j : QProb)
    (hj : 0 < like_j.num) (hpj : 0 < prior_j.num)
    (bounded : QProb.LE (QProb.div prior_i prior_j hpj) ⟨C, 1, Nat.succ_pos 0⟩) :
    QProb.LE
      (QProb.mul (QProb.div like_i like_j hj) (QProb.div prior_i prior_j hpj))
      (QProb.mul (QProb.div like_i like_j hj) ⟨C, 1, Nat.succ_pos 0⟩) :=
  mul_le_of_le _ _ _ bounded

/-- If prior odds are at least `1/C`, posterior odds are at least `Λ/C`. -/
theorem posterior_odds_ge_scaled (C : Nat) (Cpos : 0 < C)
    (like_i like_j prior_i prior_j : QProb)
    (hj : 0 < like_j.num) (hpj : 0 < prior_j.num)
    (bounded : QProb.LE ⟨1, C, Cpos⟩ (QProb.div prior_i prior_j hpj)) :
    QProb.LE
      (QProb.mul (QProb.div like_i like_j hj) ⟨1, C, Cpos⟩)
      (QProb.mul (QProb.div like_i like_j hj) (QProb.div prior_i prior_j hpj)) :=
  mul_le_of_le _ _ _ bounded

/-- Per-template answers distinguish mathematical evidence from a displayed
candidate. An identified formula or bound carries its actual source query,
model-class membership, and local application data. A graph and an arbitrary
input table alone supply none of those application proofs. Such displays stay
`candidate`/`candidateBounds`, even if a graph program printed the formula.
`none` remains undefined and `some 0` remains a supported numerical zero. -/
inductive TemplateAnswer (S : ObservedSignature.{0}) where
  | identified {source : ProbabilityTerm S} {model : ExactModel S}
      {reference : S.Assignment}
      (evidence : CertifiedQuery.FormulaCertificate.At source model reference)
  | bounded {source : ProbabilityTerm S} {model : ExactModel S}
      {reference : S.Assignment}
      (evidence : CertifiedQuery.BoundsCertificate.At source model reference)
  | candidate (formula : ProbabilityTerm S) (value : ProbabilityResult.Result)
  | candidateBounds (lower upper : QProb)
  | unsupported

/-- Presentation-only agreement summary over positive-mass atoms. A point
requires every displayed certified atom to have the same number. The legacy
container is existential in the source query, so this numerical coincidence
alone is not a certificate for one common causal target. Query-indexed
posterior reports in `CatalogueSampling` retain that additional invariant.
Identified disagreement is reported with explicit indices and values. -/
inductive Mixture (S : ObservedSignature) where
  | empty
  | point (value : QProb)
  | disagree (i : Nat) (left : QProb) (j : Nat) (right : QProb)
  | spread (atoms : List (Nat × TemplateAnswer S))

/-- Expose numbers only from applied formula certificates. Candidate values and proposed
intervals remain outside this projection. -/
def TemplateAnswer.identifiedValue {S : ObservedSignature} :
    TemplateAnswer S → Option QProb
  | .identified evidence => evidence.value
  | _ => none

/-- Recognize the actual posterior support, including zeros in unreduced rational presentations. -/
def hasMass (μ : Distro (Fin n)) (i : Fin n) : Bool :=
  decide (0 < (μ.pmf i).num)

/-- First pair of identified positive-mass atoms whose values differ. -/
def firstDisagreement {S : ObservedSignature} :
    List (Fin n) → (Fin n → TemplateAnswer S) →
      Option (Nat × QProb × Nat × QProb)
  | [], _ => none
  | i :: rest, answer =>
      match (answer i).identifiedValue, firstDisagreement rest answer with
      | some _, some d => some d
      | some vi, none =>
          let rec find : List (Fin n) → Option (Nat × QProb × Nat × QProb)
            | [] => none
            | j :: js =>
                match (answer j).identifiedValue with
                | some vj =>
                    if decide (QProb.Equiv vi vj) then find js
                    else some (i.val, vi, j.val, vj)
                | none => find js
          find rest
      | none, d => d

/-- All positive-mass atoms identify to one common rational, if any. -/
def agreedPoint {S : ObservedSignature} :
    List (Fin n) → (Fin n → TemplateAnswer S) → Option QProb
  | [], _ => none
  | i :: rest, answer =>
      match (answer i).identifiedValue with
      | none => none
      | some v =>
          let rec agrees : List (Fin n) → Bool
            | [] => true
            | j :: js =>
                match (answer j).identifiedValue with
                | some w => decide (QProb.Equiv v w) && agrees js
                | none => false
          if agrees rest then some v else none

/-- Summarize positive-mass atoms only. Missing certificates prevent a point summary;
certified disagreement retains witness indices. -/
def mixAnswers (μ : Distro (Fin n)) (answer : Fin n → TemplateAnswer S) :
    Mixture S :=
  let atoms := (List.finRange n).filter (fun i => hasMass μ i)
  match atoms with
  | [] => .empty
  | _ =>
      match firstDisagreement atoms answer with
      | some d => .disagree d.1 d.2.1 d.2.2.1 d.2.2.2
      | none =>
          match agreedPoint atoms answer with
          | some v =>
              if atoms.all (fun i => (answer i).identifiedValue.isSome) then
                .point v
              else
                .spread (atoms.map fun i => (i.val, answer i))
          | none => .spread (atoms.map fun i => (i.val, answer i))

/-- Evaluate an identified observational formula on a supplied table.
Counts data yield `none` unless the caller first builds a predictive law.
Interventional tables are scored as likelihoods, not by running this
action-free term under `do`. -/
def interpretTerm (term : ProbabilityTerm S) (data : CatalogueData S)
    (reference : S.Assignment) : ProbabilityResult.Result :=
  match data with
  | .law record => term.observationalDenote record reference
  | .counts _ _ => none

/-- First observational dataset, including an explicit empty `do`. -/
def firstObservationalData : List (Experiment S) → Option (CatalogueData S)
  | [] => none
  | e :: rest =>
      match e.tag with
      | .observational => some e.data
      | .intervene action =>
          if finAll S.count (fun i => !(action.targets i)) then some e.data
          else firstObservationalData rest

/-- Inspect graph-generated or caller-proposed syntax on an input table.
This is explicitly a candidate/plug-in calculation. Graph-only atoms and
empirical tables cannot manufacture model membership, mechanism restrictions,
or support certificates. In particular an arbitrary `.zero` proposal remains
a candidate and never contributes to a certified point mixture. -/
def candidateAnswerOf (G : ObservedGraph S) (q : JointKernelQuery S)
    (data : CatalogueData S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb))
    (override : Option (ProbabilityTerm S)) : TemplateAnswer S :=
  let outcome : IdentificationOutcome S :=
    match override with
    | some term => .identified term
    | none => identifyJointKernel G q
  match outcome with
  | .identified term => .candidate term (interpretTerm term data reference)
  | .failed _ =>
      match bounds with
      | some ⟨lo, hi⟩ => .candidateBounds lo hi
      | none => .unsupported
  | .unfinished => .unsupported

/-- Public certified formula adapter. The query, concrete model and reference
are carried by the certificate; a bare formula override is not accepted. -/
def answerOf {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment}
    (evidence : CertifiedQuery.FormulaCertificate.At source model reference) :
    TemplateAnswer S :=
  .identified evidence

/-- Public certified interval adapter. Raw endpoints are useful display
candidates, but only a class-wide enclosure with supported application data
can enter this constructor. -/
def boundedAnswerOf {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment}
    (evidence : CertifiedQuery.BoundsCertificate.At source model reference) :
    TemplateAnswer S :=
  .bounded evidence

/-- Candidate computations, including arbitrary proposed expressions, have
no certified value. This small boundary lemma prevents later mixture code
from silently reinterpreting a plug-in calculation as an identified point. -/
theorem candidateAnswerOf_not_certified (G : ObservedGraph S) (q : JointKernelQuery S)
    (data : CatalogueData S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb)) (proposal : Option (ProbabilityTerm S)) :
    (candidateAnswerOf G q data reference bounds proposal).identifiedValue = none := by
  simp only [candidateAnswerOf]
  cases proposal with
  | some term => rfl
  | none =>
    cases identifyJointKernel G q with
    | identified term => rfl
    | failed failure => cases bounds <;> rfl
    | unfinished => rfl

/-- Legacy catalogue display. The per-atom answer keeps its own certificate,
but the existential `TemplateAnswer` does not force all atoms to ask the same
query. New certified inference clients use `CertifiedPosteriorQuery`, whose
type fixes one source query and reference across the complete model family. -/
structure Report (n : Nat) (α : Type u) (S : ObservedSignature) where
  catalogue : Catalogue n α
  posterior : Distro (Fin n)
  likelihood : Fin n → Nat
  answer : Fin n → TemplateAnswer S
  mixture : Mixture S

/-- Read an index's posterior mass separately from its stored likelihood. -/
def Report.mass (R : Report n α S) (i : Fin n) : QProb :=
  R.posterior.pmf i

/-- Display an interval conditional on a supplied prior-odds bound. The report itself
does not establish that bound. -/
def Report.oddsInterval (_R : Report n α S) (C : Nat) (Cpos : 0 < C)
    (i j : Fin n) (like : Fin n → QProb) : Option (QProb × QProb) :=
  posteriorOddsInterval C Cpos (like i) (like j)

/-- Assemble a report from a successful posterior and per-atom answers. -/
def reportOf (catalogue : Catalogue n α) (posterior : Distro (Fin n))
    (likelihood : Fin n → Nat) (answer : Fin n → TemplateAnswer S) :
    Report n α S where
  catalogue := catalogue
  posterior := posterior
  likelihood := likelihood
  answer := answer
  mixture := mixAnswers posterior answer

/-- Layer 1+2 pipeline. `none` when the catalogue is exhausted (likelihood
vanishes on the whole prior support). That is not a unique-graph answer. -/
def infer (catalogue : Catalogue n α) (weight : Fin n → Nat)
    (answer : Fin n → TemplateAnswer S) : Option (Report n α S) :=
  match posterior? catalogue.prior weight with
  | none => none
  | some posterior => some (reportOf catalogue posterior weight answer)

/-- Weighted atoms from parallel label and count lists. -/
def weightedAtoms : List Ω → List Nat → List (Ω × Nat)
  | l :: ls, c :: cs => (l, c) :: weightedAtoms ls cs
  | _, _ => []

/-- Equal-length label and count lists preserve the entire count total, without
discarding a trailing count. -/
theorem totalMass_weightedAtoms (labels : List Ω) (counts : List Nat)
    (hlen : labels.length = counts.length) :
    FiniteProbRecord.totalMass (weightedAtoms labels counts) = counts.sum := by
  induction labels generalizing counts with
  | nil =>
      cases counts with
      | nil => rfl
      | cons _ _ => cases hlen
  | cons _ ls ih =>
      cases counts with
      | nil => cases hlen
      | cons c cs =>
          have tail : ls.length = cs.length := Nat.succ.inj hlen
          simpa [weightedAtoms, FiniteProbRecord.totalMass, List.sum_cons] using
            ih cs tail

/-- Empirical frequencies of observed counts. This is a plug-in statistic,
not a Dirichlet posterior-predictive table: no prior parameters occur here.
Zeros in the count word remain zeros. -/
def empiricalRecordOfCounts (labels : List Ω) (counts : List Nat)
    (hlen : labels.length = counts.length)
    (positive : 0 < counts.sum) : FiniteProbRecord Ω where
  atoms := weightedAtoms labels counts
  den := counts.sum
  den_pos := positive
  total_mass := totalMass_weightedAtoms labels counts hlen

/-- Compatibility spelling for the explicitly empirical constructor. New
statistical code should use `empiricalRecordOfCounts`, and predictive code
should use the actual supported Pólya continuation defined below. -/
abbrev recordOfCounts := @empiricalRecordOfCounts

/-- Whole-law agreement, including zeros. Undefined is not used here:
both records always supply a singleton mass. -/
def recordsAgree (predicted observed : FiniteProbRecord S.Assignment) : Bool :=
  S.assignmentEnumeration.all fun assignment =>
    decide (QProb.Equiv
      (predicted.probVal (FiniteProbRecord.singletonEvent assignment))
      (observed.probVal (FiniteProbRecord.singletonEvent assignment)))

/-- Only an exact-law datum is an exact-law observation. Sample frequencies
are never silently promoted to the true law for a compatibility test. -/
def dataAsRecord : CatalogueData S → Option (FiniteProbRecord S.Assignment)
  | .law record => some record
  | .counts _ _ => none

/-- Predicted table of a realized SCM. Empty `do` is
`HardIntervention.empty`, whose pushforward is the observational law.
Hidden-DAG or table SCMs feed `regimeAWeight` / `regimeBMass` the same
way after computing their `interventionalDist`. -/
def predictedTable (scm : ExactModel S) (tag : ExperimentTag S) :
    FiniteProbRecord S.Assignment :=
  scm.interventionalDist tag.action.value

/-- Regime A: 0/1 whether `predicted` realizes the dataset, zeros included. -/
def regimeAWeight (predicted : FiniteProbRecord S.Assignment)
    (data : CatalogueData S) : Nat :=
  match dataAsRecord data with
  | none => 0
  | some observed => boolWeight (recordsAgree predicted observed)

/-- A finite sample requires a sampling likelihood. It cannot be accepted
or rejected by testing whether its frequencies equal a proposed true law. -/
theorem regimeAWeight_counts (predicted : FiniteProbRecord S.Assignment)
    (labels : List S.Assignment) (bins : List Nat) :
    regimeAWeight predicted (.counts labels bins) = 0 := rfl

/-- Independent Regime A weights of a generative SCM on a list of experiments. -/
def regimeAModelWeight (scm : ExactModel S) (experiments : List (Experiment S)) : Nat :=
  independentWeights (experiments.map fun e =>
    regimeAWeight (predictedTable scm e.tag) e.data)

/-- Predicted singleton masses in `assignmentEnumeration` order. -/
def predictedAlphas (predicted : FiniteProbRecord S.Assignment) : List QProb :=
  S.assignmentEnumeration.map fun assignment =>
    predicted.probVal (FiniteProbRecord.singletonEvent assignment)

/-- Legacy concentration-one Dirichlet/Pólya table prior centred at the
supplied prediction. This is an additional parameter-uncertainty model, not
the IID sampling law of that fixed prediction. Count words follow the full
`S.assignmentEnumeration` order. `CountSamplingLaw` exposes the distinction
explicitly and also records shape and parameter evidence. -/
def regimeBMass (predicted : FiniteProbRecord S.Assignment) (bins : List Nat) : QProb :=
  let alphas := predictedAlphas predicted
  if h : 0 < (QProb.listSum alphas).num then
    dirichletMultinomialMass bins.sum alphas h bins
  else
    QProb.zero

/-- Apply the explicitly extra table prior to one SCM prediction. Separate
uses for different intervention tags do not assert that these priors derive
from a single common structural parameter distribution. Fixed-SCM data use
`iidModelCountLikelihood` instead. -/
def regimeBModelMass (scm : ExactModel S) (tag : ExperimentTag S)
    (bins : List Nat) : QProb :=
  regimeBMass (predictedTable scm tag) bins

/-- Query margin strictly outside `[lo, hi]`. Inside the interval is not
confirmation of a bounds-only atom. -/
def boundsExclude (lo hi value : QProb) : Bool :=
  decide (QProb.LT value lo) || decide (QProb.LT hi value)

/-- Conjunction of a Boolean 0/1 gate with a natural weight. -/
def andWeight (flag : Bool) (weight : Nat) : Nat :=
  boolWeight flag * weight

/-- Conjunction of exact compatibility gates becomes multiplication of zero/one weights. -/
theorem boolWeight_and (b c : Bool) :
    boolWeight (b && c) = boolWeight b * boolWeight c := by
  cases b <;> cases c <;> rfl

/-- A product of compatibility gates accepts exactly when every gate accepts; the empty
list is accepted. -/
theorem mulNatList_map_boolWeight :
    ∀ bs : List Bool,
      mulNatList (bs.map boolWeight) = boolWeight (bs.all fun b => b)
  | [] => rfl
  | b :: rest => by
      simp only [List.map_cons, mulNatList, List.all_cons, boolWeight_and]
      rw [mulNatList_map_boolWeight rest]

/-- Whether this SCM's predicted table realizes one tagged dataset. -/
def experimentAgrees (scm : ExactModel S) (e : Experiment S) : Bool :=
  match dataAsRecord e.data with
  | none => false
  | some observed => recordsAgree (predictedTable scm e.tag) observed

/-- Relate one tagged numerical compatibility weight to its executable exact-law agreement test. -/
theorem regimeAWeight_experimentAgrees (scm : ExactModel S) (e : Experiment S) :
    regimeAWeight (predictedTable scm e.tag) e.data =
      boolWeight (experimentAgrees scm e) := by
  simp only [regimeAWeight, experimentAgrees]
  cases dataAsRecord e.data with
  | none => rfl
  | some _ => rfl

/-- Whole-list Regime A agreement, including zeros, on every experiment. -/
def realizesExperiments (scm : ExactModel S) (experiments : List (Experiment S)) : Bool :=
  experiments.all (experimentAgrees scm)

/-- Simultaneous exact-law compatibility gives a zero/one gate, rather than a
finite-sample likelihood. -/
theorem regimeAModelWeight_eq_realizes (scm : ExactModel S)
    (experiments : List (Experiment S)) :
    regimeAModelWeight scm experiments =
      boolWeight (realizesExperiments scm experiments) := by
  induction experiments with
  | nil => rfl
  | cons e rest ih =>
      simp only [regimeAModelWeight, independentWeights, mulNatList, List.map_cons]
      rw [regimeAWeight_experimentAgrees]
      change boolWeight (experimentAgrees scm e) * regimeAModelWeight scm rest =
        boolWeight (realizesExperiments scm (e :: rest))
      rw [ih, ← boolWeight_and]
      simp [realizesExperiments]

/-- A model realizing every exact-law requirement receives compatibility weight one. -/
theorem regimeAModelWeight_of_realizes (scm : ExactModel S)
    (experiments : List (Experiment S))
    (agree : realizesExperiments scm experiments = true) :
    regimeAModelWeight scm experiments = 1 := by
  simp [regimeAModelWeight_eq_realizes, agree, boolWeight]

/-- Any failed exact-law requirement annihilates the compatibility weight. -/
theorem regimeAModelWeight_of_not_realizes (scm : ExactModel S)
    (experiments : List (Experiment S))
    (disagree : realizesExperiments scm experiments = false) :
    regimeAModelWeight scm experiments = 0 := by
  simp [regimeAModelWeight_eq_realizes, disagree, boolWeight]

/-- The listed generative SCMs are separated by these experiments when
exactly one index realizes every tagged table. Graphs-only atoms are not
this theorem's objects. Markov-equivalent models with the same predicted
tables do not separate. -/
def uniquelyRealizes {n : Nat} (models : Fin n → ExactModel S)
    (experiments : List (Experiment S)) (i : Fin n) : Prop :=
  realizesExperiments (models i) experiments = true ∧
    ∀ j : Fin n, j ≠ i → realizesExperiments (models j) experiments = false

/-- Executable form of `uniquelyRealizes`. -/
def uniquelyRealizesBool {n : Nat} [DecidableEq (Fin n)]
    (models : Fin n → ExactModel S) (experiments : List (Experiment S))
    (i : Fin n) : Bool :=
  realizesExperiments (models i) experiments &&
    (List.finRange n).all fun j =>
      decide (j = i) || !realizesExperiments (models j) experiments

/-- Extract unique-realizer evidence by finite Boolean analysis, without unrestricted
excluded middle. -/
theorem uniquelyRealizes_of_bool {n : Nat} [DecidableEq (Fin n)]
    (models : Fin n → ExactModel S) (experiments : List (Experiment S))
    (i : Fin n) (h : uniquelyRealizesBool models experiments i = true) :
    uniquelyRealizes models experiments i := by
  have parts := Bool.and_eq_true_iff.mp h
  refine ⟨parts.1, ?_⟩
  intro j hne
  have hj : (decide (j = i) ||
      !realizesExperiments (models j) experiments) = true :=
    (List.all_eq_true.mp parts.2) j (List.mem_finRange j)
  have ne : decide (j = i) = false := decide_eq_false hne
  simp [ne] at hj
  cases hr : realizesExperiments (models j) experiments with
  | false => rfl
  | true => simp [hr] at hj

/-- The selected realizer survives exact-law compatibility. -/
theorem uniquelyRealizes_weight_one {n : Nat} (models : Fin n → ExactModel S)
    (experiments : List (Experiment S)) (i : Fin n)
    (h : uniquelyRealizes models experiments i) :
    regimeAModelWeight (models i) experiments = 1 :=
  regimeAModelWeight_of_realizes _ _ h.1

/-- Every competing listed index is excluded. The conclusion concerns the supplied
catalogue only. -/
theorem uniquelyRealizes_weight_zero {n : Nat} (models : Fin n → ExactModel S)
    (experiments : List (Experiment S)) (i j : Fin n)
    (h : uniquelyRealizes models experiments i) (hne : j ≠ i) :
    regimeAModelWeight (models j) experiments = 0 :=
  regimeAModelWeight_of_not_realizes _ _ (h.2 j hne)

/-- Express event mass as an integral of its indicator, preserving repeated atoms and
zero weights. -/
theorem eventMass_eq_natIntegral_indicator (atoms : List (Ω × Nat))
    (event : Event Ω) :
    FiniteProbRecord.eventMass atoms event =
      natIntegral atoms (fun x => if event x then 1 else 0) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [FiniteProbRecord.eventMass, natIntegral]
      cases event atom.1 <;> simp [ih]

/-- The equality event recognizes its supplied label. -/
theorem singletonEvent_self [DecidableEq Ω] (x : Ω) :
    FiniteProbRecord.singletonEvent x x = true := by
  simp [FiniteProbRecord.singletonEvent]

/-- A likelihood is constant on one equality class and factors out of that singleton integral. -/
theorem natIntegral_singleton_mul [DecidableEq Ω]
    (atoms : List (Ω × Nat)) (weight : Ω → Nat) (x : Ω) :
    natIntegral atoms
        (fun y => if FiniteProbRecord.singletonEvent x y then weight y else 0) =
      weight x * FiniteProbRecord.eventMass atoms
        (FiniteProbRecord.singletonEvent x) := by
  induction atoms with
  | nil => simp [natIntegral, FiniteProbRecord.eventMass]
  | cons atom rest ih =>
      simp only [natIntegral, FiniteProbRecord.eventMass]
      by_cases hx : atom.1 = x
      · subst hx
        simp [singletonEvent_self, ih, Nat.mul_add, Nat.mul_comm]
      · have miss : FiniteProbRecord.singletonEvent x atom.1 = false := by
          simp [FiniteProbRecord.singletonEvent, hx]
        simp [miss, ih]

/-- Restricting a nonnegative integral to one label cannot increase it. -/
theorem natIntegral_singleton_le [DecidableEq Ω]
    (atoms : List (Ω × Nat)) (weight : Ω → Nat) (x : Ω) :
    natIntegral atoms
        (fun y => if FiniteProbRecord.singletonEvent x y then weight x else 0) ≤
      natIntegral atoms weight := by
  induction atoms with
  | nil => simp [natIntegral]
  | cons atom rest ih =>
      simp only [natIntegral]
      by_cases hx : atom.1 = x
      · subst hx
        simp [singletonEvent_self]
        exact ih
      · have miss : FiniteProbRecord.singletonEvent x atom.1 = false := by
          simp [FiniteProbRecord.singletonEvent, hx]
        simp [miss]
        exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- One positive-prior, positive-likelihood atom suffices for supported normalization.
Global positivity is unnecessary. -/
theorem natIntegral_pos_of_pmf_pos [DecidableEq Ω]
    (μ : Distro Ω) (weight : Ω → Nat) (x : Ω)
    (hμ : 0 < (μ.pmf x).num) (hw : 0 < weight x) :
    0 < natIntegral μ.record.atoms weight := by
  have mass_pos :
      0 < FiniteProbRecord.eventMass μ.record.atoms
        (FiniteProbRecord.singletonEvent x) := by
    simpa [Distro.pmf, FiniteProbRecord.probVal] using hμ
  have scaled := natIntegral_singleton_mul μ.record.atoms weight x
  have pos_scaled :
      0 < natIntegral μ.record.atoms
        (fun y => if FiniteProbRecord.singletonEvent x y then weight y else 0) :=
    by
      have : 0 < weight x *
          FiniteProbRecord.eventMass μ.record.atoms
            (FiniteProbRecord.singletonEvent x) :=
        Nat.mul_pos hw mass_pos
      simpa [scaled] using this
  have bound := natIntegral_singleton_le μ.record.atoms weight x
  have rewrite :
      natIntegral μ.record.atoms
          (fun y => if FiniteProbRecord.singletonEvent x y then weight y else 0) =
        natIntegral μ.record.atoms
          (fun y => if FiniteProbRecord.singletonEvent x y then weight x else 0) := by
    apply natIntegral_congr
    intro y
    by_cases hy : y = x
    · subst hy
      simp [singletonEvent_self]
    · have miss : FiniteProbRecord.singletonEvent x y = false := by
        simp [FiniteProbRecord.singletonEvent, hy]
      simp [miss]
  exact Nat.lt_of_lt_of_le (rewrite ▸ pos_scaled) bound

/-- An atom survives updating when its prior mass and likelihood are both positive. -/
theorem posterior_pmf_pos_of_likelihood_pos [DecidableEq Ω]
    (μ : Distro Ω) (weight : Ω → Nat)
    (positive : 0 < natIntegral μ.record.atoms weight) (x : Ω)
    (hμ : 0 < (μ.pmf x).num) (hw : 0 < weight x) :
    0 < ((μ.reweightNat weight positive).pmf x).num := by
  have mass :=
    eventMass_reweight μ.record.atoms weight (FiniteProbRecord.singletonEvent x)
  have rewritten := natIntegral_singleton_mul μ.record.atoms weight x
  have mass_pos :
      0 < FiniteProbRecord.eventMass μ.record.atoms
        (FiniteProbRecord.singletonEvent x) := by
    simpa [Distro.pmf, FiniteProbRecord.probVal] using hμ
  simp only [Distro.pmf, FiniteProbRecord.probVal, Distro.reweightNat,
    ofWeightedAtoms, mass, rewritten]
  exact Nat.mul_pos hw mass_pos

/-- If exactly one listed SCM realizes the experiments and the prior puts
mass on that index, the posterior is a point mass there. This is
consistency of a **list**, not uniqueness of a DAG. -/
theorem posterior_of_unique_realizer {n : Nat} [DecidableEq (Fin n)]
    (prior : Distro (Fin n)) (models : Fin n → ExactModel S)
    (experiments : List (Experiment S)) (i : Fin n)
    (separated : uniquelyRealizes models experiments i)
    (prior_pos : 0 < (prior.pmf i).num) :
    catalogueExhausted prior
        (fun j => regimeAModelWeight (models j) experiments) = false ∧
      ∃ μ, posterior? prior
          (fun j => regimeAModelWeight (models j) experiments) = some μ ∧
        0 < (μ.pmf i).num ∧
        ∀ j : Fin n, j ≠ i → (μ.pmf j).num = 0 := by
  have wi : regimeAModelWeight (models i) experiments = 1 :=
    uniquelyRealizes_weight_one models experiments i separated
  have integral_pos :
      0 < natIntegral prior.record.atoms
        (fun j => regimeAModelWeight (models j) experiments) :=
    natIntegral_pos_of_pmf_pos prior
      (fun j => regimeAModelWeight (models j) experiments) i prior_pos
      (by simp [wi])
  have not_exhausted :
      catalogueExhausted prior
        (fun j => regimeAModelWeight (models j) experiments) = false := by
    unfold catalogueExhausted posterior?
    simp [integral_pos]
  refine ⟨not_exhausted, ?_⟩
  refine ⟨prior.reweightNat _ integral_pos, ?_, ?_, ?_⟩
  · unfold posterior?
    simp [integral_pos]
  · exact posterior_pmf_pos_of_likelihood_pos prior _ integral_pos i
      prior_pos (by simp [wi])
  · intro j hne
    have wj : regimeAModelWeight (models j) experiments = 0 :=
      uniquelyRealizes_weight_zero models experiments i j separated hne
    exact posterior_pmf_zero_of_likelihood_zero prior _ integral_pos j wj

/-- Hypothesis-law invariance under a **supplied** assignment map. The map
is data (typically from a coordinate or value permutation); it is not
inferred from the dataset. If the *data* table fails the same test, that
is the caller's record, not this filter. -/
def assignmentLawInvariant (predicted : FiniteProbRecord S.Assignment)
    (σ : S.Assignment → S.Assignment) : Bool :=
  recordsAgree predicted (predicted.map σ)

/-- Regime A on one table, gated by hypothesis invariance. -/
def regimeAInvariantWeight (predicted : FiniteProbRecord S.Assignment)
    (σ : S.Assignment → S.Assignment) (data : CatalogueData S) : Nat :=
  andWeight (assignmentLawInvariant predicted σ) (regimeAWeight predicted data)

/-- Observational predicted law must be invariant; experiments still use
unchanged `regimeAModelWeight`. -/
def regimeAInvariantModelWeight (scm : ExactModel S)
    (σ : S.Assignment → S.Assignment)
    (experiments : List (Experiment S)) : Nat :=
  andWeight
    (assignmentLawInvariant (predictedTable scm .observational) σ)
    (regimeAModelWeight scm experiments)

/-- Directed and bidirected tables are unchanged after relabelling nodes
by a **supplied** node self-map. Directed lives on the signature.
The test supplies no inverse or coherent action; permutation clients use
the typed finite-symmetry interface. -/
def edgesInvariant (n : Nat) (edge : Fin n → Fin n → Bool)
    (perm : Fin n → Fin n) : Bool :=
  finAll n fun i =>
    finAll n fun j => decide (edge i j = edge (perm i) (perm j))

/-- Check both edge tables under a supplied node self-map. This Boolean result does not
prove that the map is a permutation. -/
def observedGraphInvariant (G : ObservedGraph S) (perm : Fin S.count → Fin S.count) :
    Bool :=
  edgesInvariant S.count S.directed perm &&
    edgesInvariant S.count G.bidirected perm

/-- Identity preserves every supplied finite edge table. -/
theorem edgesInvariant_id (n : Nat) (edge : Fin n → Fin n → Bool) :
    edgesInvariant n edge (fun i => i) = true := by
  refine (finAll_eq_true_iff _).mpr ?_
  intro i
  refine (finAll_eq_true_iff _).mpr ?_
  intro j
  simp

/-- Identity preserves the directed and bidirected parts of every graph. -/
theorem observedGraphInvariant_id (G : ObservedGraph S) :
    observedGraphInvariant G (fun i => i) = true := by
  simp [observedGraphInvariant, edgesInvariant_id]

/-- Templates of one hidden DAG share its observed graph, so invariance of
that graph keeps the whole `nativeTemplateCatalogue` and a violating
permutation drops it. This is not graph search. -/
def filterInvariantTemplates (G : ObservedGraph S)
    (perm : Fin S.count → Fin S.count) (templates : List α) : List α :=
  if observedGraphInvariant G perm then templates else []

/-- Identity keeps every template of the fixed graph. -/
theorem filterInvariantTemplates_id (G : ObservedGraph S) (templates : List α) :
    filterInvariantTemplates G (fun i => i) templates = templates := by
  simp [filterInvariantTemplates, observedGraphInvariant_id]

/-- Failure of the fixed-graph gate drops the entire template list, without searching
for another graph. -/
theorem filterInvariantTemplates_not
    (G : ObservedGraph S) (perm : Fin S.count → Fin S.count) (templates : List α)
    (h : observedGraphInvariant G perm = false) :
    filterInvariantTemplates G perm templates = [] := by
  simp [filterInvariantTemplates, h]

/-- Keep those graph-tagged atoms whose observed graph is invariant under
the supplied node self-map. Identity keeps every atom; another map
may keep one graph and drop another. The filter does not prove invertibility
or establish a coherent graph symmetry. -/
def filterInvariantGraphItems (perm : Fin S.count → Fin S.count)
    (items : List (ObservedGraph S × α)) : List (ObservedGraph S × α) :=
  items.filter fun pair => observedGraphInvariant pair.1 perm

/-- Identity keeps every graph-tagged item, including repeated representations. -/
theorem filterInvariantGraphItems_id (items : List (ObservedGraph S × α)) :
    filterInvariantGraphItems (fun i => i) items = items := by
  refine List.filter_eq_self.mpr ?_
  intro pair _
  exact observedGraphInvariant_id pair.1

/-- Retain an item when its graph passes the supplied self-map test. -/
theorem filterInvariantGraphItems_kept (perm : Fin S.count → Fin S.count)
    (G : ObservedGraph S) (item : α) (rest : List (ObservedGraph S × α))
    (h : observedGraphInvariant G perm = true) :
    filterInvariantGraphItems perm ((G, item) :: rest) =
      (G, item) :: filterInvariantGraphItems perm rest := by
  simp [filterInvariantGraphItems, List.filter, h]

/-- Drop an item when its graph fails the supplied self-map test. -/
theorem filterInvariantGraphItems_dropped (perm : Fin S.count → Fin S.count)
    (G : ObservedGraph S) (item : α) (rest : List (ObservedGraph S × α))
    (h : observedGraphInvariant G perm = false) :
    filterInvariantGraphItems perm ((G, item) :: rest) =
      filterInvariantGraphItems perm rest := by
  simp [filterInvariantGraphItems, List.filter, h]

/-- Invariance of this experiment's predicted table, observational or `do`. -/
def experimentInvariant (scm : ExactModel S) (σ : S.Assignment → S.Assignment)
    (e : Experiment S) : Bool :=
  assignmentLawInvariant (predictedTable scm e.tag) σ

/-- Check every experiment with its intervention fixed. This differs from equivariance
when interventions transform too. -/
def experimentsInvariant (scm : ExactModel S) (σ : S.Assignment → S.Assignment)
    (experiments : List (Experiment S)) : Bool :=
  experiments.all (experimentInvariant scm σ)

/-- Regime A on every tagged table, each gated by the same supplied `σ`. -/
def regimeAInvariantExperimentWeight (scm : ExactModel S)
    (σ : S.Assignment → S.Assignment)
    (experiments : List (Experiment S)) : Nat :=
  independentWeights (experiments.map fun e =>
    regimeAInvariantWeight (predictedTable scm e.tag) σ e.data)

/-- Factor experiment-wise gates into compatibility times fixed-experiment invariance.
No coherent group action is inferred. -/
theorem regimeAInvariantExperimentWeight_eq (scm : ExactModel S)
    (σ : S.Assignment → S.Assignment)
    (experiments : List (Experiment S)) :
    regimeAInvariantExperimentWeight scm σ experiments =
      andWeight (experimentsInvariant scm σ experiments)
        (regimeAModelWeight scm experiments) := by
  induction experiments with
  | nil => rfl
  | cons e rest ih =>
      have lhs :
          regimeAInvariantExperimentWeight scm σ (e :: rest) =
            regimeAInvariantWeight (predictedTable scm e.tag) σ e.data *
              regimeAInvariantExperimentWeight scm σ rest :=
        rfl
      have rhs :
          andWeight (experimentsInvariant scm σ (e :: rest))
              (regimeAModelWeight scm (e :: rest)) =
            andWeight (experimentInvariant scm σ e &&
                experimentsInvariant scm σ rest)
              (regimeAWeight (predictedTable scm e.tag) e.data *
                regimeAModelWeight scm rest) :=
        rfl
      rw [lhs, rhs, ih]
      simp only [regimeAInvariantWeight, andWeight, boolWeight_and]
      ac_rfl

/-- Exact singleton agreement is reflexive on the complete observed alphabet. -/
theorem recordsAgree_self (predicted : FiniteProbRecord S.Assignment) :
    recordsAgree predicted predicted = true := by
  refine List.all_eq_true.mpr ?_
  intro assignment _
  exact decide_eq_true (QProb.equiv_refl _)

/-- Whole-law agreement is symmetric despite the orientation of rational cross-multiplication. -/
theorem recordsAgree_comm (p q : FiniteProbRecord S.Assignment) :
    recordsAgree p q = recordsAgree q p := by
  simp only [recordsAgree]
  induction S.assignmentEnumeration with
  | nil => rfl
  | cons assignment rest ih =>
      simp only [List.all_cons, ih]
      have :
          decide (QProb.Equiv
              (p.probVal (FiniteProbRecord.singletonEvent assignment))
              (q.probVal (FiniteProbRecord.singletonEvent assignment))) =
            decide (QProb.Equiv
              (q.probVal (FiniteProbRecord.singletonEvent assignment))
              (p.probVal (FiniteProbRecord.singletonEvent assignment))) := by
        cases h : decide (QProb.Equiv
            (p.probVal (FiniteProbRecord.singletonEvent assignment))
            (q.probVal (FiniteProbRecord.singletonEvent assignment))) with
        | true =>
            exact (decide_eq_true
              (QProb.equiv_symm (of_decide_eq_true h))).symm
        | false =>
            have :
                ¬ QProb.Equiv
                    (q.probVal (FiniteProbRecord.singletonEvent assignment))
                    (p.probVal (FiniteProbRecord.singletonEvent assignment)) :=
              fun same => of_decide_eq_false h (QProb.equiv_symm same)
            exact (decide_eq_false this).symm
      rw [this]

/-- Singleton rational equivalence composes to yield whole-law agreement. -/
theorem recordsAgree_trans (p q r : FiniteProbRecord S.Assignment)
    (hpq : recordsAgree p q = true) (hqr : recordsAgree q r = true) :
    recordsAgree p r = true := by
  refine List.all_eq_true.mpr ?_
  intro assignment hmem
  have hpq_cell := of_decide_eq_true (List.all_eq_true.mp hpq assignment hmem)
  have hqr_cell := of_decide_eq_true (List.all_eq_true.mp hqr assignment hmem)
  exact decide_eq_true (QProb.equiv_trans hpq_cell hqr_cell)

/-- Constructively locate a false member of a failed finite conjunction by list induction. -/
private theorem all_eq_false_mem {α : Type} (p : α → Bool) :
    ∀ xs : List α, xs.all p = false → ∃ x ∈ xs, p x = false
  | [], h => by simp at h
  | x :: xs, h => by
      simp only [List.all_cons, Bool.and_eq_false_iff] at h
      rcases h with hx | hxs
      · exact ⟨x, List.mem_cons_self, hx⟩
      · rcases all_eq_false_mem p xs hxs with ⟨y, hym, hy⟩
        exact ⟨y, List.mem_cons.mpr (Or.inr hym), hy⟩

/-- An agreeing law presentation preserves witnessed disagreement with a third law. -/
theorem recordsAgree_neq_of_unique (p q r : FiniteProbRecord S.Assignment)
    (hpq : recordsAgree p q = true) (hpr : recordsAgree p r = false) :
    recordsAgree q r = false := by
  rcases all_eq_false_mem _ _ hpr with ⟨assignment, hmem, hcell⟩
  have hpq_cell := of_decide_eq_true (List.all_eq_true.mp hpq assignment hmem)
  have npr := of_decide_eq_false hcell
  have nqr : ¬ QProb.Equiv
      (q.probVal (FiniteProbRecord.singletonEvent assignment))
      (r.probVal (FiniteProbRecord.singletonEvent assignment)) :=
    fun qer => npr (QProb.equiv_trans hpq_cell qer)
  have cell_false :
      decide (QProb.Equiv
        (q.probVal (FiniteProbRecord.singletonEvent assignment))
        (r.probVal (FiniteProbRecord.singletonEvent assignment))) = false :=
    decide_eq_false nqr
  cases hall : recordsAgree q r with
  | false => rfl
  | true =>
      exact Bool.noConfusion
        ((List.all_eq_true.mp hall assignment hmem).symm.trans cell_false)

/-- Finite option alphabets: unset, or one enumerated value. -/
def optionValues (S : ObservedSignature) (i : Fin S.count) :
    List (Option (S.Value i)) :=
  none :: (S.valueEnumeration i).map some

/-- Every hard intervention on this finite signature. The list is finite
because each coordinate alphabet is finite. -/
def hardInterventionEnumeration (S : ObservedSignature) :
    List (HardIntervention S) :=
  (FiniteProduct.enumeration S.count (fun i => Option (S.Value i))
    (fun i => optionValues S i)).map fun value => ⟨value⟩

/-- Count exactly the assigned intervention coordinates. -/
def interventionTargetCount (I : HardIntervention S) : Nat :=
  (List.finRange S.count).filter (fun i => (I.value i).isSome) |>.length

/-- Recognize observation by checking that every intervention coordinate is unset. -/
def interventionIsEmpty (I : HardIntervention S) : Bool :=
  finAll S.count fun i => (I.value i).isNone

/-- Observational empty `do`, then every nonempty intervention with at most
`maxTargets` coordinates set. The cap is an input, not an inferred bound. -/
def candidateTags (S : ObservedSignature) (maxTargets : Nat) :
    List (ExperimentTag S) :=
  .observational ::
    ((hardInterventionEnumeration S).filter fun I =>
      !interventionIsEmpty I &&
        decide (interventionTargetCount I ≤ maxTargets)).map
      ExperimentTag.intervene

/-- Compare the full predicted laws of two actual SCMs at one experiment, zeros included. -/
def modelsDisagreeOn {n : Nat} (models : Fin n → ExactModel S)
    (i j : Fin n) (tag : ExperimentTag S) : Bool :=
  !recordsAgree (predictedTable (models i) tag) (predictedTable (models j) tag)

/-- A supplied experiment family separates a pair if at least one predicted full law differs. -/
def pairSeparated {n : Nat} (models : Fin n → ExactModel S)
    (tags : List (ExperimentTag S)) (i j : Fin n) : Bool :=
  tags.any (modelsDisagreeOn models i j)

/-- Require pairwise separation of distinct indices. Repeated equivalent model
representations therefore obstruct separation. -/
def allPairsSeparated {n : Nat} (models : Fin n → ExactModel S)
    (tags : List (ExperimentTag S)) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all fun j =>
      decide (i = j) || pairSeparated models tags i j

/-- Enumerate positional sublists of the requested length. Order is inherited; repeated
candidates remain distinct positional choices. -/
def combinations {α : Type} : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], Nat.succ _ => []
  | x :: rest, Nat.succ k =>
      (combinations rest k).map (fun ys => x :: ys) ++ combinations rest (k + 1)

/-- Every enumerated sublist has the requested size, supplying the measure in the
minimality proof. -/
theorem combinations_length {α : Type} (xs : List α) :
    ∀ k ys, ys ∈ combinations xs k → ys.length = k := by
  induction xs with
  | nil =>
      intro k ys hys
      cases k with
      | zero =>
          simp [combinations] at hys
          cases hys
          rfl
      | succ k =>
          simp [combinations] at hys
  | cons x rest ih =>
      intro k ys hys
      cases k with
      | zero =>
          simp [combinations] at hys
          cases hys
          rfl
      | succ k =>
          simp only [combinations, List.mem_append, List.mem_map] at hys
          rcases hys with ⟨ys', hmem, hcons⟩ | hrest
          · cases hcons
            simp [ih k ys' hmem]
          · exact ih (k + 1) ys hrest

/-- Enumerate all sublists in increasing cardinality, starting with the empty experiment family. -/
def combinationsBySize {α : Type} (xs : List α) : List (List α) :=
  (List.range (xs.length + 1)).flatMap (fun k => combinations xs k)

/-- Isolate all smaller-cardinality candidates from the search suffix. A first success
excludes precisely that prefix. -/
theorem combinationsBySize_split {α : Type} (xs : List α) (k : Nat)
    (hk : k ≤ xs.length + 1) :
    combinationsBySize xs =
      (List.range k).flatMap (combinations xs) ++
        (List.range' k (xs.length + 1 - k)).flatMap (combinations xs) := by
  unfold combinationsBySize
  have hsum : k + (xs.length + 1 - k) = xs.length + 1 :=
    Nat.add_sub_of_le hk
  have hrange :
      List.range (xs.length + 1) =
        List.range k ++ List.range' k (xs.length + 1 - k) := by
    rw [List.range_eq_range' (n := xs.length + 1), List.range_eq_range' (n := k)]
    calc
      List.range' 0 (xs.length + 1) =
          List.range' 0 (k + (xs.length + 1 - k)) := by rw [hsum]
      _ = List.range' 0 k ++ List.range' (0 + k) (xs.length + 1 - k) :=
            (List.range'_append_1 (s := 0) (m := k)
              (n := xs.length + 1 - k)).symm
      _ = List.range' 0 k ++ List.range' k (xs.length + 1 - k) := by
            rw [Nat.zero_add]
  rw [hrange, List.flatMap_append]

/-- Return the first passing member or explicit failure after exhausting the finite list. -/
def firstSatisfying {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else firstSatisfying p xs

/-- Every returned member satisfies the searched Boolean predicate. -/
theorem firstSatisfying_some {α : Type} {p : α → Bool} :
    ∀ xs x, firstSatisfying p xs = some x → p x = true
  | [], _, h => by simp [firstSatisfying] at h
  | x :: xs, y, h => by
      simp only [firstSatisfying] at h
      split at h
      · cases h
        assumption
      · exact firstSatisfying_some xs y h

/-- An exhausted search refutes the predicate for every supplied member. -/
theorem firstSatisfying_none_mem {α : Type} {p : α → Bool} :
    ∀ xs, firstSatisfying p xs = none → ∀ x ∈ xs, p x = false
  | [], _, x, hx => by cases hx
  | y :: ys, h, x, hx => by
      cases hy : p y
      · simp [firstSatisfying, hy] at h
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hy
        · exact firstSatisfying_none_mem ys h x hx
      · simp [firstSatisfying, hy] at h

/-- Searching a concatenation first exhausts its prefix; this traversal law supports
cardinality minimality. -/
theorem firstSatisfying_app {α : Type} (p : α → Bool) :
    ∀ xs ys,
      firstSatisfying p (xs ++ ys) =
        match firstSatisfying p xs with
        | some a => some a
        | none => firstSatisfying p ys
  | [], ys => by simp [firstSatisfying]
  | x :: xs, ys => by
      simp only [List.cons_append, firstSatisfying]
      split <;> simp [firstSatisfying_app p xs ys]

/-- A returned witness belongs to the searched list. No new experiment family is invented. -/
theorem firstSatisfying_mem {α : Type} {p : α → Bool} :
    ∀ xs x, firstSatisfying p xs = some x → x ∈ xs
  | [], _, h => by simp [firstSatisfying] at h
  | y :: ys, x, h => by
      simp only [firstSatisfying] at h
      split at h
      · cases h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (firstSatisfying_mem ys x h)

/-- Shortest sublist of `candidates`, by increasing length, that pairwise
Regime-A-separates the listed SCMs. `none` means some pair agrees on every
searched tag. -/
def shortestSeparatingTags {n : Nat} (models : Fin n → ExactModel S)
    (candidates : List (ExperimentTag S)) : Option (List (ExperimentTag S)) :=
  firstSatisfying (allPairsSeparated models) (combinationsBySize candidates)

/-- A returned experiment family really separates all distinct listed models. -/
theorem shortestSeparatingTags_separated {n : Nat}
    (models : Fin n → ExactModel S)
    (candidates tags : List (ExperimentTag S))
    (h : shortestSeparatingTags models candidates = some tags) :
    allPairsSeparated models tags = true :=
  firstSatisfying_some _ _ h

/-- Check that every candidate sublist of strictly smaller cardinality fails pairwise separation. -/
def noShorterSeparator {n : Nat} (models : Fin n → ExactModel S)
    (candidates : List (ExperimentTag S)) (k : Nat) : Bool :=
  (List.range k).all fun j =>
    (combinations candidates j).all fun tags =>
      !allPairsSeparated models tags

/-- Prove minimal cardinality among sublists of the supplied candidates. Experiments
outside that family are outside the claim. -/
theorem shortestSeparatingTags_minimal {n : Nat}
    (models : Fin n → ExactModel S)
    (candidates tags : List (ExperimentTag S))
    (h : shortestSeparatingTags models candidates = some tags) :
    noShorterSeparator models candidates tags.length = true := by
  have hmem : tags ∈ combinationsBySize candidates :=
    firstSatisfying_mem _ _ h
  rcases List.mem_flatMap.mp hmem with ⟨k, hkRange, hcomb⟩
  have hk : k < candidates.length + 1 := List.mem_range.mp hkRange
  have hlen : tags.length = k := combinations_length _ _ _ hcomb
  have hkLe : k ≤ candidates.length + 1 := Nat.le_of_lt hk
  rw [hlen]
  have hsplit := combinationsBySize_split candidates k hkLe
  have hsearch :
      firstSatisfying (allPairsSeparated models)
        ((List.range k).flatMap (combinations candidates) ++
          (List.range' k (candidates.length + 1 - k)).flatMap
            (combinations candidates)) = some tags := by
    unfold shortestSeparatingTags at h
    rwa [hsplit] at h
  have hnone :
      firstSatisfying (allPairsSeparated models)
        ((List.range k).flatMap (combinations candidates)) = none := by
    cases hp :
        firstSatisfying (allPairsSeparated models)
          ((List.range k).flatMap (combinations candidates)) with
    | none => rfl
    | some z =>
        have heq :
            firstSatisfying (allPairsSeparated models)
              ((List.range k).flatMap (combinations candidates) ++
                (List.range' k (candidates.length + 1 - k)).flatMap
                  (combinations candidates)) = some z := by
          rw [firstSatisfying_app, hp]
        have hz : some tags = some z := hsearch.symm.trans heq
        cases hz
        have hzmem :
            tags ∈ (List.range k).flatMap (combinations candidates) :=
          firstSatisfying_mem _ _ hp
        rcases List.mem_flatMap.mp hzmem with ⟨j, hjRange, hjcomb⟩
        have hj : j < k := List.mem_range.mp hjRange
        have hjlen : tags.length = j := combinations_length _ _ _ hjcomb
        exact absurd (hjlen.symm.trans hlen) (Nat.ne_of_lt hj)
  refine List.all_eq_true.mpr ?_
  intro j hj
  refine List.all_eq_true.mpr ?_
  intro ys hys
  have hysP :
      ys ∈ (List.range k).flatMap (combinations candidates) :=
    List.mem_flatMap.mpr ⟨j, hj, hys⟩
  have hyfalse : allPairsSeparated models ys = false :=
    firstSatisfying_none_mem _ hnone ys hysP
  simp [hyfalse]

/-- The complete list occurs among its full-size positional combinations. -/
theorem mem_combinations_self {α : Type} : ∀ xs : List α, xs ∈ combinations xs xs.length
  | [] => by simp [combinations]
  | x :: rest => by
      change x :: rest ∈ combinations (x :: rest) (rest.length + 1)
      simp only [combinations, List.mem_append, List.mem_map]
      exact Or.inl ⟨rest, mem_combinations_self rest, rfl⟩

/-- The cardinality search includes the complete supplied experiment family. -/
theorem mem_combinationsBySize_self {α : Type} (xs : List α) :
    xs ∈ combinationsBySize xs := by
  refine List.mem_flatMap.mpr ?_
  exact ⟨xs.length, List.mem_range.mpr (Nat.lt_succ_self _), mem_combinations_self xs⟩

/-- Search failure implies the whole supplied family also fails to separate; it cannot
have been omitted. -/
theorem shortestSeparatingTags_none_not_all {n : Nat}
    (models : Fin n → ExactModel S) (candidates : List (ExperimentTag S))
    (h : shortestSeparatingTags models candidates = none) :
    allPairsSeparated models candidates = false :=
  firstSatisfying_none_mem _ h _ (mem_combinationsBySize_self _)

/-- Search distinct index pairs agreeing on all supplied experiments. The result names
catalogue indices, not possible worlds outside the catalogue. -/
def inseparablePair? {n : Nat} (models : Fin n → ExactModel S)
    (candidates : List (ExperimentTag S)) : Option (Fin n × Fin n) :=
  (List.finRange n).findSome? fun i =>
    (List.finRange n).findSome? fun j =>
      if i.val < j.val && !pairSeparated models candidates i j then
        some (i, j)
      else
        none

/-- Experiments whose data tables are this SCM's own predictions. -/
def predictedExperiments (scm : ExactModel S) (tags : List (ExperimentTag S)) :
    List (Experiment S) :=
  tags.map fun tag => ⟨tag, .law (predictedTable scm tag)⟩

/-- A model agrees exactly with its own predicted table for each experiment. -/
theorem experimentAgrees_own (scm : ExactModel S) (tag : ExperimentTag S) :
    experimentAgrees scm ⟨tag, .law (predictedTable scm tag)⟩ = true := by
  simp [experimentAgrees, dataAsRecord, recordsAgree_self]

/-- A model realizes every tagged prediction it generated, including the empty family. -/
theorem realizes_predictedExperiments (scm : ExactModel S)
    (tags : List (ExperimentTag S)) :
    realizesExperiments scm (predictedExperiments scm tags) = true := by
  refine List.all_eq_true.mpr ?_
  intro e he
  rcases List.mem_map.mp he with ⟨tag, _, rfl⟩
  exact experimentAgrees_own scm tag

/-- Exact-law data from one member of a pairwise separated catalogue exclude every other
index. This is finite-list consistency, not global causal discovery. -/
theorem uniquelyRealizes_of_allPairsSeparated {n : Nat}
    (models : Fin n → ExactModel S) (tags : List (ExperimentTag S))
    (i : Fin n) (hsep : allPairsSeparated models tags = true) :
    uniquelyRealizes models (predictedExperiments (models i) tags) i := by
  refine ⟨realizes_predictedExperiments (models i) tags, ?_⟩
  intro j hne
  have pair :
      (decide (i = j) || pairSeparated models tags i j) = true :=
    List.all_eq_true.mp
      (List.all_eq_true.mp hsep i (List.mem_finRange i)) j (List.mem_finRange j)
  have disagrees : pairSeparated models tags i j = true := by
    have : decide (i = j) = false := decide_eq_false hne.symm
    simpa [this] using pair
  cases hall : realizesExperiments (models j) (predictedExperiments (models i) tags) with
  | false => rfl
  | true =>
      rcases List.any_eq_true.mp disagrees with ⟨tag, htag, hdis⟩
      have agrees :
          experimentAgrees (models j)
            ⟨tag, .law (predictedTable (models i) tag)⟩ = true :=
        (List.all_eq_true.mp hall) _ (List.mem_map.mpr ⟨tag, htag, rfl⟩)
      have same :
          recordsAgree (predictedTable (models i) tag)
            (predictedTable (models j) tag) = true := by
        rw [recordsAgree_comm]
        simpa [experimentAgrees, dataAsRecord] using agrees
      have differ :
          recordsAgree (predictedTable (models i) tag)
            (predictedTable (models j) tag) = false := by
        simpa [modelsDisagreeOn] using hdis
      exact Bool.noConfusion (same.symm.trans differ)

end CatalogueInference
end Causality
end Thesis
