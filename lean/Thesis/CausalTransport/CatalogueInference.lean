import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ObservationalEvaluation
import Thesis.Causality.HardIntervention
import Thesis.Probability.Distros.Categorical
import Thesis.Probability.Distros.Reweight
import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.Distros.Moments
import Thesis.Probability.QProbOrder

namespace Thesis
namespace Causality
namespace CatalogueInference

open Probability Probability.Distros Probability.Combinatorics

/-!
# Bayesian posterior on a finite catalogue, with kernel ID or bounds

Layer 1 places a `Distro` prior on a finite list of hypotheses and updates
it by supported reweighting. Layer 2 reuses `identifyJointKernel` and the
existing bound solvers; it does not reimplement ID and does not rank graphs
by Shannon inequalities or mutual information.

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
not confirm the atom. Regime B is Dirichlet–multinomial / Pólya on that
table, with hypothesis-specific predicted cell masses when the atom is not
the saturated joint.

Independent experiments multiply natural weights. If every positive-prior
atom then has likelihood 0, `posterior?` / `infer` return `none` and the
mixture is `empty`: the catalogue is **exhausted**, not replaced by a
silent fallback graph. Complexity scores belong only as prior weights.

A finite list of mutually disagreeing generative SCMs is **separated** by
those experiments: Regime A is then a point mass on the unique realizer,
not a unique DAG of the world. A supplied assignment permutation may be
ANDed into Regime A as an invariance constraint on the **hypothesis**
(not inferred from data, not PC). `nativeTemplateCatalogue` may be
filtered by a supplied node permutation of the host observed graph;
templates of one hidden DAG share that graph, so the filter is
all-or-nothing.

Defined-zero and undefined formula values stay distinct. No `0/0`
completion. Identified formulas remain action-free observational terms
evaluated on observational tables. Interventional scoring is likelihood,
not a second ID engine. Graph-query Shannon entropy remains a separate
diagnostic.
-/

variable {α : Type} {S : ObservedSignature.{0}}

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

def observationalExperiment (data : CatalogueData S) : Experiment S :=
  ⟨.observational, data⟩

def interveneExperiment (action : HardIntervention S) (data : CatalogueData S) :
    Experiment S :=
  ⟨.intervene action, data⟩

/-- The action used to generate a predictive table. Empty `do` is
`HardIntervention.empty`. -/
def ExperimentTag.action : ExperimentTag S → HardIntervention S
  | .observational => HardIntervention.empty S
  | .intervene action => action

/-- Finite labelled catalogue with a categorical prior on its indices. -/
structure Catalogue (n : Nat) (α : Type) where
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

def independentWeights (perExperiment : List Nat) : Nat :=
  mulNatList perExperiment

/-- Product of independent rational masses (Regime B across experiments). -/
def mulQProbList : List QProb → QProb
  | [] => QProb.one
  | w :: rest => QProb.mul w (mulQProbList rest)

def independentQProb (masses : List QProb) : QProb :=
  mulQProbList masses

/-- Product of natural coordinates, used to clear rational likelihood dens. -/
def natProduct : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 1
  | n + 1, values =>
      values (Fin.last n) * natProduct n (fun i => values i.castSucc)

theorem natProduct_pos (n : Nat) (values : Fin n → Nat)
    (positive : ∀ i, 0 < values i) : 0 < natProduct n values := by
  induction n with
  | zero => exact Nat.succ_pos 0
  | succ n ih =>
      exact Nat.mul_pos (positive (Fin.last n))
        (ih (fun i => values i.castSucc) (fun i => positive i.castSucc))

/-- Exact natural weights for a tuple of rational likelihoods: atom `i`
receives `num_i * ∏_{j ≠ i} den_j`. -/
def qprobWeights (n : Nat) (like : Fin n → QProb) : Fin n → Nat :=
  fun i =>
    (like i).num * natProduct n (fun j => if j = i then 1 else (like j).den)

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

/-- Sum Dirichlet–multinomial masses over a bounded list of hidden count
tables. Each completion is a full (observed+hidden) word; the caller
enumerates only assignments inside the stated alphabet bound. -/
def sumHiddenCompletions (trials : Nat) (alphas : List QProb)
    (positive : 0 < (QProb.listSum alphas).num)
    (completions : List (List Nat)) : QProb :=
  QProb.listSum (completions.map (dirichletMultinomialMass trials alphas positive))

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

/-- Per-template Layer 2 answer. `identified` keeps the action-free formula
and its partial value (`none` is undefined, `some 0` is defined zero). -/
inductive TemplateAnswer (S : ObservedSignature) where
  | identified (formula : ProbabilityTerm S) (value : ProbabilityResult.Result)
  | bounded (lower upper : QProb)
  | unsupported

/-- Mixture over positive-mass atoms. A point requires every such atom to
identify and agree. Identified disagreement is reported with witnesses. -/
inductive Mixture (S : ObservedSignature) where
  | empty
  | point (value : QProb)
  | disagree (i : Nat) (left : QProb) (j : Nat) (right : QProb)
  | spread (atoms : List (Nat × TemplateAnswer S))

def TemplateAnswer.identifiedValue {S : ObservedSignature} :
    TemplateAnswer S → Option QProb
  | .identified _ (some value) => some value
  | _ => none

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

/-- Layer 2: ID on the hypothesis graph, optional formula override (for
mechanism restrictions on a shared host signature), and optional bounds
when ID fails. Adjustment set `Z` is whatever the existing engine printed;
modifier set `W` is not inferred here. -/
def answerOf (G : ObservedGraph S) (q : JointKernelQuery S)
    (data : CatalogueData S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb))
    (override : Option (ProbabilityTerm S)) : TemplateAnswer S :=
  let outcome : IdentificationOutcome S :=
    match override with
    | some term => .identified term
    | none => identifyJointKernel G q
  match outcome with
  | .identified term => .identified term (interpretTerm term data reference)
  | .failed _ =>
      match bounds with
      | some ⟨lo, hi⟩ => .bounded lo hi
      | none => .unsupported
  | .unfinished => .unsupported

structure Report (n : Nat) (α : Type) (S : ObservedSignature) where
  catalogue : Catalogue n α
  posterior : Distro (Fin n)
  likelihood : Fin n → Nat
  answer : Fin n → TemplateAnswer S
  mixture : Mixture S

def Report.mass (R : Report n α S) (i : Fin n) : QProb :=
  R.posterior.pmf i

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

/-- Posterior-predictive table from counts, for interpreting identified
formulas in Regime B. Zeros in the count word remain zeros. -/
def recordOfCounts (labels : List Ω) (counts : List Nat)
    (hlen : labels.length = counts.length)
    (positive : 0 < counts.sum) : FiniteProbRecord Ω where
  atoms := weightedAtoms labels counts
  den := counts.sum
  den_pos := positive
  total_mass := totalMass_weightedAtoms labels counts hlen

/-- Whole-law agreement, including zeros. Undefined is not used here:
both records always supply a singleton mass. -/
def recordsAgree (predicted observed : FiniteProbRecord S.Assignment) : Bool :=
  S.assignmentEnumeration.all fun assignment =>
    decide (QProb.Equiv
      (predicted.probVal (FiniteProbRecord.singletonEvent assignment))
      (observed.probVal (FiniteProbRecord.singletonEvent assignment)))

def dataAsRecord : CatalogueData S → Option (FiniteProbRecord S.Assignment)
  | .law record => some record
  | .counts labels bins =>
      if hlen : labels.length = bins.length then
        if hpos : 0 < bins.sum then
          some (recordOfCounts labels bins hlen hpos)
        else none
      else none

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

/-- Independent Regime A weights of a generative SCM on a list of experiments. -/
def regimeAModelWeight (scm : ExactModel S) (experiments : List (Experiment S)) : Nat :=
  independentWeights (experiments.map fun e =>
    regimeAWeight (predictedTable scm e.tag) e.data)

/-- Predicted singleton masses in `assignmentEnumeration` order. -/
def predictedAlphas (predicted : FiniteProbRecord S.Assignment) : List QProb :=
  S.assignmentEnumeration.map fun assignment =>
    predicted.probVal (FiniteProbRecord.singletonEvent assignment)

/-- Regime B: Dirichlet–multinomial using the atom's predicted cell masses.
Count words should follow `S.assignmentEnumeration` order. -/
def regimeBMass (predicted : FiniteProbRecord S.Assignment) (bins : List Nat) : QProb :=
  let alphas := predictedAlphas predicted
  if h : 0 < (QProb.listSum alphas).num then
    dirichletMultinomialMass bins.sum alphas h bins
  else
    QProb.zero

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

theorem boolWeight_and (b c : Bool) :
    boolWeight (b && c) = boolWeight b * boolWeight c := by
  cases b <;> cases c <;> rfl

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

theorem regimeAModelWeight_of_realizes (scm : ExactModel S)
    (experiments : List (Experiment S))
    (agree : realizesExperiments scm experiments = true) :
    regimeAModelWeight scm experiments = 1 := by
  simp [regimeAModelWeight_eq_realizes, agree, boolWeight]

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

theorem uniquelyRealizes_weight_one {n : Nat} (models : Fin n → ExactModel S)
    (experiments : List (Experiment S)) (i : Fin n)
    (h : uniquelyRealizes models experiments i) :
    regimeAModelWeight (models i) experiments = 1 :=
  regimeAModelWeight_of_realizes _ _ h.1

theorem uniquelyRealizes_weight_zero {n : Nat} (models : Fin n → ExactModel S)
    (experiments : List (Experiment S)) (i j : Fin n)
    (h : uniquelyRealizes models experiments i) (hne : j ≠ i) :
    regimeAModelWeight (models j) experiments = 0 :=
  regimeAModelWeight_of_not_realizes _ _ (h.2 j hne)

theorem eventMass_eq_natIntegral_indicator (atoms : List (Ω × Nat))
    (event : Event Ω) :
    FiniteProbRecord.eventMass atoms event =
      natIntegral atoms (fun x => if event x then 1 else 0) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [FiniteProbRecord.eventMass, natIntegral]
      cases event atom.1 <;> simp [ih]

theorem singletonEvent_self [DecidableEq Ω] (x : Ω) :
    FiniteProbRecord.singletonEvent x x = true := by
  simp [FiniteProbRecord.singletonEvent]

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
by a **supplied** permutation. Directed lives on the signature. -/
def edgesInvariant (n : Nat) (edge : Fin n → Fin n → Bool)
    (perm : Fin n → Fin n) : Bool :=
  finAll n fun i =>
    finAll n fun j => decide (edge i j = edge (perm i) (perm j))

def observedGraphInvariant (G : ObservedGraph S) (perm : Fin S.count → Fin S.count) :
    Bool :=
  edgesInvariant S.count S.directed perm &&
    edgesInvariant S.count G.bidirected perm

theorem edgesInvariant_id (n : Nat) (edge : Fin n → Fin n → Bool) :
    edgesInvariant n edge (fun i => i) = true := by
  refine (finAll_eq_true_iff _).mpr ?_
  intro i
  refine (finAll_eq_true_iff _).mpr ?_
  intro j
  simp

theorem observedGraphInvariant_id (G : ObservedGraph S) :
    observedGraphInvariant G (fun i => i) = true := by
  simp [observedGraphInvariant, edgesInvariant_id]

/-- Templates of one hidden DAG share its observed graph, so invariance of
that graph keeps the whole `nativeTemplateCatalogue` and a violating
permutation drops it. This is not graph search. -/
def filterInvariantTemplates (G : ObservedGraph S)
    (perm : Fin S.count → Fin S.count) (templates : List α) : List α :=
  if observedGraphInvariant G perm then templates else []

theorem filterInvariantTemplates_id (G : ObservedGraph S) (templates : List α) :
    filterInvariantTemplates G (fun i => i) templates = templates := by
  simp [filterInvariantTemplates, observedGraphInvariant_id]

theorem filterInvariantTemplates_not
    (G : ObservedGraph S) (perm : Fin S.count → Fin S.count) (templates : List α)
    (h : observedGraphInvariant G perm = false) :
    filterInvariantTemplates G perm templates = [] := by
  simp [filterInvariantTemplates, h]

end CatalogueInference
end Causality
end Thesis
