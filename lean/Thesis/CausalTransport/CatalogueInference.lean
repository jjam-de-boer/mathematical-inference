import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ObservationalEvaluation
import Thesis.Probability.Distros.Categorical
import Thesis.Probability.Distros.Reweight
import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.QProbOrder

namespace Thesis
namespace Causality
namespace CatalogueInference

open Probability Probability.Distros Probability.Combinatorics

/-!
# Bayesian posterior on a finite catalogue, with certified ID or bounds

Layer 1 places a `Distro` prior on a finite list of hypotheses and updates
it by supported reweighting. Layer 2 reuses `identifyJointKernel` and the
existing bound solvers; it does not reimplement ID and does not rank graphs
by Shannon inequalities or mutual information.

Hypotheses are caller-declared, or any already enumerated finite list
including `nativeTemplateCatalogue` at explicit node/source bounds. Templates
of one hidden DAG share that DAG's observed graph, so Layer 2 is constant
on such a list; Regime A/B still distinguish mechanism shapes.

Regime A is a 0/1 whole-law likelihood: whether the hypothesis realizes the
supplied observational record, including zeros. Regime B is Dirichlet–
multinomial / Pólya on a table. The v1 default is the **observed** assignment
table (caller-supplied Dirichlet parameters). Summing bounded hidden
assignments is the same compound law on caller-enumerated hidden count
tables; wiring `CodeNativeTemplate` source tables to those completions is
the remaining native-template generalization.

Defined-zero and undefined formula values stay distinct. No `0/0`
completion. Graph-query Shannon entropy remains a separate diagnostic.
-/

variable {α : Type} {S : ObservedSignature.{0}}

/-- Observational input for a catalogue update. -/
inductive CatalogueData (S : ObservedSignature) where
  | law (record : FiniteProbRecord S.Assignment)
  | counts (labels : List S.Assignment) (bins : List Nat)

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
every atom with positive prior mass has likelihood zero. -/
def posterior? (prior : Distro (Fin n)) (weight : Fin n → Nat) :
    Option (Distro (Fin n)) :=
  if h : 0 < natIntegral prior.record.atoms weight then
    some (prior.reweightNat weight h)
  else
    none

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
Counts data yield `none` unless the caller first builds a predictive law. -/
def interpretTerm (term : ProbabilityTerm S) (data : CatalogueData S)
    (reference : S.Assignment) : ProbabilityResult.Result :=
  match data with
  | .law record => term.observationalDenote record reference
  | .counts _ _ => none

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

/-- Layer 1+2 pipeline. Fails only when the likelihood vanishes on the
whole prior support. -/
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

end CatalogueInference
end Causality
end Thesis
