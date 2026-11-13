import Thesis.Causality.SelectedEntropy
import Thesis.Probability.Distros.ConditionalInformation
import Thesis.Probability.Distros.UncertaintyMeasure

namespace Thesis
namespace Causality

open Probability Probability.Distros

/-!
# Remaining query uncertainty across a finite catalogue of graph hypotheses

Given observational data, competing graphs are compared by (i) whether the
data violate independencies the graph asserts, and (ii) whether the graph
identifies the query.  The Shannon entropy of the uniform law on the
data-compatible hypotheses is uncertainty about which remaining graph is
right.  Restricting further to hypotheses that identify the query is the
suitability ranking: a graph that fits the data but leaves the query
unidentified is less suited than one that both fits and identifies.

This is not a Bayesian posterior on graphs, and it does not run ID/IDC.
Identifiability is a supplied hypothesis, as in a certificate.  Rejecting a
graph because a claimed CI identity fails is sound; surviving the test is
not a proof that the graph is correct.
-/

variable {S : ObservedSignature}

/-- `I(left; right | cond) = 0` as an entropy identity on selected coordinates. -/
def conditionalMutualZero (μ : Distro S.Assignment)
    (left right cond : NodeSet S) : Prop :=
  ExactLog.Equiv
    (mutualInformation
      (selectedEntropy μ (NodeSet.union left cond))
      (selectedEntropy μ (NodeSet.union right cond))
      (selectedEntropy μ (NodeSet.union (NodeSet.union left right) cond)))
    (selectedEntropy μ cond)

instance (μ : Distro S.Assignment) (left right cond : NodeSet S) :
    Decidable (conditionalMutualZero μ left right cond) :=
  inferInstanceAs (Decidable (ExactLog.Equiv _ _))

theorem conditionalMutualZero_iff_vanishing
    (μ : Distro S.Assignment) (left right cond : NodeSet S) :
    conditionalMutualZero μ left right cond ↔
      ExactLog.Equiv (selectedConditionalMutualInformation μ left right cond)
        ExactLog.zero :=
  (ExactLog.sub_equiv_zero_iff _ _).symm

/-- One competing Markov reading of the same observed coordinates. -/
structure QueryGraphCandidate (S : ObservedSignature) where
  independencies : List (NodeSet S × NodeSet S × NodeSet S)
  identifiesQuery : Bool

def QueryGraphCandidate.compatible (candidate : QueryGraphCandidate S)
    (μ : Distro S.Assignment) : Bool :=
  candidate.independencies.all fun triple =>
    decide (conditionalMutualZero μ triple.1 triple.2.1 triple.2.2)

def QueryGraphCandidate.suited (candidate : QueryGraphCandidate S)
    (μ : Distro S.Assignment) : Bool :=
  candidate.compatible μ && candidate.identifiesQuery

/-- Shannon entropy of the uniform law on a nonempty finite remainder. -/
def finiteCatalogueEntropy : Nat → Option ExactLog
  | 0 => none
  | n + 1 => some (ProbabilityVector.uniform (n + 1) (Nat.succ_pos n)).entropy

/-- Uncertainty about which data-compatible graph remains.  Empty remainder
means every supplied hypothesis is excluded by the data. -/
def graphUncertaintyEntropy (candidates : List (QueryGraphCandidate S))
    (μ : Distro S.Assignment) : Option ExactLog :=
  finiteCatalogueEntropy (candidates.filter (fun candidate => candidate.compatible μ)).length

/-- Remaining uncertainty after keeping only hypotheses that both fit the
data and identify the query. -/
def querySuitabilityEntropy (candidates : List (QueryGraphCandidate S))
    (μ : Distro S.Assignment) : Option ExactLog :=
  finiteCatalogueEntropy (candidates.filter (fun candidate => candidate.suited μ)).length

theorem finiteCatalogueEntropy_singleton :
    ∃ value, finiteCatalogueEntropy 1 = some value ∧ ExactLog.Equiv value ExactLog.zero := by
  refine ⟨_, rfl, ?_⟩
  simpa using ProbabilityVector.uniform_entropy 1 (by decide)

theorem finiteCatalogueEntropy_pair :
    ∃ value, finiteCatalogueEntropy 2 = some value ∧
      ExactLog.Equiv value (ExactLog.log (PositiveRatio.ofNat 2 (by decide))) := by
  refine ⟨_, rfl, ?_⟩
  exact ProbabilityVector.uniform_entropy 2 (by decide)

/-- A singleton remainder has no graph uncertainty. -/
theorem graphUncertainty_of_unique_compatible (candidates : List (QueryGraphCandidate S))
    (μ : Distro S.Assignment)
    (unique : (candidates.filter (fun candidate => candidate.compatible μ)).length = 1) :
    ∃ value, graphUncertaintyEntropy candidates μ = some value ∧
      ExactLog.Equiv value ExactLog.zero := by
  unfold graphUncertaintyEntropy
  rw [unique]
  exact finiteCatalogueEntropy_singleton

end Causality
end Thesis
