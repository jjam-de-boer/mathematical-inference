import Thesis.CausalTransport.InterventionalEntropy
import Thesis.CausalTransport.GraphQueryUncertainty
import Thesis.CausalTransport.ShannonElimination
import Thesis.Probability.Distros.ConditionalInformation

namespace Thesis
namespace Causality

open Probability Probability.Distros

/-!
# What entropy can and cannot do in this development

The probability layer already supplies exact-log Shannon entropy, KL,
grouping, Gibbs, constructive real logarithms and a positive-domain
entropy derivative.  The causal layer now reads those functionals on
observational and interventional assignment records.

This module records the investigation's scope decisions.  Several
nearby projects are possible; only some are useful here.
-/

/-- Three inequivalent entropy projects.  They share vocabulary and must
not be substituted for one another. -/
inductive EntropyProject where
  /-- A finite distribution over candidate causal graphs, measuring
  uncertainty about which graph is correct. -/
  | graphUncertainty
  /-- Coding-theoretic graph entropy of Körner and related structural
  graph invariants. -/
  | structuralGraphEntropy
  /-- Shannon inequalities satisfied by every distribution compatible
  with a fixed causal structure. -/
  | compatibleShannonInequalities

/-- Usefulness for *this* repository, as opposed to mere definability.
`graphUncertainty` is a Bayesian/ID posterior over graphs and stays unused:
ID/IDC still run inside one graph class.  `GraphQueryUncertainty` is the
approved finite-catalogue ranking given data and supplied identifiability;
it is not that posterior and is not a substitute for ID/IDC. -/
def EntropyProject.usefulHere : EntropyProject → Bool
  | .graphUncertainty => false
  | .structuralGraphEntropy => false
  | .compatibleShannonInequalities => true

/-- Graph-uncertainty entropy as a posterior over graphs is not used by
ID/IDC.  The quantity is definable on any finite `Distro` of labels. -/
theorem EntropyProject.graphUncertainty_not_used :
    EntropyProject.graphUncertainty.usefulHere = false := rfl

/-- Körner graph entropy is a coding invariant of an undirected graph with
a distinguished independent-set family.  Causal DAGs here are not that
object, and no encoder of graph colourings is present. -/
theorem EntropyProject.structuralGraphEntropy_not_used :
    EntropyProject.structuralGraphEntropy.usefulHere = false := rfl

/-- Shannon-type inequalities on observable entropies are useful as *sound
exclusion tests*: a violated inequality rejects a candidate structure.
They are not a complete compatibility criterion, even after hidden-variable
elimination.  They cannot reject the native binary-bow class, whose endpoint
models realize every finite rational observed law, and they cannot identify
interventional entropy from an observational law.  This repository already
has sharper complete answers for binary bow and binary IV laws. -/
theorem EntropyProject.compatibleInequalities_used :
    EntropyProject.compatibleShannonInequalities.usefulHere = true := rfl

/-- Selected-coordinate chain rule `H(larger) = H(smaller) + H(larger|smaller)`
is grouping of the canonical forgetful map.  It is not an observed-parent
factorization after hidden vertices are marginalized. -/
theorem selected_entropy_chain_is_grouping {S : ObservedSignature}
    (μ : Distro S.Assignment)
    {smaller larger : NodeSet S} (included : NodeSet.Subset smaller larger) :
    ExactLog.Equiv (selectedEntropy μ larger)
      (ExactLog.add (selectedEntropy μ smaller)
        (selectedConditionalEntropy μ smaller larger)) :=
  selectedEntropy_chain μ included

/-- A supplied Shannon monotonicity claim on selected coordinates.  Checking
is evaluation of the existing entropy functional; it does not search for
inequalities and does not eliminate hidden-variable coordinates. -/
structure ShannonMonotonicityClaim (S : ObservedSignature) where
  smaller : NodeSet S
  larger : NodeSet S
  included : NodeSet.Subset smaller larger

def ShannonMonotonicityClaim.holds (claim : ShannonMonotonicityClaim S)
    (μ : Distro S.Assignment) : Prop :=
  ExactLog.LE (selectedEntropy μ claim.smaller) (selectedEntropy μ claim.larger)

/-- Selected-coordinate monotonicity is a theorem, not a searched inequality. -/
theorem ShannonMonotonicityClaim.verified (claim : ShannonMonotonicityClaim S)
    (μ : Distro S.Assignment) : claim.holds μ :=
  selectedEntropy_mono μ claim.included

/-- Submodularity as a supplied certificate: checking is evaluation.  Hidden
variable elimination of the elemental cone is sound and incomplete. -/
structure ShannonSubmodularityClaim (S : ObservedSignature) where
  first : NodeSet S
  second : NodeSet S

def ShannonSubmodularityClaim.holds (claim : ShannonSubmodularityClaim S)
    (μ : Distro S.Assignment) : Prop :=
  ExactLog.LE
    (ExactLog.add (selectedEntropy μ (NodeSet.union claim.first claim.second))
      (selectedEntropy μ (NodeSet.inter claim.first claim.second)))
    (ExactLog.add (selectedEntropy μ claim.first) (selectedEntropy μ claim.second))

instance (claim : ShannonSubmodularityClaim S) (μ : Distro S.Assignment) :
    Decidable (claim.holds μ) :=
  inferInstanceAs (Decidable (ExactLog.LE _ _))

/-- Entropic CI as an information identity.  `I(X;Y|Z) = 0` is equivalent
to `H(XZ)+H(YZ)-H(XYZ) = H(Z)`.  The identity is sound for d-separation on
the full DAG; it is not automatically an identity of observed-parent
conditionals after hidden vertices are marginalized. -/
def conditionalIndependenceIdentity
    (entropyXZ entropyYZ entropyXYZ entropyZ : ExactLog) : Prop :=
  ExactLog.Equiv (mutualInformation entropyXZ entropyYZ entropyXYZ) entropyZ

/-- Existing KL on a declared grid requires a strictly positive reference
mass at every cell, including cells of zero observed mass.  A Janzing
disruption whose post-cutting law has extra zeros is therefore outside
the current `relativeEntropy` interface; that is an infinite KL, not a
missing rational value. -/
theorem relativeEntropy_requires_positive_reference
    [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) :
    ExactLog.LE ExactLog.zero
      (μ.relativeEntropy reference grid support referenceSupport positive) :=
  μ.relativeEntropy_nonnegative reference grid support referenceSupport positive

/-- Entropy message passing needs the entropy-semiring pair `(mass, mass · H)`,
not a list of node entropies.  Exactness holds on cycle-free factor graphs.
After hidden-variable projection, the observed factor graph need not be a
tree, and the existing evaluator already computes finite-grid entropy by
direct summation. -/
inductive EntropyComputationMethod where
  | exactFiniteGrid
  | groupingIdentities
  | entropyMessagePassingOnTrees
  | loopyMessagePassing

def EntropyComputationMethod.exactHere : EntropyComputationMethod → Bool
  | .exactFiniteGrid => true
  | .groupingIdentities => true
  | .entropyMessagePassingOnTrees => false
  | .loopyMessagePassing => false

theorem EntropyComputationMethod.tree_passing_not_exact_for_arbitrary_graphs :
    EntropyComputationMethod.entropyMessagePassingOnTrees.exactHere = false := rfl

/-- The existing constructive derivative of `-p log₂ p` is proved on every
positive part of `[0,1]`, not at zero and not through SCM mechanisms.
Rational causal weights are unchanged by that auxiliary calculus. -/
structure EntropyBackpropStatus where
  positiveDomainDerivative : Bool
  derivativeAtZero : Bool
  mechanismJacobian : Bool
  rationalSimplexAttainment : Bool

def entropyBackpropStatus : EntropyBackpropStatus where
  positiveDomainDerivative := true
  derivativeAtZero := false
  mechanismJacobian := false
  rationalSimplexAttainment := false

theorem entropyBackpropStatus.no_mechanism_jacobian :
    entropyBackpropStatus.mechanismJacobian = false := rfl

theorem entropyBackpropStatus.no_derivative_at_zero :
    entropyBackpropStatus.derivativeAtZero = false := rfl

theorem entropyBackpropStatus.no_rational_simplex_attainment :
    entropyBackpropStatus.rationalSimplexAttainment = false := rfl

/-- The constructive first variation of `-p log₂ p` is proved on every
positive part of `[0,1]`.  It is not a Jacobian through SCM mechanisms, and a
rational moment polytope need not contain a rational maximiser. -/
theorem entropy_objective_has_positive_domain_derivative :
    entropyBackpropStatus.positiveDomainDerivative = true := rfl

/-- Hidden-variable Fourier–Motzkin on the elemental Shannon cone is available
and incomplete. -/
theorem hidden_variable_elimination_incomplete :
    hiddenVariableEliminationComplete = false :=
  hiddenVariableEliminationComplete_false

end Causality
end Thesis
