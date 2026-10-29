import Thesis.Examples.FiniteEnsembleFitting
import Thesis.Examples.EntropyMeanHalfDiscriminant
import Thesis.Examples.UniformEntropyPaths
import Thesis.Examples.GibbsDegeneracy
import Thesis.Examples.FiniteStatisticalMechanics
import Thesis.Examples.GibbsPartition
import Thesis.Examples.AnalyticLinear
import Thesis.Examples.EntropyKKT
import Thesis.Examples.EntropySupportFace
import Thesis.Examples.AnalyticGibbs
import Thesis.Examples.EntropyGibbsForm
import Thesis.Examples.EntropyMultipliers
import Thesis.Examples.EntropyStationarity
import Thesis.Examples.RationalEntropyOptimizer
import Thesis.Examples.ConstructiveEntropyOptimizer
import Thesis.Examples.ConstructiveEntropyCurvature
import Thesis.Examples.ConstructiveEntropyDerivative
import Thesis.Examples.RationalConstraintDensity
import Thesis.Examples.ConstructiveRealFeasibility
import Thesis.Examples.ConstructiveRealEntropy
import Thesis.Examples.ConstructiveLogExp
import Thesis.Examples.ConstructiveExpAddition
import Thesis.Examples.ConstructiveLogDerivative
import Thesis.Examples.RationalLogVariation
import Thesis.Examples.UncertaintyMeasure
import Thesis.Examples.EntropyMeanHalf
import Thesis.Examples.LogLinearEntropy
import Thesis.Examples.EntropyOptimize
import Thesis.Examples.EntropyContinuity
import Thesis.Examples.EntropyMoments
import Thesis.Examples.EntropySmallMass
import Thesis.Examples.EntropyConcavity
import Thesis.Examples.EntropyBounds
import Thesis.Examples.EntropyGibbsEquality
import Thesis.Examples.EntropyGibbs
import Thesis.Examples.FiniteAMGM
import Thesis.Examples.Entropy
import Thesis.Examples.ExactLog
import Thesis.Examples.ConditionalReadoutFailure
import Thesis.Examples.ConditionalReadoutPaths
import Thesis.Examples.DistributionLaws
import Thesis.Examples.DistributionExtensions
import Thesis.Examples.DistroRealization
import Thesis.Examples.DistroPartialMoments
import Thesis.Examples.DistroRanks
import Thesis.Examples.BooleanChannelExpansion
import Thesis.Examples.FiniteProductBalance
import Thesis.Examples.PairRootChannels
import Thesis.Examples.LocalCheckBaseline
import Thesis.Examples.LocalCheckImports
import Thesis.Examples.LocalCheckCoreImports
import Thesis.Examples.LocalCheckDefinition
import Thesis.Examples.LocalCheckRetainedDependency
import Thesis.Examples.LocalCheckFiniteDecision
import Thesis.Examples.PositiveModal
import Thesis.Examples.SupportedModal

/-!
# Extra regressions owned by the axiom-policy gate

These files are not imported by the ordinary `Thesis` facade.  Importing a
library lemma does not elaborate a separate test module, so the collection
gate pulls them in here.  Their expanded-graph and local-check proofs can
need more kernel memory than a capped single-module check; they still belong
inside the same `propext` / `Quot.sound` policy.

Constructive entropy/exact-log example files that are not imported by
`Thesis.lean` are listed here so they remain in the collection gate.
-/
