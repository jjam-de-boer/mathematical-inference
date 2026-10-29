import Thesis.Probability.RationalThirteenSquareObstruction
import Thesis.Probability.FiniteGrandThermodynamicIdentification
import Thesis.Probability.FinitePhysicalDegeneracy
import Thesis.Probability.ConstructivePotentialUniqueness
import Thesis.Probability.FiniteStatisticalEntropy
import Thesis.Probability.ConstructiveRealFittedGibbsCertificates
import Thesis.Probability.ConstructiveRealFaceKKT
import Thesis.Probability.ConstructiveRealFarkas
import Thesis.Probability.ConstructiveRealEntropyVariational
import Thesis.Probability.ConstructiveRealFaceMultipliers
import Thesis.Probability.ConstructiveRealEntropyInterior
import Thesis.Probability.ConstructiveRealEntropyGlobalOptimality
import Thesis.Probability.ConstructiveRealLogLinearOptimality
import Thesis.Probability.ConstructiveRealEntropyGibbsForm
import Thesis.Probability.ConstructiveRealEntropyMultipliers
import Thesis.Probability.ConstructiveRealEntropyStationarity
import Thesis.Probability.ConstructiveRealRationalEntropyOptimizer
import Thesis.Probability.ConstructiveRealEntropyOptimizer
import Thesis.Probability.ConstructiveRealEntropyStrongConcavityClosed
import Thesis.Probability.ConstructiveRealEntropyDerivative
import Thesis.Probability.ConstructiveRealRationalConstraints
import Thesis.Probability.ConstructiveRealEntropyCertificates
import Thesis.Probability.ConstructiveRealEntropySum
import Thesis.Probability.ConstructiveRealRelativeEntropy
import Thesis.Probability.ConstructiveRealLogInverse
import Thesis.Probability.ConstructiveRealExpPositive
import Thesis.Probability.ConstructiveRealLogGeneralDerivative
import Thesis.Probability.RationalLogVariation
import Thesis.Probability.ConstructiveRealInverseDerivative
import Thesis.Probability.ConstructiveDerivativeProduct
import Thesis.Probability.ConstructiveDerivativeChain
import Thesis.Probability.ConstructiveDerivativeUniqueness
import Thesis.Probability.ConstructiveRealExpDerivative
import Thesis.Probability.ConstructiveDerivativeAlgebra
import Thesis.Probability.RationalExponentialVariation
import Thesis.Probability.ConstructiveRealExpLimits
import Thesis.Probability.ConstructiveRealExponential
import Thesis.Probability.RationalExponential
import Thesis.Probability.RationalTaylorExponential
import Thesis.Probability.ConstructiveRealLogReciprocal
import Thesis.Probability.ConstructiveRealLogOrder
import Thesis.Probability.ConstructiveRealReciprocal
import Thesis.Probability.ConstructiveRealProductLimits
import Thesis.Probability.ConstructiveRealOrderedRing
import Thesis.Probability.ConstructiveRealCauchyOrder
import Thesis.Probability.EntropyRealProducts
import Thesis.Probability.ConstructiveRealCauchy
import Thesis.Probability.ConstructiveRealRing
import Thesis.Probability.ConstructiveRealMultiplication
import Thesis.Probability.RationalNorm
import Thesis.Probability.ConstructiveRealLimits
import Thesis.Probability.EntropyInterpretation
import Thesis.Probability.EntropyTermBounds
import Thesis.Probability.FiniteAMGM
import Thesis.Probability.ExactLogEnclosure
import Thesis.Probability.Core
import Thesis.Probability.FiniteProbabilityValueEscape
import Thesis.Probability.RationalSquareObstruction
import Thesis.Probability.IndependentBooleanObstruction
import Thesis.Probability.Combinatorics
import Thesis.Probability.ConstructivePermutation
import Thesis.Probability.Reindexing
import Thesis.Probability.FiniteCellProduct
import Thesis.Probability.Urn
import Thesis.Probability.QualitativeUrn
import Thesis.Probability.FiniteRecord
import Thesis.Probability.FiniteRecordSupport
import Thesis.Probability.FiniteRecordPresentation
import Thesis.Probability.FiniteProductPresentation
import Thesis.Probability.FiniteEnumerationBounds
import Thesis.Probability.FiniteFunctionTables
import Thesis.Probability.FiniteRecordAlmostSure
import Thesis.Probability.FiniteRecordConsistencyBounds
import Thesis.Probability.AffineInterval
import Thesis.Probability.RationalMixture
import Thesis.Probability.FiniteProductReindex
import Thesis.Probability.FiniteProductSplicing
import Thesis.Probability.FiniteProductSourceCompression
import Thesis.Probability.FiniteProbabilityPolynomialCertificates
import Thesis.Probability.FiniteRecordSlicing
import Thesis.Probability.FiniteRecordCatalogue
import Thesis.Probability.FiniteSupportCatalogue
import Thesis.Probability.FiniteProductSupportLaw
import Thesis.Probability.FiniteRecordPerturbation
import Thesis.Probability.FiniteLinearResponse
import Thesis.Probability.FiniteSignedMass
import Thesis.Probability.FiniteConditionalContrast
import Thesis.Probability.FiniteConditionalContrastPreservation
import Thesis.Probability.FiniteSignedProduct
import Thesis.Probability.FiniteProductBlocks
import Thesis.Probability.FinitePowerProduct
import Thesis.Probability.FiniteUniformProduct
import Thesis.Probability.FiniteProductSupport
import Thesis.Probability.FiniteSupportedSum
import Thesis.Probability.FiniteBooleanCharacter
import Thesis.Probability.FiniteBooleanBlocks
import Thesis.Probability.FiniteBooleanTranslation
import Thesis.Probability.FiniteBooleanInteraction
import Thesis.Probability.FiniteBooleanBasis
import Thesis.Probability.FiniteBooleanCovariance
import Thesis.Probability.FiniteBooleanCylinderCovariance
import Thesis.Probability.FiniteRatioPerturbation
import Thesis.Probability.ConditionalUniqueness
import Thesis.Probability.FiniteProductConditionals
import Thesis.Probability.BooleanNoise
import Thesis.Probability.BooleanChannelTable
import Thesis.Probability.BooleanChannelExpansion
import Thesis.Probability.BooleanChannelReserve
import Thesis.Probability.ConditionalNoise
import Thesis.Probability.ColliderChannel
import Thesis.Probability.ColliderRealization
import Thesis.Probability.Construction
import Thesis.Probability.FiniteProductResponse
import Thesis.Probability.FiniteProductAllocation
import Thesis.Probability.FiniteProductGrouping
import Thesis.Probability.FiniteProductBalance
import Thesis.Probability.Distros

/-!
# Finite constructive probability and auxiliary analytic values

This facade reexports the public probability development. Implementations
should import focused owners; detailed hypotheses and proof explanations
remain beside their declarations.

## Records, events and independent products

Start with `Core`, `Urn`, `QualitativeUrn` and `FiniteRecord`: Boolean
events, rational arithmetic, finite counting, weighted laws and supported
conditioning. Records allow repeated labels and zero weights on arbitrary
ambient outcome types. `FiniteRecordPresentation` distinguishes sampling
codes from a declared observable domain retaining null values.

`Construction` and the `FiniteProduct*` modules construct actual independent
product laws, reindex assignments and group independent source blocks.
Their compression results preserve the stated finite target family and
independence structure.

## Distributions, information and finite constraints

`Distros.Record` owns the general distribution and relabelling interface;
`Distros.Basic` adds natural-valued moments and generating functions.
`Distros.LawBasics` supplies law equality and almost-sure support without
those numeric dependencies. Named distribution families and their sampling,
moment and concentration results live below `Distros`.

`ExactLog`, `EntropyValue` and `Distros.Entropy` provide exact finite
information values and inequalities. `Distros.PartialMomentProblem`,
`Distros.RationalLinearSolve` and `Distros.EntropyOptimize` own the finite
constraint and certified optimization interfaces, with their explicit
feasibility and approximation hypotheses.

`Distros.UncertaintyCharacterization` derives Shannon entropy from explicit
rational representation, permutation, null-outcome, grouping, uniform-order
and fair-bit requirements. The implemented entropy inhabits that specification.
Selecting the maximum is a further inference principle: it selects the
admissible law with greatest uncertainty, rather than following from grouping
consistency alone. The analytic optimization results prove the consequences
of that selection, including constructive existence, uniqueness, exact feasible
rational approximation, multiplier fitting, signed interval KKT and forced-zero
face handling.

`FinitePhysicalModel` and `FinitePhysicalEnsembles` treat declared microstates
as physical modeling data. `FinitePhysicalDegeneracy` counts their actual fibers
and proves the entropy correction for grouped Gibbs laws; repeated record atoms
remain presentation choices. Statistical physical entropy is kB*ln(2)*H_bits.
The closed/open thermodynamic-identification theorems compare it with an
independent entropy satisfying a uniform Clausius law on explicitly admitted
positive affine paths, under equilibrium and temperature calibration. They fix
the additive constant by a reference convention and do not establish empirical
adequacy or arbitrary-path connectivity. `EntropyMeanHalfDiscriminant` in the
examples connects the original rational certificates to an attained irrational
ideal law, its constructed multipliers and the exclusion of a rational maximum.

## Finite algebra and analytic values

`Reindexing`, `FiniteBoolean*`, `BooleanChannel*` and the response/balance
modules supply finite sum, product and character identities for causal
countermodels. `FiniteProbabilityPolynomialCertificates` checks supplied
rational bounds against actual independent-source probabilities.
`FiniteConditionalContrast` expresses supported conditional agreement as a
zero integer mean and treats null evidence separately.
`FiniteConditionalContrastPreservation` transports its vanishing across records
with matching evidence and joint-event probabilities.
`RationalSquareObstruction` and `IndependentBooleanObstruction` retain
the checked fixed-mechanism rational obstruction and its precise scope.

The `ConstructiveReal*` modules develop auxiliary arithmetic, limits,
logarithms, exponentials, differentiation and entropy with explicit error
control. Their finite-constraint and certificate bridges state their domains
locally. Causal probability records retain finite rational weights.
`Distros.ConditionalInformation` names the grouping remainder as
conditional entropy and records Shannon monotonicity of two-stage
refinement; mutual information is `H(X)+H(Y)-H(X,Y)` from those values.
-/
