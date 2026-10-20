import Thesis.Probability.Distros.Basic
import Thesis.Probability.Distros.FinitePresentation
import Thesis.Probability.Distros.Bernoulli
import Thesis.Probability.Distros.Categorical
import Thesis.Probability.Distros.Binomial
import Thesis.Probability.Distros.Multinomial
import Thesis.Probability.Distros.Sampling
import Thesis.Probability.Distros.LimitAnalogs
import Thesis.Probability.Distros.Gaussian
import Thesis.Probability.Distros.WaitingTime
import Thesis.Probability.Distros.BernoulliWaiting
import Thesis.Probability.Distros.BernoulliRace
import Thesis.Probability.Distros.Moments
import Thesis.Probability.Distros.Concentration
import Thesis.Probability.Distros.LawEquivalence
import Thesis.Probability.Distros.PointMass
import Thesis.Probability.Distros.FinCap
import Thesis.Probability.Distros.IndependentSums
import Thesis.Probability.Distros.ChiSquared
import Thesis.Probability.Distros.GaussianMoments
import Thesis.Probability.Distros.BetaBinomial
import Thesis.Probability.Distros.MultivariatePGF
import Thesis.Probability.Distros.PGFUniqueness
import Thesis.Probability.Distros.CategoricalProduct
import Thesis.Probability.Distros.MultinomialAggregation
import Thesis.Probability.Distros.MultinomialCovariance
import Thesis.Probability.Distros.BinomialMoments
import Thesis.Probability.Distros.BetaBinomialMoments
import Thesis.Probability.Distros.GeometricMoments
import Thesis.Probability.Distros.HypergeometricMoments
import Thesis.Probability.Distros.FactorialMoments
import Thesis.Probability.Distros.FactorialPGF
import Thesis.Probability.Distros.BinomialInversion
import Thesis.Probability.Distros.FactorialInversion
import Thesis.Probability.Distros.MomentTableAlgebra
import Thesis.Probability.Distros.ProbabilityGrid
import Thesis.Probability.Distros.FinitePmfExpectation
import Thesis.Probability.Distros.FactorialMomentTable
import Thesis.Probability.Distros.FactorialMomentRealization
import Thesis.Probability.Distros.MomentTableCheck
import Thesis.Probability.Distros.MultivariateFactorialInversion
import Thesis.Probability.Distros.FactorialRectangle
import Thesis.Probability.Distros.ProbabilityList
import Thesis.Probability.Distros.JointMomentTableAlgebra
import Thesis.Probability.Distros.JointMomentTable
import Thesis.Probability.Distros.JointMomentRealization
import Thesis.Probability.Distros.JointMomentTableCheck
import Thesis.Probability.Distros.MultivariateFactorialPGF
import Thesis.Probability.Distros.MultivariateReconstruction
import Thesis.Probability.Distros.PositiveSupport
import Thesis.Probability.Distros.HighestFactorialMoments
import Thesis.Probability.Distros.PositiveReconstruction
import Thesis.Probability.Distros.PolyaUpdates
import Thesis.Probability.Distros.Degenerate
import Thesis.Probability.Distros.NegativeBinomialMoments
import Thesis.Probability.Distros.CapConsistency
import Thesis.Probability.Distros.HypergeometricUrn
import Thesis.Probability.Distros.MultivariateHypergeometric
import Thesis.Probability.Distros.HypergeometricFactorialMoments
import Thesis.Probability.Distros.HypergeometricMarginals
import Thesis.Probability.Distros.HypergeometricAggregation
import Thesis.Probability.Distros.DepletingUrn
import Thesis.Probability.Distros.DepletingHistory
import Thesis.Probability.Distros.DepletingWord
import Thesis.Probability.Distros.DepletingConditioning
import Thesis.Probability.Distros.DepletingPrefix
import Thesis.Probability.Distros.DepletingConsistency
import Thesis.Probability.Distros.DepletingSupport
import Thesis.Probability.Distros.DepletingAggregation
import Thesis.Probability.Distros.DepletingAggregationConditioning
import Thesis.Probability.Distros.Reweight
import Thesis.Probability.Distros.MulticolourPolya
import Thesis.Probability.Distros.KernelInvariance
import Thesis.Probability.Distros.SignedCovariance
import Thesis.Probability.Distros.SignedCauchy
import Thesis.Probability.Distros.RationalMoments
import Thesis.Probability.Distros.RationalClearing
import Thesis.Probability.Distros.RationalCovarianceAlgebra
import Thesis.Probability.Distros.FiniteCovariance
import Thesis.Probability.Distros.OccupancyCovariance
import Thesis.Probability.Distros.HypergeometricCovariance
import Thesis.Probability.Distros.OccupancyDegenerate
import Thesis.Probability.Distros.OccupancyCovarianceEntries
import Thesis.Probability.Distros.OccupancyNullspace
import Thesis.Probability.Distros.RationalConcentration
import Thesis.Probability.Distros.RationalMarkov
import Thesis.Probability.Distros.RationalChebyshev
import Thesis.Probability.Distros.ConditionalMoments
import Thesis.Probability.Distros.ConditionalObservable
import Thesis.Probability.Distros.ConditionalTower
import Thesis.Probability.Distros.ConditionalAlgebra
import Thesis.Probability.Distros.ConditionalProjection
import Thesis.Probability.Distros.ProjectionEquality
import Thesis.Probability.Distros.RefinementGain
import Thesis.Probability.Distros.AlmostSureTower
import Thesis.Probability.Distros.ObservationChains
import Thesis.Probability.Distros.RationalLinearOrder
import Thesis.Probability.Distros.RationalIntervalCheck
import Thesis.Probability.Distros.RationalLinearInequalities
import Thesis.Probability.Distros.RationalLinearProjection
import Thesis.Probability.Distros.RationalLinearSolve
import Thesis.Probability.Distros.RationalLinearBounds
import Thesis.Probability.Distros.FiniteGridMoments
import Thesis.Probability.Distros.RationalLinearObjective
import Thesis.Probability.Distros.RationalSimplex
import Thesis.Probability.Distros.RationalMassGrid
import Thesis.Probability.Distros.PartialMomentProblem
import Thesis.Probability.Distros.PartialMomentBounds
import Thesis.Probability.Distros.CovarianceRows
import Thesis.Probability.Distros.RationalVectorSpace
import Thesis.Probability.Distros.RationalCoordinateBasis
import Thesis.Probability.Distros.RationalKernelBasis
import Thesis.Probability.Distros.CovarianceOperator
import Thesis.Probability.Distros.OccupancyRank
import Thesis.Probability.Distros.OccupancyRankDegenerate
import Thesis.Probability.Distros.ReinforcedUrn
import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.Distros.RationalBetaBinomial
import Thesis.Probability.Distros.RationalUpdates
import Thesis.Probability.Distros.JointFactorialMoments
import Thesis.Probability.Distros.ReinforcedAggregation
import Thesis.Probability.Distros.ReinforcedMoments
import Thesis.Probability.Distros.ReinforcedVariance
import Thesis.Probability.Distros.ReinforcedUpdates
import Thesis.Probability.Distros.ReinforcedPrefix

/-!
Named finite distros.

Reading order:

`FinitePresentation` supplies weighted finite sampling codes and a separate
duplicate-free declared-domain adapter. Its decoding theorems preserve all
events and supported conditionals without a unit-cell denominator expansion.
Sampling codes do not redefine observed values, and declared null values are
retained rather than silently excluded as nonpositive support.

1. `Basic` defines `Distro` / `NatDistro`, outcome relabelling (including
   composition, sections, and the identity map), moments, PGF, Markov,
   Chebyshev, Fin-supported weight packaging, and the slotwise Cauchy
   product for independent Fin-supported sums, packaged both as event masses
   and as PMFs;
2. `Bernoulli` is the two-cell generating atom, with mean, whole-number
   PGF, and PGF at a general nonnegative rational, identified with the
   one-trial binomial along `false ↦ 0` and `true ↦ 1`;
3. `Categorical` is the finite labelled urn, with discrete uniform as the
   equal-weight case;
4. `Binomial` derives the success-count law from independent Bernoulli
   trials, records the closed binomial weights, identifies the two
   presentations as events and as PMFs, records the closed mean, evaluates
   the PGF at whole-number arguments and at a general nonnegative rational,
   and identifies the independent sum of equal-weight binomials with the
   binomial of the summed trial count, and identifies the one-trial case
   with the Bernoulli distro mapped along `bernoulliBit` and back along
   `bernoulliOfBit`, including the round-trip sections;
5. `Multinomial` is the occupancy-count law of independent categorical
   draws, with singleton occupancy PMFs under `multinomialWeight` and
   event mass that splits as a binomial mixture over the first coordinate;
6. `Sampling` records hypergeometric (without-replacement) and truncated
   geometric waiting-time distros, together with a right-censored geometric
   that lumps leftover mass onto the last cell.  Hypergeometric event
   probabilities are selected-weight sums against the Vandermonde total, and
   the marked-count PGF is the homogenised Vandermonde generating polynomial.
   Truncated and censored geometric PGFs are recorded at whole-number
   arguments and at a general nonnegative rational.  Their integer weights
   retain the common Bernoulli trial denominator;
7. `LimitAnalogs` records the lattice Gaussian with rational kernel
   `q^(k²)` for `0 ≤ q ≤ 1`, the
   de Moivre binomial special case, χ² as a sum of `df` centred squares,
   and the Pólya / truncated-gamma counterparts.  The lattice Gaussian mean
   is the window centre by reflection symmetry.  The truncated negative
   binomial has PGFs as ratios of `nbSumHomog` generating sums, at
   whole-number arguments and at a general nonnegative rational, and a
   right-censored sibling with the tail on the same trial denominator.
8. `Gaussian` verifies the cleared-denominator kernel, proves decreasing
   weights with increasing squared distance, identifies the zero-base point
   mass and the unit-base discrete uniform law, and retains the shifted mean.
9. `WaitingTime` identifies the truncated and censored one-success negative
   binomial with geometric as actual distributions and numeric embeddings,
   with event, PMF and general rational PGF consequences.
10. `BernoulliWaiting` computes first-success occupancy on the actual finite
    independent Bernoulli product, identifies its censored geometric
    pushforward on every Boolean event, and obtains the truncated law by
    conditioning that same record on success in the window.
11. `BernoulliRace` stops the actual Bernoulli product at either a success
    or failure threshold.  Its ordinary and terminal occupancies give the
    corrected NB weights and tail, exhaust the fixed trial horizon, and
    agree with both the truncated and censored NB laws on every event.
12. `Moments` supplies natural and rational expectation, transport under maps,
    linearity, independent means and variances, and rational PGF factorisation.
    `Concentration` connects cleared squared deviations to variance and proves
    Chebyshev at positive rational radii.  `LawEquivalence` transports laws
    through maps, products, positive conditioning, expectations, moments,
    variance and PGFs, independently of atom presentations.
13. `IndependentSums` regroups repeated independent sums as actual records
    and proves their moment scaling and PGF power laws.
14. `ChiSquared` applies regrouping to the squared-coordinate construction:
    equal radius and kernel give additivity of degrees of freedom on every event.
15. `GaussianMoments` proves zero signed centred mean and exact finite kernel
    sums for Gaussian variance and the second/fourth moments needed for χ².
16. `BetaBinomial` proves rising-factorial Vandermonde and the closed denominator,
    constructs reinforced Pólya colour paths from sequential Bernoulli urn draws,
    identifies their success-count pushforward on every event, and gives the mean.
17. `MultivariatePGF` proves occupancy dimensions and trial totals, the
    rational multivariate multinomial generating function, and its natural
    argument specialization via a reusable rational binomial theorem.
18. `BinomialMoments` proves Bernoulli and binomial second moments and closed
    variances, including zero trials and deterministic Bernoulli parameters.
19. `BetaBinomialMoments` proves the second factorial moment and closed
    reinforced-urn variance, with zero trials included.
20. `GeometricMoments` uses finite summation by parts to prove closed means,
    second moments and witnessed variances for the corrected truncated and
    censored waiting times.  All formulas include zero cap and zero failure weight.
21. `HypergeometricMoments` derives the first and second factorial moments
    by absorption and Vandermonde, proves the finite-population mean and variance,
    and handles empty and one-cell urns explicitly.
22. `FactorialMoments` generalizes the binomial, hypergeometric and beta-binomial
    falling-factorial moments to every order, including orders above support.
23. `PolyaUpdates` proves word permutation invariance and the exact
    reinforced continuation law after conditioning on a supported prefix,
    with both next-colour predictive probabilities.
24. `PointMass` recognizes one-cell laws and transports their mean, variance
    and PGF. `Degenerate` supplies positive-total constructors for censored
    waiting times and beta-binomial, including deterministic endpoints and
    the general reinforced-urn correspondence.
25. `NegativeBinomialMoments` gives all-order factorial moments as shifted
    finite generating sums and closed means, second moments and witnessed
    variances for truncated and censored laws, including zero cap and the
    censored zero-success-weight endpoint.
26. `FinCap` gives reusable finite-window conditioning and censoring laws.
    `CapConsistency` applies them to truncated and right-censored geometric
    and NB families, including zero success weight in the censored laws.
27. `HypergeometricUrn` realizes sampling without replacement by sequential
    Bernoulli colour draws and removal. Its marked-count pushforward agrees
    with hypergeometric on every event, and its mean and finite-population
    variance follow by law transport.
28. `PGFUniqueness` proves that generating functions determine finite numeric
    laws and bounded count-vector laws, using unique natural coefficients
    and a constructive positional decoding section.
29. `CategoricalProduct` constructs ordered independent categorical draws
    using the existing product operation. Reading off their occupancy vector
    gives the multinomial law on every Boolean event.
30. `MultinomialAggregation` proves arbitrary category coarsening, binomial
    coordinate marginals, and their closed means and witnessed variances.
31. `SignedMoments` gives covariance an integer numerator and identifies it
    with the centered product integral and the existing diagonal variance.
    `MultinomialCovariance` proves the distinct-coordinate cross moment and
    nonpositive covariance, including zero trials and zero-weight colours.
32. `Reweight` transports positive natural likelihood reweighting through
    equality of laws and maps. `MulticolourPolya` constructs sequential
    categorical reinforcement and the Dirichlet-multinomial count law,
    proves their event correspondence and rising-total normalization, and
    recovers beta-binomial for two colours, including zero-colour endpoints.
33. `KernelInvariance` proves that equivalent rational Gaussian kernel
    presentations give the same law, and transports this to finite χ².
34. `SignedCovariance` supplies signed expectation, symmetric bilinear
    covariance, law/map transport, independence and the dependent-sum
    variance law. Integer observables have nonnegative rational variance,
    with a proof of agreement with the existing witnessed Nat variance.
35. `StepRising` and `ReinforcedUrn` allow any natural reinforcement increment,
    with exact sequential categorical semantics, count law and closed
    normalizer. Zero increment recovers multinomial and one recovers Pólya.
    Scaling initial counts and increment together preserves every event law.
36. `RationalPolya` clears a common denominator to implement arbitrary
    nonnegative rational Pólya parameters. Its count law, parameter
    representation invariance and agreement with the natural-parameter
    constructors are proved, including zero individual parameters.
37. `FactorialConvolution` gives all-order coefficient absorption and
    generalized rising-factorial Vandermonde. `JointFactorialMoments`
    proves every mixed falling-factorial moment for multinomial,
    Dirichlet-multinomial and arbitrary reinforcement, with zero colours,
    orders above finite support and rational parameters included.
38. `CategoricalAggregation` and `ReinforcedAggregation` prove category
    merging for actual reinforced paths and their count laws at every
    increment. Dirichlet-multinomial coordinates have beta-binomial
    marginals and the corresponding closed means and variances.
39. `ReinforcedMoments` extracts individual factorial moments, means,
    cross moments and nonpositive signed covariances from the mixed-order
    formula, including arbitrary increments and zero selected parameters.
40. `ReinforcedHistory` identifies the updated state from counts and
    splits actual sequential paths. `ReinforcedExchangeability` proves
    word probabilities and permutation invariance for arbitrary colours.
41. `ReinforcedConditioning` conditions the actual path record on observed
    counts and proves its future law is exactly the updated urn, making
    counts sufficient. `ReinforcedUpdates` gives count support and the
    closed next-colour predictive probability at every increment.
42. `ReinforcedPrefix` proves ordered-prefix conditioning, its predictive
    probability, and direct equality in law with conditioning only on the
    observed counts, including supported deterministic prefixes.
43. `RationalParameters` identifies every positive-reinforcement integer urn
    with rational parameters divided by that reinforcement. `RationalAggregation`,
    `RationalBetaBinomial` and `RationalUpdates` expose rational category sums,
    coordinate beta-binomial marginals, and actual count-conditioned future
    path and count laws with parameters increased by the observed counts.
44. `ReinforcedVariance` gives the closed coordinate variance at every natural
    reinforcement, including zero trials, zero weights and zero reinforcement.
45. `SignedConcentration` and `SignedCauchy` prove rational-radius Chebyshev
    for integer observables, zero variance exactly for almost-sure constants,
    and covariance Cauchy–Schwarz including the zero-variance cases.
46. `FactorialPGF` expands a bounded numeric PGF about one using its factorial
    moments divided by factorials. Matching moments through a common finite
    support bound reconstructs every event probability and every rational PGF.
47. `RationalMoments` provides signed rational-observable expectation,
    covariance and variance, with linearity and integer-expectation agreement.
    These are the observable types needed for conditional moment decompositions.
48. `ConditionalPartitions` constructs exhaustive finite evidence partitions
    from the actual atom records, retaining unsupported cells with explicit
    zero conditional values. `ConditionalMoments` proves total expectation,
    variance and covariance for signed rational observables and conditional means.
    Integer and natural-observable variance agree with the existing interfaces.
49. `MultivariateHypergeometric` constructs multicolour sampling without
    replacement and proves its Vandermonde normalization. Its factorial-moment
    modules give all joint moments, including vanishing orders, and reconstruct
    the hypergeometric law of each coordinate. `HypergeometricAggregation`
    proves arbitrary category coarsening with summed stocks and empty groups.
50. `RationalClearing` transports signed rational moments through laws and maps
    and proves variance nonnegativity by finite-support denominator clearing.
    `RationalConcentration` gives rational covariance Cauchy–Schwarz and the
    almost-sure zero-variance characterization, respecting unreduced values.
    `RationalMarkov` and `RationalChebyshev` handle rational observables and
    thresholds, with genuine centered-square variance and exact deviation events.
51. `ConditionalObservable` partitions actual atoms by finite-valued observables,
    defines their conditional-mean observables and proves residual orthogonality.
    `ConditionalTower` gives explicit refinement and tower laws, including
    unsupported fibres, and actual-record equality for nested supported evidence.
52. `DepletingUrn` constructs actual categorical removal paths and identifies
    their occupancy law with multivariate hypergeometric sampling. Its history
    and word modules prove no-overdraw bounds and stock conservation.
    `DepletingConditioning` and `DepletingPrefix` condition actual path records
    and recover the remaining-stock law, with counts sufficient for prediction.
    `DepletingConsistency` gives horizon consistency and the joint law of
    successive count blocks, including empty samples and exhausted stocks.
53. `MultivariateFactorialPGF` expands bounded count-vector PGFs about one
    using all mixed factorial moments. `MultivariateReconstruction` proves
    that a finite rectangle of those moments determines the entire joint
    event law; the all-orders characterization obtains its bound from support.
54. `RationalCovarianceAlgebra` supplies signed rational product factorization,
    symmetric bilinear covariance, rational scaling, independence, and the
    dependent-sum variance formula, on the original finite records.
55. `ConditionalAlgebra` gives rational linearity, pull-out, idempotence and
    almost-sure uniqueness from fibre integrals. `ConditionalProjection`
    proves the squared-error decomposition, least-squares optimality and
    squared-norm contraction, retaining zero values on unsupported fibres.
56. `HighestFactorialMoments` extracts PMFs and full fixed-total joint laws
    from the top total order alone, with multinomial, reinforced and
    hypergeometric formulas. `PositiveSupport` supplies weighted congruence
    and finite-record singleton extensionality without shrinking domains.
57. `DepletingSupport` characterizes supported count observations by dimension,
    total draws and stock bounds, proves word permutation invariance even for
    null words, and provides conditioning from explicit feasible-count data.
58. `PositiveFactorialPGF`, `PositivePGFUniqueness` and `PositiveReconstruction`
    require dimensions and bounds only almost surely, so null outliers do not
    obstruct expansion or reconstruction. Original records and declared
    domains, and all existing stronger interfaces, are retained.
59. `ProjectionEquality` characterizes zero squared error and all optimal
    label predictors up to almost-sure equivalence, proves distance contraction,
    and proves decreasing optimal error under almost-sure label refinement.
60. `BinomialInversion` supplies constructive signed inverse Pascal coefficients.
    `FactorialInversion` and `MultivariateFactorialInversion` recover explicit
    numeric and joint PMFs by finite alternating sums of factorial moments,
    under almost-sure bounds and dimensions, with varying totals permitted.
61. `FiniteCovariance` identifies weighted-sum variance with the covariance
    quadratic form and proves positive semidefiniteness and its null directions.
    `OccupancyCovariance` specializes this to multinomial, reinforced and
    hypergeometric laws, including the fixed-total null direction and complete
    zero rows for zero-weight or zero-stock coordinates.
62. `DepletingAggregation` merges complete ordered removal paths on the
    original weighted records, even at raw impossible horizons. Its conditioning
    module proves remaining-stock identities, positive grouped evidence and
    commutation of the actual count-conditioned future path laws with merging.
63. `RefinementGain` identifies the exact reduction in prediction error with
    the squared distance between the conditional means, and characterizes
    equality of the errors by almost-sure equality of those means.
64. `FactorialRectangle` generalizes mixed expansion, explicit inversion and
    moment reconstruction to coordinate-specific bounds holding only almost
    surely. Its enumeration retains zero-width axes and the empty rectangle.
65. `HypergeometricCovariance` extracts the mixed second moment and closed
    nonpositive off-diagonal covariance, in both signed moment interfaces.
66. `MomentTableAlgebra` proves reverse Pascal inversion. `ProbabilityGrid`
    constructs normalized rational tables with every zero-mass cell retained.
    `FactorialMomentTable` and `FactorialMomentRealization` characterize bounded
    rational moment tables by nonnegative normalized inverted masses, construct
    their realizing law, recover every supplied moment, and prove uniqueness in law.
67. `OccupancyDegenerate` handles zero trials and full-population samples,
    including empty and one-ball populations. `OccupancyCovarianceEntries`
    factors the full covariance geometry through one categorical draw.
    `OccupancyNullspace` gives exact coefficient-based null criteria: on
    positive colours coefficients agree, while null-category coefficients are
    unrestricted; zero trials and full-population sampling are explicit exceptions.
68. `AlmostSureTower` proves the pointwise tower law under refinement required
    only almost surely, including unsupported coarse fibres. `CovarianceRows`
    identifies null quadratic directions with zero covariance-row products and
    specializes that equivalence to all three occupancy families.
69. `MomentTableCheck` scans a supplied scalar table and returns a certified
    realizing record or a negative-cell/normalization obstruction. The joint
    table modules tensor the inverse over coordinate-specific rectangles,
    construct the unique joint law and recover every supplied rectangle moment.
    `JointMomentTableCheck` provides the same executable certified decision for
    mixed tables. Both successful checkers retain every zero-mass grid cell.
70. `ObservationChains` composes almost-sure finite refinements with changing
    label dimensions, proves towers between stages, zero conditional increment
    means and orthogonality, and decomposes cumulative prediction improvement
    into the exact finite sum of increment energies.
71. `RationalLinearSolve` decides finite rational linear inequalities by
    constructive elimination and lifting, returning assignments or checked
    refutation traces. `PartialMomentProblem` connects this to actual finite
    laws for selected integer responses and scalar or mixed factorial moments,
    with exact rational intervals and no denominator cap. Grid restrictions
    are almost sure; constructed records retain every declared zero-mass cell.
72. `PartialMomentBounds` computes sharp event and moment bounds over those
    compatible laws. `RationalLinearBounds` projects the objective to one
    closed interval and lifts both endpoints; the public certificate includes
    actual compatible laws attaining both bounds and universal inequalities.
-/
