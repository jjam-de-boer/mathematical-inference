import Thesis.Probability.Distros.Basic
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
import Thesis.Probability.Distros.PolyaUpdates
import Thesis.Probability.Distros.Degenerate
import Thesis.Probability.Distros.NegativeBinomialMoments
import Thesis.Probability.Distros.CapConsistency
import Thesis.Probability.Distros.HypergeometricUrn
import Thesis.Probability.Distros.MultivariateHypergeometric
import Thesis.Probability.Distros.HypergeometricFactorialMoments
import Thesis.Probability.Distros.HypergeometricMarginals
import Thesis.Probability.Distros.HypergeometricAggregation
import Thesis.Probability.Distros.Reweight
import Thesis.Probability.Distros.MulticolourPolya
import Thesis.Probability.Distros.KernelInvariance
import Thesis.Probability.Distros.SignedCovariance
import Thesis.Probability.Distros.SignedCauchy
import Thesis.Probability.Distros.RationalMoments
import Thesis.Probability.Distros.RationalClearing
import Thesis.Probability.Distros.RationalConcentration
import Thesis.Probability.Distros.RationalMarkov
import Thesis.Probability.Distros.RationalChebyshev
import Thesis.Probability.Distros.ConditionalMoments
import Thesis.Probability.Distros.ConditionalObservable
import Thesis.Probability.Distros.ConditionalTower
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
-/
