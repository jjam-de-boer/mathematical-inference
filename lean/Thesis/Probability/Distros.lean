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
import Thesis.Probability.Distros.IndependentSums
import Thesis.Probability.Distros.ChiSquared
import Thesis.Probability.Distros.GaussianMoments
import Thesis.Probability.Distros.BetaBinomial
import Thesis.Probability.Distros.MultivariatePGF
import Thesis.Probability.Distros.BinomialMoments
import Thesis.Probability.Distros.BetaBinomialMoments
import Thesis.Probability.Distros.GeometricMoments

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
-/
