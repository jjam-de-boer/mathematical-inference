import Thesis.Probability.Distros.Basic
import Thesis.Probability.Distros.Bernoulli
import Thesis.Probability.Distros.Categorical
import Thesis.Probability.Distros.Binomial
import Thesis.Probability.Distros.Multinomial
import Thesis.Probability.Distros.Sampling
import Thesis.Probability.Distros.LimitAnalogs

/-!
Named finite distros.

Reading order:

1. `Basic` defines `Distro` / `NatDistro`, outcome relabelling, moments, PGF,
   Markov, Chebyshev, Fin-supported weight packaging, and the slotwise Cauchy
   product for independent Fin-supported sums, packaged both as event masses
   and as PMFs;
2. `Bernoulli` is the two-cell generating atom, with mean and whole-number
   PGF, identified with the one-trial binomial along `false ↦ 0` and
   `true ↦ 1`;
3. `Categorical` is the finite labelled urn, with discrete uniform as the
   equal-weight case;
4. `Binomial` derives the success-count law from independent Bernoulli
   trials, records the closed binomial weights, identifies the two
   presentations as events and as PMFs, records the closed mean, evaluates
   the PGF at whole-number arguments, and identifies the independent sum
   of equal-weight binomials with the binomial of the summed trial count,
   and identifies the one-trial case with the Bernoulli distro mapped along
   `bernoulliBit` and back along `bernoulliOfBit`;
5. `Multinomial` is the occupancy-count law of independent categorical
   draws, with singleton occupancy PMFs under `multinomialWeight`;
6. `Sampling` records hypergeometric (without-replacement) and truncated
   geometric waiting-time distros, with singleton PMFs and the truncated
   geometric whole-number PGF;
7. `LimitAnalogs` records the lattice Gaussian `base^(k²)` window, the
   de Moivre binomial special case, χ² as a sum of centred squares, and
   the Pólya / truncated-gamma counterparts.  The lattice Gaussian mean
   is the window centre by reflection symmetry.  The truncated negative
   binomial has a whole-number PGF as a ratio of `nbSum` generating sums.
-/
