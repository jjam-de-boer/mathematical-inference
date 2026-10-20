# Finite entropy and maximum-entropy implementation

The goal retains rational probability laws and the existing constructive axiom
policy. Entropy values may be irrational; exact symbolic logarithms and rational
interval certificates are auxiliary values, never new atom weights. Units are bits.

## Checkpoint 1: exact logarithmic arithmetic

- `PositiveRatio` supplies unreduced positive rational arguments, equivalence,
  order, products, inverses and powers.
- `ExactLog` represents `log₂(argument) / degree` with a positive natural degree.
  Equivalence and order compare rational powers at common degrees. Addition,
  negation, natural scaling and positive natural division respect the value.
- `ExactLogRational` embeds signed rational numbers of bits and proves exact
  correspondence with integer cross-product comparison.
- `ExactLogEnclosure.enclose` terminates for every positive rational tolerance.
  It returns a common-denominator rational interval containing the exact value,
  with a proved width strictly below the requested tolerance. Binary-length
  initial bounds and depth selection avoid a linear-depth precision search.
- `Thesis.Examples.ExactLog` checks root/argument presentation changes, negative
  values, exact bounds around `log₂(3)`, and executed certified bisection.
  Both full and early arithmetic axiom gates import the regressions.

These are symbolic logarithms with an exact ordered arithmetic interpretation,
not a newly assumed real logarithm. A separate semantic bridge to a completed
real-number model would need its own proof and is not silently assumed.

## Checkpoint 2: entropy and positive-reference KL

- `ExactLogWeights` proves congruence for both rational coefficients and exact
  logarithm values, monotonicity, and finite-sum congruence/permutation laws.
- `EntropyValue` defines `-p log₂(p)` and `p log₂(p/r)`, with explicit zero
  observed-mass branches and positive reference masses. Both respect unreduced
  rational presentations. Entropy contributions in `[0,1]` are nonnegative.
- `Distros.EntropyGrid` requires distinct observable outcomes. `Distro.entropy`
  and `Distro.relativeEntropy` require almost-sure grid support, so extra null
  atom labels remain admissible. They aggregate the original singleton PMFs.
- Entropy and KL are invariant under `SameLaw`. Entropy is nonnegative and
  invariant under grid permutation and adjoining a zero-mass cell. Positive
  reference laws have zero self-divergence.
- Executed regressions cover fair and point laws, duplicate/split/reordered
  records, rescaled denominators, a retained null outlier, grid changes, and
  unequal positive prior weights. The fair-law/prior `(1/4,3/4)` KL value is
  certified exactly as `log₂(4/3)/2`.

## Checkpoint 3: constructive arithmetic–geometric mean foundation

`FiniteAMGM` proves the denominator-cleared finite inequality at every list
length, using Cauchy's finite doubling/descending proof. Natural multiplicities
then give weighted AM–GM, including zero values and weights. Both non-strict and
strict common-denominator product bounds are available for the rational Gibbs
inequality. This foundation does not yet establish KL nonnegativity, its equality
case, entropy concavity, or maximum-entropy optimization.

## Checkpoint 4: rational Gibbs inequality and KL nonnegativity

`RationalAMGM` clears the finitely supplied argument denominators and proves
weighted rational products are at most one whenever their arithmetic mean is
at most one, including empty and zero-weight families. `LogMeanInequality`
transports that algebraic result to common-degree exact logarithms.

`Distros.EntropyGibbs` proves grid PMF normalization and numerator sums, then
`Distro.relativeEntropy_nonnegative` for every rational law and positive reference
law on the declared grid. It imposes no positivity assumption on observed masses.
The proof includes aggregation of duplicate atom occurrences and null outliers.
Executed regressions include a point law on a three-state grid with two zero
observed cells, whose uniform-reference KL equals `log₂(3)` exactly.

The equality case, upper entropy bounds, strict concavity and optimization
results remain outstanding; KL nonnegativity alone does not establish them.

## Checkpoint 5: equality in Gibbs and KL

`FiniteAMGMEquality` proves the weighted equality case using midpoint
comparisons and the already established finite AM–GM bound. `RationalAMGMEquality`
and `LogMeanEquality` transport it to arbitrary positive rational arguments;
zero-weight arguments remain unrestricted.

`Distro.relativeEntropy_equiv_zero_iff` proves that KL vanishes exactly when
the laws agree on every Boolean event. Equality at positive observed cells
and normalization also force equality at zero observed cells. The regressions
check a split/rescaled/reordered law with a null outlier, a genuinely different
point law, and an unrestricted zero-weight argument in the rational equality
lemma. No literal atom-list equality is assumed.

## Remaining full goal

1. Strengthen the grid-independence interface as needed for the later optimizer;
   preserve every established atom-presentation and null-cell invariance law.
2. Prove entropy bounds, KL nonnegativity and equality, strict concavity,
   uniqueness and global log-linear optimality, with explicit support/boundary
   assumptions. Investigate a finite weighted AM–GM route.
3. Integrate exact/interval rational expectations through `PartialMomentProblem`,
   retaining infeasibility certificates, forced-zero cells and redundant rows.
4. Prove an explicit uniform entropy continuity modulus, including zero. Implement
   total finite-box optimization with exactly feasible rational witnesses and a
   global rational entropy gap at every positive rational tolerance. No fixed
   denominator cap or exact rational maximizer is presumed.
5. Exercise uniform/unique/inconsistent/boundary/redundant constraints, duplicate
   and null presentations, and the three-state mean-1/2 irrational-optimum case.
   State the additional semantic bridge required for real-optimum claims.

Ordinary local Lake builds use `LEAN_NUM_THREADS=1`, the committed 4608 MiB
compiler threshold and the existing cache. Only one build may run on the machine
at a time. Targeted checks do not establish full-project success; the full build
and axiom audit remain mandatory. Remote CI repeats both gates for published
checkpoints before they are reported as verified on main.
