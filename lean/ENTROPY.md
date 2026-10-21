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
inequality. Later checkpoints use this foundation to establish KL and entropy
bounds; strict concavity and the total optimizer remain separate tasks.

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

KL nonnegativity alone does not establish the equality or optimality results;
the following checkpoints prove those additional statements separately.

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

## Checkpoint 6: entropy bounds and the cross-entropy criterion

`ExactLogLinear` proves rational bilinearity and the finite-sum identities needed
for entropy comparisons. `CrossEntropyValue` and `Distros.CrossEntropy` establish
KL = cross entropy minus entropy, the global cross-entropy upper bound, and a
positive-candidate optimality criterion: fixing the candidate cross entropy
makes the candidate a global entropy maximum, with equality exactly at the same
law. The bridge from rational moment constraints and a log-linear score to this
cross-entropy equality is still required.

`EntropyGrid.uniform` retains every declared cell with weight one.
`Distros.EntropyUniform` proves its entropy is exactly `log₂(cardinality)` and
that every supported law satisfies `0 ≤ H ≤ log₂(cardinality)`. Equality in the
upper bound holds exactly for the uniform law. Null cells in the declared grid
remain part of the cardinality, and null atom outliers remain admissible.

`Thesis.Examples.EntropyBounds` checks the three-state uniform bound and its
equality case, and the nonuniform candidate `(1/4, 1/4, 1/2)` with entropy `3/2`
bits. A competitor with the same cross entropy and a retained null outlier has
strictly smaller entropy.

## Checkpoint 7: strict concavity, including the boundary

`Distro.mixture` wraps the scale-and-append rational record construction, keeping
both atom lists and their null outliers. Singleton masses and cross entropy obey
the expected affine formulas even when input denominators differ.

`Distro.entropy_mixture_comparison` proves concavity for any two positive natural
mixing masses, normalized by their sum, and equality exactly when the input laws
are `SameLaw`. `Distro.entropy_strict_concave` states the strict consequence for
different laws. Shared zero-mass cells are handled by an internal positive-support
restriction with a proved entropy-preservation lemma; the caller's declared grid
and atom records are never replaced. No full-grid positivity premise remains.

`Distro.entropy_maximum_unique` proves that any attained maximum in a class closed
under midpoints is unique as a law. This is a conditional uniqueness theorem,
not an existence assertion for exact rational maximizers. Regressions exercise
shared zero cells, null outliers, unequal denominators, unequal mixing weights,
strict inequality for distinct point laws, and equality for split presentations.

## Checkpoint 8: moment feasibility and the first continuity estimate

`EntropyMomentConvex` proves affine signed rational expectations for the actual
mixture constructor, and preservation of every closed rational moment interval.
`PartialMomentProblem.Admissible` includes the original almost-sure grid support
and all existing constraint rows. Its entropy uniqueness theorem now applies
directly to exact and interval problems, with no row independence or interior
mass hypothesis. The existing feasibility/refutation solver remains the source
of exactly feasible rational witnesses and infeasibility certificates.

Regressions combine an exact mean, a signed response interval, a forced-zero
coordinate, duplicate redundant rows, unrelated input denominators and retained
null outliers. Mixture feasibility is proved for all such problems, not checked
only on a denominator grid.

`FiniteBernoulli` proves finite power difference and complement bounds by natural
induction. `EntropySmallMass` derives
`log₂(den/(den-1)) ≤ 1/m` whenever `2m ≤ den`, and exact-log monotonicity in a
nonnegative rational coefficient. These are proved ingredients for the boundary
continuity argument, not yet a full entropy continuity modulus or an optimizer.

## Checkpoint 9: quantitative entropy continuity at zero

`EntropyTermBounds` derives a scalar cross-entropy bound from the actual
Gibbs theorem, using an auxiliary two-state reference. The observed mass may
be zero or one. For every `k`, it proves
`p ≤ 1/2^(k+1) → -p log₂ p ≤ (k+3)/2^(k+1)`.

`entropyBoundaryThreshold` supplies a positive rational threshold for every
positive rational tolerance. `entropyTerm_near_zero` proves that every rational
probability below that threshold has entropy contribution at most the requested
error. Its construction uses finite powers and binary lengths, with no
unbounded search, real logarithm axioms or denominator restriction on the input.
Regressions include probability zero and a non-dyadic mass `3/10000000`.

This completes the scalar boundary estimate. The uniform two-point continuity
modulus, moment/log-linear bridge and total constrained optimizer remain open.

## Checkpoint 10: uniform two-point entropy continuity

`EntropyIncrement` proves algebraic bounds on the change of an entropy term
between positive probabilities. `EntropyContinuity` combines those bounds with
the zero-boundary estimate. For every natural precision `n`, coordinate distance
at most `1/2^(3n+6)` gives entropy-contribution error at most `1/2^n`. The theorem
covers arbitrary unreduced rational presentations and both probability endpoints.
A total rational threshold interface also accepts every positive rational error.

`Distros.EntropyContinuity` lifts that result to full entropy on the caller's
declared grid. Its explicit coordinate threshold depends only on grid cardinality
and requested error. The resulting symmetric entropy bounds quantify over all
supported rational laws, without a denominator cap or an interior-support premise.
Regressions exercise zero, one, interior probabilities, unrelated denominators,
a zero cell gaining positive mass, a shared null cell and null record outliers.

The finite-box constrained optimizer and the moment/log-linear optimality bridge
remain unfinished. Uniform continuity is now a proved input to that optimizer,
rather than an assumption left to its caller.

## Checkpoint 11: total certified rational entropy optimization

`ProbabilityBoxes` enumerates a finite cover by rational coordinate intervals.
Every rational probability in `[0,1]` has a floor-selected box, and any two points
in one box differ by at most its width. The mesh controls interval width, never
the denominator of an input law or a feasible solver witness.

`EntropyBoxes` adds these coordinate intervals to the unchanged
`PartialMomentProblem` grid and original exact/interval rows. `EntropyBoxSearch`
uses the existing complete feasibility solver in each box. A box containing a
feasible law cannot be rejected, and its exactly feasible witness is close enough
for the proved entropy continuity bound. Exact comparisons select a maximum
among those finitely many candidates. The result bounds every feasible rational
law, not just those candidates. A universal-entropy-bound fast path can avoid the
exhaustive cover when it already certifies the supplied feasible witness.

`ExactLogPositiveEnclosure` clips a lower endpoint at zero only under a proved
nonnegativity hypothesis. Its integer conversions use explicit constructive
cases. `PartialMomentProblem.solveEntropy` either retains the original certified
infeasibility result or returns an `EntropyCertificate` containing an actual
compatible rational law `q` and nonnegative rational `L,U` with

- `L ≤ H(q)`;
- `H(p) ≤ U` for every exactly feasible rational law `p`;
- `L ≤ U ≤ L + epsilon`.

Optimization error and enclosure width each receive half of the requested
positive rational tolerance. The fallback is a total reference algorithm; its
finite Cartesian box enumeration may be very expensive. No practical runtime or
exact rational maximizer is asserted.

Executed regressions check arbitrary-denominator box indexing, feasible and
infeasible boxes, an infeasible moment problem, the full singleton solver with a
clipped zero lower endpoint, and a fair-law certificate at tolerance `1/1000`.
The whole dependency closure passes the constructive arithmetic axiom gate.

## Remaining full goal

1. Complete the bridge from fixed rational moment expectations and a log-linear
   reference score to the established global cross-entropy optimality criterion,
   with explicit support/boundary assumptions.
2. Complete the three-state mean-`1/2` example with useful concrete certified
   approximations and an accurate explanation of its usual irrational optimum.
   Extend executed optimizer regressions for forced-zero and redundant rows.
3. Document the precise additional real-number semantic/density bridge needed to
   interpret rational universal certificates as bounds on the usual real optimum.
   The implementation currently quantifies over the framework's rational laws.
4. Continue complete-project builds, full axiom audits and remote CI for each
   published checkpoint. Targeted or early checks alone are never full verification.

Ordinary local Lake builds use `LEAN_NUM_THREADS=1`, the committed 4608 MiB
compiler threshold and the existing cache. Only one build may run on the machine
at a time. Targeted checks do not establish full-project success; the full build
and axiom audit remain mandatory. Remote CI repeats both gates for published
checkpoints before they are reported as verified on main.
