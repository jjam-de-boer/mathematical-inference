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

## Checkpoint 12: signed-moment log-linear optimality

`LogExpectation` integrates exact logarithmic observables against aggregated
PMFs and proves finite affine integration. `ShiftedMoments` computes a finite
offset for each signed integer response on the original declared grid. Fixed
signed expectations therefore fix the corresponding nonnegative natural moments;
unsupported zero-weight atom labels impose no extra shift hypothesis.

`PartialMomentProblem.LogLinearReference` records a positive rational reference,
an affine log score and selected exact rows from the original problem. The
coefficients are arbitrary exact logarithm values and may be negative. The
selected endpoints need only be equivalent rational presentations; redundant
rows and other interval constraints remain admissible.

`LogLinearReference.crossEntropy_fixed` proves equal cross entropy for every two
feasible laws. A feasible anchor consequently gives a universal entropy upper
bound even when the reference itself has the wrong target expectation. If the
positive reference is feasible, `LogLinearReference.optimal` proves global
maximality and equality exactly at the same probability law. This is the promised
fixed-expectation bridge, not merely a stationary-point assertion.

The reference positivity premise includes every declared cell. A candidate with
forced zeros cannot satisfy that premise on the full grid; the total optimizer
has no such premise and already handles those boundaries. The entropy-preserving
internal support restriction is available for separate boundary score arguments.
Regressions prove a nonuniform global maximum under a negative integer response,
with a retained null outlier. The constructive arithmetic audit passes.

## Checkpoint 13: tight mean-one-half certificate and validation

`EntropyHomogeneous` proves an equivalent common-degree entropy formula, allowing
concrete certificates to execute without multiplying all the individual root
degrees. `Thesis.Examples.EntropyMeanHalf` uses the exactly feasible rational law
`(62/100, 26/100, 12/100)`, with a split atom and a retained null outlier. It keeps
the original grid, exact mean `1/2` and duplicate redundant signed rows.

A rational Gibbs reference with ratio `13/30` gives a global upper bound through
the proved moment/log-linear bridge, even though that reference has a different
mean. Exact rational-power comparisons certify the interval `[2599/2000,
2601/2000] = [1.2995,1.3005]` bits, with width exactly `1/1000`, for the requested
rational optimum certificate. No exact rational maximizer is asserted.

The same example exposes the general total algorithm at every positive rational
tolerance. Additional executed regressions retain a forced-zero cell and repeated
signed constraint rows. `EntropyCertificate.width_bound` also states the width as
the existing witnessed rational subtraction `U - L ≤ epsilon`.

All six planned mathematical activities are now implemented for rational laws.
The complete build and full axiom audit remain mandatory publication gates.
Practical improvements to the exhaustive fallback and the separate real-number
semantic development are extensions beyond this completed rational scope.

## Standard real-valued semantics: additional bridge required

The kernel results above concern exact symbolic logarithms and the framework's
rational probability laws. No completed real-number type, real logarithm axioms,
choice principle or real-valued maximizer is silently imported.

To interpret the same certificates in the usual finite real model, a separate
semantic development must establish the following facts.

1. Interpret an `ExactLog` as `log₂(argument)/degree` in a real-number model with
   a logarithm on positive arguments, and prove that equivalence, addition, rational scaling and
   rational-power order agree with that interpretation. Embed rational bit bounds
   by the same ordered map. This identifies the symbolic entropy with
   `-sum p_i log₂(p_i)`, using the proved zero convention.
2. Embed the original rational moment rows into real finite-coordinate space and
   prove density of exactly feasible rational points in their real feasible
   polytope. Rounding coordinates independently is insufficient for exact moment
   equalities. A suitable route is a finite rational-vertex representation followed
   by rational approximation of convex combination coefficients; that preserves
   exact equalities, closed intervals, forced-zero faces and redundant rows.
3. Prove continuity of real finite entropy, including zero. Density and the closed
   order relation then transfer each universal rational upper certificate to
   every real feasible law. Compactness of the nonempty bounded closed polytope
   and continuity yield an attained usual real maximum, if that existence claim
   is wanted. Constructive real existence would require its own corresponding
   compactness or effective-limit proof.

These are additional semantic/density theorems, not premises exposed by the
rational algorithm. The implementation already returns the requested universal
rational certificates without assuming those real theorems.

## The three-state mean-one-half real model

In the usual real interpretation, a positive Gibbs law on `{0,1,2}` with mean
`1/2` has probabilities `(1,r,r²)/(1+r+r²)`, where `3r²+r-1=0`. The positive
solution is `r=(sqrt(13)-1)/6`. It satisfies the constraint, and the global Gibbs
inequality certifies it as the real entropy maximum. Strict concavity gives
uniqueness. Since `r` is irrational and equals the ratio of its second and first
probabilities, that exact real optimizer cannot have all rational probabilities.

This real-model explanation is not asserted as a new Lean theorem about a real
number type. The rational library instead certifies exactly feasible rational
approximations and universal error bounds. Its separate real semantic/density
bridge, described above, is what would formally connect those certificates to
the displayed real optimizer.

## Verification and scope

Every new example is included in both the early constructive audit and the full
project audit. Completed mathematical checkpoints are published to main only
after the complete CI build and full axiom gate pass. The implementation keeps
rational laws, exact symbolic logarithms, and certified rational approximations;
it does not claim an efficient exhaustive search or a completed real semantics.

Ordinary local Lake builds use `LEAN_NUM_THREADS=1`, the committed 4608 MiB
compiler threshold and the existing cache. Only one build may run on the machine
at a time. Targeted checks do not establish full-project success; the full build
and axiom audit remain mandatory. Remote CI repeats both gates for published
checkpoints before they are reported as verified on main.


## Foundational and physical extension: in progress

The completed six-activity rational implementation above defines Shannon
entropy and proves its theory and certified optimization. The subsequent
seven-activity goal additionally asks for a characterization from uncertainty
requirements, constructive analytic semantics, a real feasible-polytope and
optimizer bridge, multiplier necessity and sufficiency, partition-function
calculus, and a conditional finite thermodynamic identification. These further
activities are not claimed complete by the earlier checkpoint descriptions.

The first foundation now includes:

- `EntropyGrouping`: the exact product-mass identity, finite two-stage grouping,
  independent-product additivity, rational presentation congruence, permutation
  and insertion of null coordinates. Zero branch weights are allowed.
- `Distros.UncertaintyMeasure`: normalized rational probability vectors and an
  explicit abstract uncertainty specification. Its requirements are coordinate
  representation invariance, permutation, null insertion, grouping, monotone
  uniform uncertainty, and fair-bit normalization in `ExactLog`. No uniform
  logarithm formula, derivative or uniqueness conclusion is a premise.
- `UncertaintyMeasure.shannon`: the implemented entropy satisfies every listed
  requirement. The bridge from an existing `Distro` uses aggregated singleton
  masses, so split records and null outliers do not become extra states.
- `Distros.UncertaintyUniform`: grouping implies `h(mn) = h(m) + h(n)`,
  `h(1) = 0`, and `h(n^k) = k h(n)` for every abstract measure, including
  exponent zero. These are the first steps of the number-theoretic proof.
  The subsequent checkpoints establish uniform uniqueness and then the full
  rational-vector characterization.

The new regressions include unequal rational denominators, a three-way
refinement with a zero-weight branch, retained zero coordinates, abstract
uniform power laws, and the aggregated distribution bridge. Both early and
full audits import the regression module. The remaining analytical and
physical work retains its full requested scope and requires separate proofs.

### Uniform uncertainty is now characterized

`ExactLogSeparation` proves an explicit Archimedean separation principle for
exact symbolic logarithms. A positive exact value has a computed natural
multiple of at least one bit, by a finite Bernoulli lower bound. Consequently,
if every natural amplification of `x` is at most the same amplification of
`y` plus one bit, then `x ≤ y`. No real completion, derivative, general excluded
middle, or extra separation axiom is used.

`Distros.UncertaintyUniformUniqueness` compares each uniform choice with the
two adjacent powers of two around its repeated product. Grouping and fair-bit
normalization put every admissible uncertainty measure inside the same bit
bracket. The proved separation principle forces two such measures to agree.
Thus `UncertaintyMeasure.uniform_log` derives `h(n) = log₂(n)` from the listed
requirements. The subsequent refinement checkpoint applies this result to
arbitrary rational vectors, including their null cells.

### Complete rational Shannon characterization

`ProbabilityVectorCounts` computes a common natural-count presentation of every
normalized rational vector using the existing constructive denominator-clearing
algorithm. It proves coordinate equivalence without imposing a denominator cap.
`UncertaintyRefinement` groups a uniform space into positive count blocks and
uses the proved uniform uniqueness to force agreement between any two admissible
uncertainty measures on those rational vectors.

`UncertaintyCharacterization` extends the result to arbitrary zero coordinates
using permutation and null insertion. These transformations occur inside the
proof; its public theorem concerns the entire original vector. Its theorem
`UncertaintyMeasure.unique` compares any two measures satisfying the listed
requirements. `UncertaintyMeasure.characterization` then specializes one of them
to the proved Shannon instance and yields exactly the implemented entropy.
`distro_characterization` connects the result to the existing `Distro.entropy`
on aggregated observable grids, including split atoms and null outliers.

This completes the rational `ExactLog` characterization requested in activity 1.
No uniform logarithm formula, continuity, derivative or entropy formula was a
premise about the arbitrary measure. The proof uses the established order
separation of the chosen exact value space. It does not assert a characterization
for arbitrary other value spaces or for unrestricted real probability vectors.

The uncertainty requirements identify the quantity. They do not alone imply
that an inference procedure must maximize it. Choosing maximal uncertainty
subject to known constraints is an additional inference criterion; the existing
certified optimizer proves that criterion is met to the supplied tolerance.
An alternative justification through a sampling/allocation model requires that
model and its asymptotic argument as additional premises. Neither the probability
rules nor fixed averages alone silently supply this policy.

Activity 2 now has the initial value foundation described below. Activities 3–6
remain open: real feasible-law and optimizer bridges, multiplier necessity and
interval/boundary qualifications, partition-function calculus, and the
conditional physical correspondence.
Activity 7 remains ongoing as each new stage is tested and audited. The rational
characterization regressions include unreduced unequal denominators, null cells
at several positions, generic arbitrary measures, and the existing law adapter.


### Constructive analytic values: first foundation

`RationalApproximation` proves rational order closure under arbitrarily small
positive rational errors, with an explicit separating precision. The proof
works with unreduced signed fractions. `ConstructiveReal` then presents an
auxiliary real value by an executable enclosure at every positive rational
precision. Its intervals are mutually consistent and their widths are bounded
by the requested precision. Rational values have singleton enclosures. Closed
order is a proposition comparing all enclosure bounds; no arbitrary real
comparison or equality decision is assumed.

`ConstructiveRealAdditive` and `ConstructiveRealScaling` construct addition,
negation, finite sums, natural division and nonnegative rational scaling, with
proved congruence and additive/order laws. These values remain auxiliary;
`Distro` atom weights and exactly feasible solver outputs are still rational.
The current arithmetic gives correctness constructions, without a claim of
an optimized numerical evaluator.

`ExactLogRationalArithmetic` proves signed rational-bit addition and natural
amplification identities. `ExactLogInterpretation` constructs a real presentation
from the existing rational bisection certificates. It preserves and reflects
`ExactLog` order and equivalence, agrees with the rational embedding, and
preserves addition, negation, finite sums, natural division and rational scaling.
Thus existing exact comparisons can be used as real-value bounds, and the
interpretation does not identify unequal exact values.

`EntropyInterpretation` constructs base-two logarithms of positive rational
arguments in this value space, proves their product/inverse laws, and connects
the existing rational entropy and KL summands to `−p log₂(p)` and
`p (log₂(p) − log₂(r))`. The finite entropy sum is preserved. Zero observed
mass contributes zero without evaluating `log(0)`; KL retains its explicit
positive-reference hypothesis.

This is a partial implementation of activity 2. The subsequent checkpoint
below constructs effective rational limits. General limit and continuity rules,
multiplication of arbitrary real values, logarithms on general positive
real arguments, exponentials, differentiation and certified Taylor remainder
bounds still require separate proofs. No calculus, ideal optimizer existence,
rational feasible-polytope density, multiplier existence or physical entropy
identification is claimed by this initial value foundation.

The new audited regressions compute rational enclosures of `log₂(3)`, transfer
an exact lower bound to real order, exercise arbitrary-presentation additive
laws and rational scaling, and preserve null entropy coordinates and KL terms.


### Effective rational limits

`ConstructiveRealLimits` completes a regular rational approximation net by an
explicit interval construction. It proves a bound around every supplied
approximant and uniqueness of the resulting real value among presentations
satisfying those bounds. A `RationalCauchySequence` includes an executable
modulus and a proved tail-error estimate. A common later index turns it into
a regular net, without requiring a monotone modulus. The resulting limit has
proved error bounds for every sufficiently late sequence term.

Every existing `ConstructiveReal` also supplies a regular net of computed
rational lower endpoints. Completing that net is proved equivalent to the
original real presentation. This is scalar rational reconstruction; it does
not independently round probability coordinates or establish density inside
a constrained feasible polytope.

The regressions construct the nonconstant sequence `1 − 1/(n+1)`, give it a
valid modulus, and prove its independently constructed limit equals one.
They also check tail bounds and reconstruction for arbitrary real presentations
and the certified `log₂(3)` presentation. The approximation modulus is explicit
input data: these results do not assert convergence from strict concavity or
supply the quantitative optimizer estimates still required in activity 3.
