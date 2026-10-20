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

## Remaining full goal

1. Define Shannon entropy and positive-reference KL divergence on distinct finite
   grids, aggregating duplicate outcome occurrences. Prove `SameLaw` invariance,
   including splitting, reordering, denominator changes and null outliers.
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

Capped local elaboration checks cover selected modules only. Each checkpoint
still requires remote full compilation and both transitive axiom gates before
being reported as verified on main.
