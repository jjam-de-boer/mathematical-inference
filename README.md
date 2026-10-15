# Mathematical inference: science and logic

This repository holds Jelmer de Boer's *Mathematical inference: science and
logic*: the Master's thesis in Artificial Intelligence submitted to the Open
University in 2026, and a book manuscript based on that thesis.

The work develops a finite, constructive account of mathematical inference.
It brings together Jaynes-style probability, Pearl-style structural causal
models, and explicit changes in epistemic state, with selected constructions
and proofs checked in Lean 4. It also considers the scientific practices and
institutions in which inference is performed.

## Read the texts

- The submitted thesis is available as a [PDF](latex/Thesis_Jelmer_de_Boer.pdf).
- The book manuscript is available as a [PDF](latex/mathematical_inference.pdf).

## Lean formalisation

The Lean development formalises selected finite constructions from the work.
Its public entry points are:

- `Thesis.Probability` — finite constructive probability;
- `Thesis.Causality` — finite structural causal models, interventions, modal
  edits, and counterfactual semantics; and
- `Thesis.CausalTransport` — finite-source correspondence and explicit
  interfaces to externally established causal results.

The complete development also includes a tenure-track example that combines
these components.

```mermaid
flowchart LR
  P[Finite constructive probability] --> C[Finite causal semantics]
  C --> T[Finite-source causal transport]
  C --> E[Tenure-track example]
  T --> E
```

### Finite distributions

[`Thesis.Probability.Distros`](lean/Thesis/Probability/Distros.lean) exposes
the named finite laws and their checked interpretations. Geometric and
negative-binomial outcomes count Bernoulli failures before the requested
successes. Truncation conditions on success within the finite window;
censoring clips the failure count to the cap and retains the entire tail.
Both laws are derived from actual finite Bernoulli products, and the
one-success negative binomial equals geometric.

The lattice Gaussian uses the rational kernel `q^(x²)` on `x ∈ [-radius, radius]`,
with `0 ≤ q ≤ 1`. Zero gives a point mass and one gives the discrete uniform
law. Equivalent rational presentations of the kernel give the same Gaussian
and finite χ² laws on every event. Its signed mean is zero and its variance is the exact finite second
centred moment. The finite χ² law sums independent squared coordinates:
equal radius and kernel give additivity in the degrees of freedom, mean
`df · m₂`, and variance `df · (m₄ − m₂²)`.

The library includes reusable expectation, map, independent-sum and PGF laws;
closed Bernoulli, binomial, geometric, hypergeometric and beta-binomial
moments; general rational censored PGFs; and a multivariate multinomial PGF
with matching occupancy dimensions. Beta-binomial normalization is the
rising factorial `(α+β)↑trials`, and its success-count law agrees on every
event with sequential finite Pólya urn draws and same-colour reinforcement.
Ordered Pólya words are exchangeable. Conditioning on a supported prefix
updates the two urn counts by the observed colour counts, with the exact
future law and both next-draw probabilities proved. The `*DistroOfTotal`
constructors permit zero success weight in censored waiting times and one
zero beta-binomial colour count. Their deterministic point-mass laws are
proved; beta-binomial moments and the urn correspondence include both
endpoints. Existing strict constructors agree with these variants.
Law equivalence transports event agreement through maps, products, positive
conditioning, expectations, moments, variance and PGFs, without requiring
finite enumerations of outcome types. Chebyshev is connected to variance
and holds at every positive rational radius. Finite generating functions
determine numeric and bounded count-vector laws constructively. Independent draws from the categorical constructor produce
the multinomial occupancy law on every event, including zero-weight colours.
Arbitrary category partitions produce multinomial laws with summed weights;
coordinate counts have binomial marginals, closed means and variances.
Distinct-coordinate cross moments and nonpositive covariances are proved with
integer numerators over positive denominators. The generic covariance agrees
with the centered product integral and with witnessed variance on its diagonal.
The signed-observable API extends this to integer coordinates, with symmetry,
bilinearity, law/map transport, zero covariance under independence, and the
covariance term in dependent-sum variance. Integer-observable variance is
proved nonnegative and agrees with the existing witnessed natural variance.
Falling-factorial moments of binomial, hypergeometric and beta-binomial laws
are proved at every order,
including orders above their finite support. General negative-binomial
factorial moments reduce to shifted finite generating sums; their means,
second moments and witnessed variances include the cap boundary terms and
the censored zero-success-weight endpoint. Conditioning a larger truncated
geometric or NB law on a smaller window recovers that smaller law; clipping
a larger right-censored law gives the smaller censored law on every event.
Hypergeometric is also realized by actual sequential two-colour urn draws
without replacement: each Bernoulli colour draw removes one ball of that
colour. Its count law agrees on every event, including empty and single-colour
urns, and the mean and finite-population variance transport to that process.

Multicolour Pólya paths draw from the current categorical weights and add one
to the chosen colour. Their occupancy law is Dirichlet-multinomial, with
multinomial coefficients times rising-factorial factors and normalizer
`(sum α)↑trials`. The categorical first-step semantics, every-event count
correspondence, support and PMF are proved, with zero individual parameters
permitted. Two colours recover the positive-total beta-binomial numeric law.
Natural likelihood reweighting transports through law equivalence and maps.
A general urn can add any natural number of balls after each draw. Its
rising-factorial normalizer and count law recover multinomial at increment
zero and the existing Pólya / Dirichlet-multinomial at increment one.
Scaling initial counts and reinforcement together preserves the law.
Arbitrary nonnegative rational Pólya parameters are implemented by clearing
one common denominator and adding that denominator after each draw. The
ordered and occupancy laws are invariant under equivalent rational
presentations and recover the original natural-parameter constructors.
Every joint falling-factorial moment is proved for multinomial,
Dirichlet-multinomial and arbitrary reinforcement. The formula is the total
falling trial factor times the product of coordinate rising factors, divided
by the rising total; at zero reinforcement these become weight powers.
The identities include zero colours and orders above the trial count.
Merging any categories in a reinforced path or count law sums their initial
weights and retains their reinforcement increment. Every Dirichlet-multinomial
coordinate has its beta-binomial marginal, closed mean and variance, with
zero-weight and single-colour endpoints included. Joint factorial moments
also give the individual factorial moments, means and distinct-coordinate
cross moments and signed covariances for every reinforcement increment.
Ordered reinforced words are exchangeable: equal colour counts give equal
word probabilities. Conditioning the actual path record on observed counts
and dropping the observed draws gives exactly the urn with parameters
increased by the increment times those counts. Counts are therefore
sufficient for every future event; the next-colour probability is
`(alpha[i] + d * count[i]) / (sum alpha + d * observed draws)`.

Variance uses the existing witnessed `QProb.sub` operation, and boundary
cases are covered by theorem statements and kernel-checked
[`DistributionLaws`](lean/Thesis/Examples/DistributionLaws.lean) and
[`DistributionExtensions`](lean/Thesis/Examples/DistributionExtensions.lean) regressions.

### Verification

The project uses Lean `v4.30.0-rc2` and has no third-party Lake dependencies.
To build the development:

```sh
cd lean
lake build
```

To enforce the project-wide kernel-axiom policy, run:

```sh
cd lean
lake build Thesis.AxiomAudit
```

The audit checks every declaration owned by an imported `Thesis.*` library
module and fails the build if a transitive kernel dependency is not `propext`
or `Quot.sound`. Continuous integration builds this audit target explicitly.
Finite-model soundness, d-separation correctness, and positive-model joint
and conditional completeness are implemented constructively. The public
constructors are `ObservedGraph.publishedSoundness` and
`ObservedGraph.publishedCompleteness`; completeness requires a value-rich
finite signature (two supplied distinct labels at each observed node).
Both joint and conditional fields return inspectable do-calculus/probability
derivations, with no external countermodel-family assumption or new Lean axiom.

The same positive-model result is implemented for every finite original
hidden DAG, with fixed observed domains and arbitrary finite hidden-variable
and private-noise domains. The constructor is
`FiniteLatentProjection.publishedHiddenDAGCompleteness`. In
`HiddenDAGCorrespondence`, `HiddenDAGModelClass.identifyJointKernel_identifiable_iff`
and `HiddenDAGModelClass.identifyConditionalKernel_identifiable_iff` prove that
the corrected ID/IDC engines succeed exactly for identifiable queries in the
full positive original-DAG class. Failure constructs actual original-DAG
countermodels, including genuine conditional value disagreement on common
support; no external latent-projection interface is assumed.

The finite probability records permit zeros. Native hidden-DAG soundness
already accepts explicit local derivation-support witnesses, and guarded
observational-chain compilation handles null prefixes without assigning a
value to `0 / 0`. Guarded joint ID and conditional IDC now have uniform
recursive local-data compilers and native interpretation. The one-way
all-model boundary is also implemented: identifiability in the full class
allowing zeros returns an actual guarded success and its local-data
compilation, while guarded failure constructs native countermodels in that
class. This does not make the local data automatically available everywhere.
The positive-model engine equivalences above remain distinct.

The current-input algebra is also zero-permitting: recursive marginal
certificates no longer require observed positivity, and exact prefix-quotient
derivations accept support at their enumerated input variants plus positivity
of the one displayed denominator. Their numerator may be zero. Native
hidden-DAG adapters preserve those same local conditions without assuming
canonical membership of a collapsed model. Component-factor extraction now
uses the graph-derived exchange/deletion rules with explicit local support;
its exchange intermediate can obtain support from observable predecessor
overlap. `PublishedCurrentKernelReduction.guardedComponent_supportedAt`
now constructs the whole prefix-first guarded component tree: each quotient
retains the actual current input, and its subtrees are requested only on a
positive causal or displayed prefix branch. The native adapter
`hiddenDAG_guardedComponent_supportedAt` preserves these same explicit local
conditions for original hidden DAGs, including noncanonical multi-child
collapsed roots. Regressions exercise an undefined quotient skipped by a
zero prefix, without replacing it by an arbitrary conditional value.

The reverse component-to-host bridge is also implemented by
`PublishedCurrentKernelReduction.hostFactorOfComponent_supportedAt` and its
native adapter `hiddenDAG_hostFactorOfComponent_supportedAt`. It keeps the
independently compiled component's exact prefix quotient and builds the two
reversed graph-rule trees from explicit local data, without assuming a
reduction of the whole host joint. Zero-outcome regressions exercise both a
compound component marginal and a noncanonical original hidden-DAG model.

Whole-host component-family assembly is implemented by
`PublishedComponentKernelReductionFamily.guardedReduction_supportedAt`.
Its guarded topological fold reads each independently compiled component's
exact quotient. Components may interleave; no whole-host reduction or
strict-product regrouping is assumed. A regression has a supported zero
first component and an undefined later component input: the guarded host
is still a supported zero, while the old strict product remains undefined.
`GuardedHostChain` provides the shared bounded derivation/support induction
for this assembly and the earlier whole-component extraction.

Native component-family assembly is implemented by
`PublishedComponentKernelReductionFamily.hiddenDAG_guardedReduction_supportedAt`.
Both prefix guards, the component conditional, finite input trees and the
displayed denominator are native data. Literal term and observational-record
preservation construct the full original-DAG support tree without requiring
a canonical collapse or a positive complete observed law. A nonpositive
five-node regression with a three-child collapsed root checks the supported
zero host and its genuinely undefined, skipped final quotient.

`identifyGuardedJointKernel` now computes the full guarded current-kernel ID
program, including pruning, action augmentation, component restriction and
multi-component assembly. Successful formulas remain action-free. Its graph
decisions and exact failure witnesses match the corrected positive engine,
and its public calls never return the unfinished sentinel. A complete native
mediator regression identifies structurally in both programs: the guarded
formula gives a supported zero while the strict formula is undefined.

The guarded `identified` outcome is still a candidate, not a blanket
semantic claim. `identifyGuardedKernelFuelLocalCompilation` and
`identifyGuardedJointKernelLocalCompilation` now construct its formula-aligned
derivation and support tree from recursively composed primitive local data.
The initial observational compilation requires only unit data; marginals
request inherited data at their actual enumerated variants, and guarded
folds request quotient data only on positive prefix branches.
`identifyGuardedJointKernel_soundAt` interprets the exact successful expression
in compatible root models, and `identifyGuardedJointKernel_hiddenDAG_soundAt`
reads it in every original finite hidden-DAG model at the stated boundary.
The native two-model identification adapter requests data in both models:
the dual causal/displayed prefix demand sets still require a general
recursive transfer proof; observable quotient leaves alone do not supply it.
`identifyGuardedConditionalKernel` retains the established finite rule-2
search, uses guarded joint ID at termination, and keeps the exact Bayes
numerator and its marginal denominator. Its decisions and failure witnesses
match positive IDC, with no public unfinished sentinel.
`identifyGuardedConditionalKernelFuelLocalCompilation` and
`identifyGuardedConditionalKernelLocalCompilation` compose the complete
promotion/Bayes support tree from primitive data; a terminal branch-data
lemma makes that boundary inspectable without normalizing the graph search.
`identifyGuardedConditionalKernel_hiddenDAG_soundAt` gives the native
interpretation, and its two-model adapter again requests local data on both
sides. A nonpositive native regression actually populates the compiler data
and applies the generic theorem to a supported-zero conditional, rather than
only comparing numerical evaluations.
`Kernel.supportedAt_promoteCondition` proves that actual conditional support
survives promotion by SCM composition and finite event-mass monotonicity.
The native rule-2 adapter consequently needs only the original conditional's
support, not factual action overlap or a separately assumed promoted support.
A native regression applies it at an observationally null action, where the
actual intervened conditioner is positive. `ConditionalPromotionCompilation`
now supplies its deeper recursive data: every demanded marginal variant
receives primitive component data, a zero `X` prefix skips the undefined
later quotient, and the Bayes/promotion constructors build the whole native
tree. `exact_program_formula` checks literal syntax and `native_sound`
interprets the exact engine expression, not just a numerical zero check.

`GuardedHiddenDAGBoundary` returns literal guarded success equations and
local-data compilations from all-class joint/conditional identifiability,
without choice or a semantic identifiability case split. Guarded failures
retain actual original-query countermodels, including conditional value
separation on common support. The returned local data is not asserted
inhabited in every model merely from success or the semantic premise.

An unrestricted zero-class **success iff identifiability** claim is false,
not an unfinished theorem to force. `GuardedHiddenDAGZeroBoundary` constructs
two finite original-DAG models on `X -> Y` with identical whole observed laws
but effects zero and one at an unobserved action value. Guarded ID succeeds
structurally there, its formula is undefined, and native soundness proves
that the compiler's local data is unavailable at that invalid application.
The final scope audit covers the requested implementation boundaries:

- Removed ordinary legacy entry points are rejected by the axiom/API gate;
  the modern engines' import-boundary regression excludes even qualified
  legacy imports. Historical traces retain explicitly labelled legacy code.
- Joint ID and conditional IDC construct the exact successful derivation and
  its support tree from primitive local data, permitting observed zeros.
  Native regressions validate skipped undefined quotients, compound recursive
  data and null-factual-action promotion; an invalid unsupported action is
  explicitly rejected by `no_local_data`.
- Native soundness and inhabited positive-model joint/conditional/hedge
  completeness cover original finite hidden DAGs, with fixed value-rich
  observed domains and arbitrary finite hidden/private-noise sizes. Neither
  canonical collapse nor an external latent-projection theorem is assumed.

The qualifications are part of the theorem statements: zero-aware soundness
requires the explicit local data, positive completeness retains its stated
model class, and unrestricted zero-class success equivalence is refuted,
not silently asserted.

Work toward the broader support-qualified Shpitser--Pearl result is active.
`Causality.Admissibility` formalizes the primitive displayed action test
`P(x | Pa(X) \ X) > 0` and positivity of the actual intervened conditioner.
The action test is proved equivalent to a genuinely defined positive
conditional. Pointwise overlap and overlap on every supported parent context
are distinct predicates, and their observational transfer is proved without
choice. These primitive tests permit observed zeros; they do not yet assert
that every conditional demanded by an ID/IDC run is admissible.

`ConditionalSupport` also proves exact preservation of earlier conditioner
probabilities under later interventions. Together with intrinsic promotion,
this constructs both primitive component-factor endpoints from an already
supported host conditional. The forward and reverse graph bridges no longer
request an independent exchange-support witness, and forward extraction no
longer requests a separate component-source witness. A native null-action
regression demonstrates why factual overlap is unnecessary for these
intrinsic support steps. The original local-data APIs keep their primitive
data explicit, especially recursive marginal variants and positive displayed
denominators. The newer availability and admissibility constructors described
below now build that data internally. The final zero-containing semantic
completeness package remains open; neither the positive package nor the
previously scoped implementation audit is relabelled as that broader result.

The recursive factor boundaries have now been weakened further.
`CurrentKernelSupportCompletion.marginal_source_positiveAt` interprets an
already completed inner marginal and transports its displayed positive value
to the actual causal predecessor. `CurrentKernelFactorInputs.host_supportedAt`
then builds the new host factor without factual overlap. Component-family
assembly uses the corresponding `CurrentKernelFamilyFactorInputs`: its causal
branch constructs host support from the actual positive prefix, while its
printed branch builds only the printed quotient. The actual guarded ID/IDC
local-data algebra now requests projected-graph accuracy, the recursive
finite input data and a positive displayed denominator; separate factor-level
factual-overlap and causal-component-support fields are no longer required.
The older raw sufficient-overlap constructors remain available separately.

`GuardedEvaluationSupport` reads support of the actual printed expression
back into its earlier printed prefixes, the factors demanded by positive
printed weights, each defined quotient's positive denominator and every
listed summand of a defined marginal. These general inversion lemmas do not
take a compiler tree or global positivity as a premise. What remains is the
uniform recursive construction of the local data from the published
admissible observational domain, including the causal/printed prefix bridge,
followed by the final support-qualified joint/conditional completeness
certificates. The uniform printed-support availability results below close
the recursive-data boundary, but do not replace that admissibility argument.

The causal/printed prefix bridge is now proved generically in
`GuardedPrintedSupportCompletion`. Its induction constructs the preceding
prefix tree before interpreting it, so a causal positive-prefix request can
use printed-only factor conditions without assuming soundness of the next
factor. `LocalKernelDataAvailability` uses that bridge and the evaluation
inverses to construct component and family data from a defined printed
expression and availability of the preceding inputs. Observation, literal
reindexing, strict marginalization, component extraction and family assembly
all preserve this constructive `PrintedAvailable` invariant.

`LocalKernelQueryDataAvailability` preserves the same invariant through
action deletion/addition, uncut ancestral pruning, incoming-cut action
augmentation and containing-component restriction. The actual split and
empty-host branch compilers also preserve it. The uniform
`identifyGuardedKernelFuelLocalCompilation_printedAvailable` now composes
these results for every actual fuel-bounded ID success, and the public joint
wrapper retains the literal returned formula. `LocalConditionalDataAvailability`
and `identifyGuardedConditionalKernelFuelLocalCompilation_printedAvailable`
extend the invariant through every actual IDC promotion and terminal Bayes
branch, retaining the original conditioner's support explicitly.

`GuardedPrintedSoundness` interprets those complete constructions in projected
root models and in all original finite hidden DAGs. Its public
`*_soundAt_of_printed_support` adapters require defined printed expressions,
plus original source support for conditional queries, not caller-populated
recursive data. Its native two-model adapters transfer printed support by
action-free observational invariance; original conditional common support
remains explicit. Regressions apply these adapters to the actual recursive
joint, zero-numerator Bayes and null-factual-action promotion programs, and
reject the genuinely undefined null-action formula.

`UsedConditionalAdmissibility` now specifies the used-conditional boundary
independently of the graph, identification engine and compiler. Kernel leaves
test their actual conditioners; quotients test their displayed denominators;
marginals inspect their listed variants. A guarded product demands its factor
only under a positive defined weight, whereas an ordinary product remains
strict. `supportedAt_of_usedConditionalsAdmissible` constructs support from
these primitive tests, and `usedConditionalsAdmissibleAt_iff_supported`
proves they introduce no stronger hidden requirement than this expression
language's actual partial evaluation. Neither direction uses causal soundness.

`HiddenDAGAdmissibility` states the tests directly on original finite
hidden-DAG records and proves their exact preservation through collapse.
Observable action overlap and action-free used-conditional tests transfer
between observationally agreeing records. The original causal conditioner's
positivity does not transfer by that argument and remains explicit.

`GuardedAdmissibleCertificates` constructs joint and conditional certificates
from every actual guarded success. Their support fields are inhabited
uniformly from the primitive native tests, using the full ID/IDC availability
proofs; callers do not supply compiler `Data` or recursive support trees.
These certificates have native one-model soundness and two-model
identification methods at admissible references. Their stated application
boundary uses fixed action values on all supported observed-parent contexts,
not a silently substituted pointwise action test. Native regressions apply
both certificates outside the globally positive model class, exclude an
inadmissible factual action, and distinguish a skipped null quotient from a
strict product that demands it.

`HiddenDAGAdmissibleDomain` now states primitive query admissibility and
semantic identification independently of any engine or proposed output:
uniform action overlap, plus positive original causal conditioners for
conditional queries. Identification quantifies over all native model pairs
at jointly admissible references. Independently proved positive coverage
puts the existing failure pairs inside this zero-containing domain without
restricting the domain itself to positive models or choosing a separating
reference. `HiddenDAGAdmissibleCompleteness` then constructs actual joint and
conditional certificates from those semantic premises and assembles the
inhabited `PrimitiveAdmissibleCompleteness` joint/conditional/hedge fields.
Failure and hedge witnesses retain their original native records, with
explicit admissibility at every reference. Regressions also feed directly
proved observational identification into both completeness fields and apply
the returned literal formulas in a genuinely nonpositive native model.

The missing used-conditional qualification cannot simply be removed.
`AdmissibleFrontDoorBoundary` retains a structurally successful graph but
uses a deterministic mediator, with `X = M = U`, `Z = U`, and respectively
`Y = false` or `Y = M xor U`. Both native records have identical whole
observed distributions and both action values are admissible everywhere.
Nevertheless `P(Y = true,Z = false | do(X = true))` is zero versus one half.
The exact guarded expression is undefined at that reference and its
used-conditional predicate correctly rejects it. Thus success iff semantic
identifiability on the external primitive query domain alone is false,
even after excluding null external actions.

The supported-zero graph-level result is now assembled separately in
`HiddenDAGSupportedDomain` and `HiddenDAGSupportedCorrespondence`. The semantic
definition asks for an actual finite action-free observational expression
that computes the native query on its primitive demand domain; it mentions
neither engine success nor compiler support trees. Its explicit
`PositiveCovered` condition admits every positive native record, preventing
an invalid expression such as `0/0` from claiming identification on an empty
domain. Coverage is proved for all kernel-generated expressions and also for
valid zero-containing syntax, including a skipped undefined factor.

`identifyGuardedJointKernel_identifiable_iff` and its conditional counterpart
prove exact success correspondence with that independent semantic predicate.
`identifiable_iff_positive` and `conditionalIdentifiable_iff_positive` also
prove that it retains the full established graph-level identification
criterion, rather than a smaller set chosen for the regressions. These
semantic equivalences do not restrict soundness applications to positives.
`publishedSupportedAdmissibleCompleteness` inhabits the actual joint,
conditional and hedge fields, returning the literal guarded expressions,
their path do-calculus derivations and their constructed native support.
The actual native failure pairs satisfy every positive-covered candidate's
application tests, so they refute all such observational representations.

The certificates now expose a stronger intrinsic application boundary than
the papers' separate factual-action restriction. Joint support needs only
the returned expression's used-conditional tests; conditional support needs
those tests and the positive original intervened conditioner. The
`intrinsic_soundAt` and `intrinsic_identifiableAt` methods require no factual
action overlap. The old paper-qualified wrappers remain available.
`jointAdmissibleAt_iff_supported` and
`conditionalAdmissibleAt_iff_endpoints_supported` prove exact applicability:
no hidden extra data, positive outcome numerator or factual overlap is
required. Pointwise and uniform-parent paper application boundaries are
both proved included in this intrinsic domain. A native null-action
promotion regression applies the new completeness output outside the
paper-qualified action boundary, while supported-zero joint/Bayes examples
and invalid null quotients remain checked.

The scope is finite rational probability, fixed value-rich observed domains
for the completeness/countermodel direction, and arbitrary finite hidden
and private-noise alphabets in every original hidden DAG. It is query-level,
support-qualified graph identification, not an unrestricted action-only
zero-class equivalence. Applicability is maximal for each literal returned
formula under the existing partial evaluation, but no theorem here promises
that this formula covers every reference covered by any alternative formula,
or that graph failure excludes every distribution-specific identification.
Those stronger data-dependent coverage problems require a separate result;
they are not silently asserted by the supported completeness package.

Continuous probability, general measure theory, and a complete formalisation
of every philosophical or sociological claim are outside this project's scope.
