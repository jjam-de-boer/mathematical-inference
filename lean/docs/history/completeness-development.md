# Historical completeness development

These notes preserve the historical implementation inventory from
`CausalTransport/Completeness.lean` at the refactoring baseline `f298629`.
They describe earlier stages, including obligations subsequently discharged;
they are not a list of current open completeness problems. The current
published positive-class theorem is assembled in `HedgeChannelCompleteness`,
and native positive and supported-zero coverage is described in
`THEOREM_COVERAGE.md`.

This is a verbatim historical source comment. No mathematical declaration
is moved or deleted by recording it here. The older engine's valid trace
and failure facts remain distinct from the refuted general formula compiler.

## Preserved implementation inventory

```text
/-
Detailed implementation inventory.  This checkpoint record is intentionally
kept near the implementation, but is not the module's public status summary.

Constructive completeness of finite identification, specialized to the
classical model class.

`PublishedCompleteness` is indexed by a `GraphModelClass`.  The Shpitser–Pearl
/ Huang–Valtorta theorem is the inhabitant for `GraphModelClass.positive`
once the signature supplies `ValueRich` (two enumerated distinct values at
every node).  The unrestricted class `GraphModelClass.all` remains the home
of soundness: certificates that work with zeros.

This module records the executable ID engine, positivity of
observational cylinders, the empty-action certificate (already action-free),
agreement of executable c-components with inductive bidirected connectivity,
and extraction of a `HedgeWitness` from ID failure by finite search over
vertex selections and kept directed children inside the failing
c-component.  Successful ID runs are action-free observational formulae.

The detailed inventory below records the legacy engine's proved leaves and
the obligations identified at that checkpoint.  Its long list of
finite-depth failure paths documents checked special cases already in the
library; it is not a roadmap for adding ever-deeper path enumerations.
Generic work on nested engine results belongs in `IdentificationInduction`,
which exposes exact success, failure, and unfinished traces for structural
induction.  The legacy engine's unrestricted formula-aligned success compiler
has since been refuted by the positive front-door regression; the local
certificates below remain proved, but cannot be assembled into that global
compiler.  `KernelSuccessCompilation` now targets `identifyJointKernel`
and its actual current expression by one complete fuel induction.
`KernelCompilation`, `ComponentCompilation`, `KernelRecursionCompilation`,
and `KernelProductCompilation` supply its supported branch constructors.
The remaining failure/countermodel work must likewise target the replacement
program.  The historical obligations were:

* success of `Legacy.identifyJoint` on a nonempty action implies a
  `DoCalculusDerivation` to the identified formula, hence a
  support-carrying `IdentificationCertificate`; the empty-action base
  case is `emptyActionIdentifiedPublishedCertificate`, whose formula is
  the ID output and whose derivation is marginalization of `P(V)`
  reindexed by `eqCongr` along the empty-action and `Y ∪ (V \ Y) = V`
  coverings;
  empty-action IDC inhabits `emptyActionPublishedConditionalCertificate`
  (Bayes `P(Y, Z) / P(Z)`) and
  `emptyActionIdentifiedPublishedConditionalCertificate` (engine formula
  via `emptyActionIdentifiedConditionalIdDerivation`);
  nonempty-action success unpacks to a nested identified run after
  ancestral restriction (`identifyFuel_eq_identified_of_shrink`), and
  shrink whose nested remaining misses the action is the empty-action
  base case on that ancestral set
  (`identifyFuel_eq_identified_of_shrink_empty`);
  when `Y` is path-d-separated from `X` in `G_{\overline{X}}`, rule 3
  deletes the action and empty-action ID supplies the observational
  marginal (`deleteActionIdentifiedPublishedCertificate`);
  an empty outcome is vacuously d-separated, so the same certificate
  inhabits `emptyOutcomeIdentifiedPublishedCertificate` and matches
  the empty-free-c-component engine output
  (`identifyJoint_eq_identified_of_empty_free`);
  the public structural trace's `emptyAction` and `emptyFree` constructors
  now compile directly to formula-aligned packages
  (`publishedJointSuccessLeafCompilation?`), rather than being rediscovered
  by a front-end query heuristic;
  the same d-separation plus two empty-action marginalizations onto
  `An(Y)_{G_{\overline{X}}}` inhabits
  `firstShrinkEmptyIdentifiedPublishedCertificate`, whose formula is
  the engine output of the first-shrink-empty branch
  (`identifyJoint_eq_identified_of_first_shrink_empty`);
  Boolean d-separation in `G_{\overline{X}}` unpacks to
  `deleteActionIdentifiedPublishedCertificate?` and
  `firstShrinkEmptyIdentifiedPublishedCertificate?`; empty action,
  empty outcome, or that same test inhabits
  `identifiedPublishedCertificate?`;
  empty-condition IDC reuses that packer
  (`identifiedPublishedConditionalCertificate?`), and empty-action IDC
  remains `emptyActionIdentifiedPublishedConditionalCertificate`;
  on the positive class, the same three IDC shapes (empty conditioner,
  rule-1 deletion, rule-2 exchange) also wrap
  `identifiedPublishedCertificatePositive?`, so consecutive 4.2 joints
  lift to conditionals
  (`identifiedPublishedConditionalCertificateFromPositiveJoint?`);
  nonempty 4.3 action shrink wraps the same IDC shapes through
  `identifiedPublishedCertificatePositiveWithShrink?`;
  the 4.2 chain-rule branch is `identifyFuel_eq_identified_of_chain`;
  singleton 4.2 whose topological predecessors contain the action
  inhabits `chainSingletonIdentifiedPublishedCertificate` as the engine
  formula `∑_{S \ Y} Q[S]` with `S = Y = {y}` (rule 1 inserts extra
  predecessors), unpacked on the
  positive class by `chainSingletonIdentifiedPublishedCertificate?`;
  consecutive two-vertex 4.2 inhabits
  `twoVertexIdentifiedPublishedCertificate`;
  independent product-split of a composite outcome inhabits
  `productSplitIdentifiedPublishedCertificate`; successive
  rest-versus-head factorization inhabits
  `productSplitAllIdentifiedPublishedCertificate` as `∏_v P(v | X)`;
  4.3 restriction and product-split success unpack by
  `identifyFuel_eq_identified_of_restrict` and
  `identifyFuel_eq_identified_of_product`;
  nonempty 4.3 whose nested query already has a positive-class
  certificate inhabits `shrinkActionIdentifiedPublishedCertificate`
  (rule 3 deletes `X \ H`; the engine host is `firstRestrictHost?`);
  stacked 4.3 restrictions recurse in
  `identifiedPublishedCertificatePositiveWithShrink?` along the
  strictly shorter action `X ∩ H`;
  4.3 whose nested host misses the action is
  `identifyFuel_eq_identified_of_restrict_empty`;
  the empty-free-c-component branch is
  `identifyFuel_eq_identified_of_empty_free`;
* Boolean hedge tests on some enumerated selection inside an ID failure
  (`failedHedgeSelection` is the most general vertex pair the failure
  record determines; the thinned forest is a further specialization).
  Search completeness already lifts any such selection to
  `hedgeWitness? = some _`.  ID failure yields a single remaining
  c-component (`identifyJoint_eq_failed`); the recorded free side is a
  self-c-component (`identifyJoint_eq_failed_free`); `closedForestChild`
  is well-formed and child-closed on that pair.  The failure cut
  `remaining \ free` is nonempty; disjointness from the original action
  and meeting `X` follow once the cut is the local action inside
  `remaining`.  Ancestral remaining sets yield `keptSinks ⊆ small` and
  `rootsReachOutcomeBool`; `hedgeTestsHold` therefore holds whenever
  `free = remaining \ (remaining ∩ X)` and the remaining set is ancestral
  of `Y` in `G_{\overline{cut}}`.  Immediate 4.1 hedges on the full graph
  (`hedgeWitness?_eq_some_of_failed_immediate`) inhabit that interface.
  So do full-remaining fails with `free = V \ X`
  (`hedgeWitness?_eq_some_of_failed_remaining_eq`) and first ancestral
  restriction when the fail remaining is that ancestral set
  (`hedgeWitness?_eq_some_of_failed_after_shrink`), first ancestral
  restriction then a nested product split on that ancestral remaining
  set (`hedgeWitness?_eq_some_of_failed_after_shrink_product`), first
  ancestral restriction then a nested product split then 4.3 onto the
  piece's containing c-component
  (`hedgeWitness?_eq_some_of_failed_after_shrink_product_restrict`), first
  ancestral restriction then a nested product split then 4.3 then a
  nested product split on that host
  (`hedgeWitness?_eq_some_of_failed_after_shrink_product_restrict_product`), first
  ancestral restriction then a nested product split then ancestral shrink
  of that piece
  (`hedgeWitness?_eq_some_of_failed_after_shrink_product_shrink`), first
  ancestral restriction then a nested product split then ancestral shrink
  then a nested product split
  (`hedgeWitness?_eq_some_of_failed_after_shrink_product_shrink_product`), first
  ancestral restriction then a nested 4.3 restriction
  (`hedgeWitness?_eq_some_of_failed_after_shrink_restrict`), first ancestral
  restriction then 4.3 then a nested product split
  (`hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product`), first
  ancestral restriction then 4.3 then a nested product split then 4.3
  (`hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_restrict`), first
  ancestral restriction then 4.3 then a nested product split then ancestral
  shrink
  (`hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_shrink`), first 4.3
  restriction when the fail remaining is the containing c-component
  (`hedgeWitness?_eq_some_of_failed_after_restrict`), first 4.3
  restriction then a nested product split on that host
  (`hedgeWitness?_eq_some_of_failed_after_restrict_product`), first
  4.3 restriction then a nested product split then 4.3 onto the piece's
  containing c-component
  (`hedgeWitness?_eq_some_of_failed_after_restrict_product_restrict`), first
  4.3 restriction then a nested product split then 4.3 then a nested
  product split on that host
  (`hedgeWitness?_eq_some_of_failed_after_restrict_product_restrict_product`), first
  4.3 restriction then a nested product split then ancestral shrink of
  that piece
  (`hedgeWitness?_eq_some_of_failed_after_restrict_product_shrink`), first
  4.3 restriction then a nested product split then ancestral shrink then
  a nested product split
  (`hedgeWitness?_eq_some_of_failed_after_restrict_product_shrink_product`), first
  4.3 restriction then a nested ancestral shrink
  (`hedgeWitness?_eq_some_of_failed_after_restrict_shrink`), and first
  4.3 restriction then shrink then a nested product split
  (`hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product`), first
  4.3 restriction then shrink then a nested product split then 4.3
  (`hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_restrict`), first
  4.3 restriction then shrink then a nested product split then ancestral
  shrink
  (`hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_shrink`).  Product-nested fails
  unpack by `identifyFuel_eq_failed_of_product` (top-level first-product
  uses that lemma) and instantiate a different local query
  (`identifyJoint_eq_failed_site`);
  if that site still agrees with `q` on the remaining vertices,
  `hedgeWitness?_eq_some_of_failed_site_agrees` lifts the hedge.  When
  the local outcome is the recorded free component,
  `hedgeWitness?_eq_some_of_failed_free_ancestral` lifts it from
  free-component ancestry plus ancestry of the original `Y` under
  `G_{\overline{X}}`, without requiring `cut ⊆ X`.  A first product
  split whose nested call never left the full graph, with free side the
  failing piece, lifts by that interface
  (`hedgeWitness?_eq_some_of_failed_after_product_of`); the unshrunk
  remaining-full case is
  `hedgeWitness?_eq_some_of_failed_after_product`, and if the recorded
  free side is already one of the listed pieces,
  `hedgeWitness?_eq_some_of_failed_after_first_product`.  If the nested call
  is itself an immediate 4.1 fail on that piece, the remaining/free
  record and free-component ancestry are those of the nested 4.1 site
  (`hedgeWitness?_eq_some_of_failed_after_product_immediate`).  Nested
  4.1 that first shrinks remaining, then fails immediately on that
  ancestral set, lifts once the smaller remaining set meets original
  `X` and is ancestral of original `Y` in `G_{\overline{X}}`
  (`hedgeWitness?_eq_some_of_failed_after_product_shrink_immediate`).
  Nested shrink whose recorded remaining set is that ancestral set, with
  free side the local `remaining \ X`, lifts without requiring an
  immediate 4.1 Boolean (`hedgeWitness?_eq_some_of_failed_after_product_shrink`).
  Nested shrink that then product-splits on that ancestral remaining set,
  with free side the failing subpiece, lifts by
  `hedgeWitness?_eq_some_of_failed_after_product_shrink_product`.
  Nested shrink then product then 4.3 onto the subpiece's containing host
  lifts by
  `hedgeWitness?_eq_some_of_failed_after_product_shrink_product_restrict`.
  Nested shrink then product then ancestral shrink of that subpiece lifts
  by
  `hedgeWitness?_eq_some_of_failed_after_product_shrink_product_shrink`.
  Nested shrink that then 4.3-restricts onto a containing host of that
  ancestral remaining set, with free side `host \ (V \ piece)`, lifts by
  `hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict`.
  Nested 4.3 restriction onto a containing c-component of the piece, with
  remaining/free the local remaining-eq equations on that host, lifts by
  the same interface (`hedgeWitness?_eq_some_of_failed_after_product_restrict`).
  Nested 4.3 that then fails as an immediate 4.1 hedge on that host lifts
  once the host meets original `X` and is ancestral of original `Y`
  (`hedgeWitness?_eq_some_of_failed_after_product_restrict_immediate`).
  Nested 4.3 that then product-splits on that host, with free side the
  failing subpiece, lifts by
  `hedgeWitness?_eq_some_of_failed_after_product_restrict_product`.
  Nested 4.3 then product then 4.3 onto the subpiece's containing host
  lifts by
  `hedgeWitness?_eq_some_of_failed_after_product_restrict_product_restrict`.
  Nested 4.3 then product then ancestral shrink of that subpiece lifts by
  `hedgeWitness?_eq_some_of_failed_after_product_restrict_product_shrink`.
  Nested 4.3 that then ancestrally shrinks on that host, with remaining
  the nested `An(piece)` and free side `remaining \ (V \ piece)`, lifts by
  `hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink`.
  These finite-depth cases are subsumed by
  `hedgeWitness?_eq_some_of_identifyJoint_failed`: its Type-valued trace
  induction transports arbitrary nested failures through shrink, restriction,
  and product frames without choice or a depth bound.
* the countermodel program for a `HedgeWitness` plus `ValueRich` targets a
  `CounterexampleIn` of the positive class, hence non-identifiability; the
  pair-root expansion
  `hedgeLatentExtension` (Boolean pair roots plus one private enumeration
  index per observed node) is the shared latent skeleton, and
  `hedgeModel` (empty parent mask `hedgeBaseModel`, full mask
  `hedgeCopyModel`) is a compatible, observationally positive embedding
  on that skeleton (`hedgeModel_mem_positive`);
  observational `QProb.Equiv` of any two masks is
  `hedgeModel_observationally_equivalent` (equal-weight pair-bit
  preimages); XOR-plus-uniform copies preserve interventional margins,
  so the query cell uses `hedgeMixModel` (pair-root XOR switches between
  copying a `ValueRich` parent label and the private decode), also
  compatible and positive (`hedgeMixModel_mem_positive`);
  under `do(X = second)`, odd action-parent parity together with an incident
  pair-root strictly increases the empty-mask mass of `Y = first` relative to
  the action-mask copy
  (`hedgeMix_interventional_first_mass_lt_of_parentParity`,
  `hedgeMix_interventional_first_not_equiv_of_parentParity`); the earlier
  unique-parent lemmas remain compatibility specializations; the generic
  parent-bit forms and `hedgeDoPivot` strengthen this again to any selected
  outcome with at least one directed action parent by assigning only one
  chosen parent `second`; singleton-outcome separation also keeps the model
  switch mask independent of the query action
  (`hedgeSingletonOutcome_not_valueEquivalent_of_parentBit`), so the
  singleton-mask specialization can alter just one useful action parent while
  the query still intervenes on every action coordinate;
  `hedgeSingleRootMixModel` localizes the switch itself to one pair-root while
  retaining the complete latent extension; it is compatible, strictly
  positive, and observationally equal across a singleton pivot mask whenever
  that root is incident to the pivot
  (`hedgeSingleRootMixModel_observationally_equivalent_singleton`); if the
  same root is incident to a queried child, the one-root mass gap yields
  `hedgeSingleRootSingletonOutcome_not_valueEquivalent`, eliminating all
  restrictions on other bidirected arms and outgoing pivot edges for a bow;
  observational agreement of the two mix masks is still required for a
  `CounterexampleIn` in general; an arbitrary action mask agrees with the
  empty mix when every edge leaving a masked vertex preserves pair-root
  incidence (`hedgeMixModel_observationally_equivalent_of_edge_shared_switch`),
  proved by induction over the graph's topological node order; the earlier
  seed-plus-sink condition is a specialization
  (`hedgeMixModel_observationally_equivalent_of_shared_switch`), and
  singleton action is the special case `hedgeMask_of_singleton`;
  unique-child bows are the special case
  (`hedgeMixModel_observationally_equivalent_of_bow`), and the same
  hypotheses inhabit `hedgeBowCounterexampleIn` in the positive class;
  composite-outcome cylinders split as a singleton coordinate times
  the complementary cylinder (`agreesOn_split_coord`); a shared-switch
  outcome that is any set of directed children of one seed is separated
  whenever that seed is their unique action parent
  (`hedgeChildren_not_valueEquivalent`); combining this with edge-wise
  observational agreement permits non-sink extra action vertices in
  `hedgeEdgeSharedChildrenCounterexampleIn`; the executable test and package
  are `hedgeWitnessEdgeSharedReady` and
  `hedgeEdgeSharedChildrenCounterexampleIn_of_ready`; the seed-plus-sink
  `hedgeSharedSwitchCounterexampleIn` remains a convenient specialization
  (`hedgeWitnessSharedSwitchReady` tests subset of those children and
  seed-or-sink extras, not a singleton action); the action-wide `second`
  assignment `hedgeActionReference`
  matches `hedgeDoSecond` without a singleton hypothesis
  (`hedgeDoSecond_eq_action_intervention`);
  `HedgeWitness` now stores `actionSeed`/`outcomeSeed` as data (member-list
  search, not `Exists` into `Type`), so a bow-shaped witness inhabits
  `hedgeBowCounterexampleIn_of_witness`; a pair-root incident to the
  outcome seed is `firstIncidentPairRoot`, and
  `hedgeBowCounterexampleIn_of_witness_any` recovers it from a Boolean
  `any`; unique mutual bidirected neighbourhoods are identical pair-root
  incidence (`hedgeIncident_eq_of_unique_bidirected`) and inhabit
  `hedgeBowCounterexampleIn_of_witness_unique_bidirected`;
  singleton action/outcome member lists name those seeds
  (`HedgeWitness.action_unique_of_members`,
  `HedgeWitness.outcome_unique_of_members`);
  a kept forest edge from the action seed to the outcome seed is a
  directed edge (`HedgeWitness.directed_of_forest_child`);
  Boolean bow tests on a witness are `hedgeWitnessBowReady`, and
  `hedgeBowCounterexampleIn_of_ready` inhabits the counterexample from
  those tests; shared pair-root switches at every directed child of the
  action seed are `hedgeWitnessSharedSwitchReady` /
  `hedgeSharedSwitchCounterexampleIn_of_ready` (the unique-child bow is
  the special case); `hedgeCounterexampleIn?` / `hedgeCounterexample?`
  package those as an `Option` from a witness or an ID-failure record;
  for the general hedge, `HedgeWitness.actionRoot` follows the stored child
  map to a common root and `actionBoundaryParent` / `actionBoundaryChild`
  select a concrete large-forest edge crossing into the small forest;
  `rootReadoutOutcome` reflects the witness's inductive root-to-outcome
  reachability back into the finite Boolean search and selects a concrete
  reachable query outcome for every forest root without choice;
  `rootReadoutRoute` computes corresponding duplicate-free directed routes,
  proves that their edges survive `G_{\overline{X}}`, and supplies
  deterministic predecessor maps; `rootReadoutSuccessor` resolves route
  intersections into a well-formed acyclic no-splitting routing forest whose
  sinks are query outcomes; `hedgeRoutingFlow_conservation` proves that any
  local XOR flow on this forest carries total hedge-root parity to total sink
  parity, and `exists_outcome_bit_of_rootReadoutFlow` extracts a queried sink
  carrying an odd readout without choice; `hedgeFlowReadoutModel` realizes
  that recurrence as graph-compatible mechanisms, while
  `rootFlowReadoutModel_sinkParity_doSecond` closes its end-to-end transport
  theorem under the query intervention; route-priority
  `forestChildPrioritize` composes either c-forest with that routing without
  splitting a stream when a route re-enters the hedge, and every resulting
  sink is still a query outcome; in fact, both compositions have exactly the
  same canonical sink set (`largeOutcomeFlowSinks_eq_rootReadoutSinks`,
  `smallOutcomeFlowSinks_eq_rootReadoutSinks`); `parityReadoutOutcome` and
  `parityReadoutRoute` retain the action-branch specialization;
  `largeReadoutParityModel` and `smallReadoutParityModel` then wrap the two
  parity models with graph-compatible mechanisms that copy the encoded bit
  along every indexed route edge;
  `hedgeXorPairBitsWithin` and `hedgeForestParentBitsFrom` restrict the two
  parity inputs to an arbitrary c-forest; `largeParityModel` and
  `smallParityModel` package the faithful unsoftened construction--the second
  model changes only nodes in `F'`, where it ignores pair-roots and kept
  directed parents outside `F'`; both are compatible and share a product
  prior, but no positivity claim is made for them; canonical roots for
  bidirected path edges and XOR superposition give
  `BidirectedComponent.pairBits_of_even_target`, and the exhaustive
  `evenTargetPairBits` turns that incidence-surjectivity proof into data
  without choice; XOR translation proves equal fiber counts for any two even
  component targets (`pairBitRealizers_length_eq_of_even`), while the finite
  handshaking identity `hedgeNodeXor_incidence` derives evenness for the
  incidence required by every actual large- or small-forest evaluation;
  `nestedPairBits_of_inner_even` further proves that the piecewise
  outer/small incidence map is surjective whenever its small restriction is
  even, and `nestedPairBitRealizers_length_eq_of_inner_even` proves all such
  targets have equal fibers by another explicit XOR permutation; explicit
  injections between the ordinary and nested zero kernels then yield the
  cross-map count `pairBitRealizers_length_eq_nested`; c-forest cancellation
  shows that the large and nested required targets are even simultaneously
  (`largeRequiredEven_iff_smallRequiredEven`), while odd targets have empty
  fibers; the same cancellation makes the action-free small model's common
  root parity identically even (`smallParityModel_rootParity_doSecond`) and
  reduces the large model's common-root parity exactly to its structural-
  equation defects on `F \cap X`
  (`largeParityModel_rootParity_eq_actionDefects_doSecond`); an explicit
  action-seed/root incidence vector then flips exactly one common-root output,
  proving constructively that some large-model latent assignment has odd
  total root parity (`exists_largeParityModel_rootParity_true_doSecond`);
  hence the odd common-root event has positive interventional mass in the
  large model and zero mass in the small model
  (`parityModels_rootParity_not_equiv_doSecond`), and event-to-kernel
  extensionality packages the unsoftened pair as an unrestricted-class
  `rootParityCounterexample` for the corresponding common-root query;
  `largeOutcomeFlowModel` and `smallOutcomeFlowModel` inject the respective
  c-forest incidence into the composed readout; the small sink parity is
  uniformly even, while the explicit action-seed/root toggle makes one large
  sink assignment odd; the common sink event is local to `q.outcome`, and
  `outcomeFlowModels_query_separated` proves that these combined models
  already disagree on the original kernel query;
  `hedgeCoordinateSupportLatents` factors complete latent assignments
  into pair-root and private coordinates, so every observed atom has the same
  number of equal-weight preimages and
  `parityModels_observationally_equivalent` proves full observational
  agreement of the unsoftened pair.  Establishing observational equivalence
  for the combined outcome-flow pair, then adding full-support noise without
  erasing its separation, remain hard steps--the tempting construction that
  merely gates a private decode by restricted pair parity already fails
  observational equivalence on the two-node bow;
  outcome vertices sit in their ancestral set in `G_{\overline{X}}`
  (`outcome_subset_ancestralSet`), so the nested shrink-empty summed
  blocks cover `V \ Y` (`first_shrink_empty_summed_eq`);
  `hedgeRecodeLatent` flips private indices by the parent-bit toggle of
  `mask` so that `hedgeRecode_eval` identifies the empty-mask evaluation
  of the recoded assignment with the masked evaluation of the original
  (`hedgeUnrecode_eval` is the dual well-founded identity);
* `KernelSuccessCompilation` now closes the structural success direction for
  the corrected current-kernel program.  Once replacement failure transport
  and the general positive original-query countermodel are closed,
  identifiability in the positive class can imply joint ID success.  General
  conditional reduction is also required before assembling
  `PublishedCompleteness (GraphModelClass.positive G)`.

No axiom of choice or excluded middle is used in the engine; the hedge
countermodel will pick the two `ValueRich` values by structure projection,
not by search through a `Prop`.
-/
```

