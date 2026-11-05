# Lean project instructions

## Scope and main results

This Lean 4 library is a constructive (Martin-Löf type theory) finitary
probability theory: finite rational weights, explicit zeros, and
support-aware conditionals. Qualitative probability follows
Clayton–Waddington finite-urn ratios; causality follows Pearl (structural
causal models and the three do-calculus rules). A finished public mode is
an SCM plus current belief; compact intervention and the modal stack stay
on workspace records.

The main implemented results are:

- Finite probability laws, named distributions, moments and related inequalities.
  Explicit node-law recipes generate rational tables. A table may be a node's
  independent noise, or one table at each listed parent configuration of a
  child, giving the local kernel P(child | parents). Constraint recipes
  return certified feasibility or refutation. If any listed parent
  configuration is infeasible there is no kernel and no invented fallback
  row. Recipes do not identify a joint from observations and do not
  construct a graph posterior.
- When every graph parent configuration of a child is listed and the
  tables exist, those rows are the child's mechanism: independent noise
  per node, no extra confounding. Given parents = pa, the child's law
  is that row, zeros included. A missing graph parent configuration
  yields no model, not a uniform or maximum-entropy default.
- Entropy and information inequalities and continuity; Shannon characterization
  from explicit uncertainty requirements on finite rational vectors, recorded
  in exact logarithms (`ExactLog`).
  Constructive ideal maximum-entropy existence and uniqueness, and certified
  exactly feasible rational approximation. Selecting maximum entropy remains a
  further inference principle.
- Finite microcanonical, canonical and grand-canonical ensembles, physical
  degeneracy corrections and heat/work variation.
- Under explicit equilibrium, temperature calibration and a uniform Clausius
  heat-temperature law, independently specified thermodynamic entropy agrees
  with statistical entropy up to a reference constant along admitted
  quantitatively regular positive probability paths.
- Soundness of the three do-calculus rules and supported derivations.
  Once those identities hold numerically for a finite SCM, they also hold
  as qualitative equality of supported interventional conditionals, by
  the Clayton–Waddington fact that finite-urn comparisons are cell-count
  ratios.
- Number-free comparison of experimental claims (a hard intervention
  together with an observed event), with order axioms and effectiveness:
  after `do(X{=}x)`, the event `X{=}x` matches every-outcome. Every
  finite SCM induces such a comparison from its interventional laws.
  The three do-rules then hold of that inducing SCM as qualitative
  equalities of supported conditionals; d-separation is used in the
  proof, not as an assumption of the comparison, and not as a second
  identification engine. This is not causality from qualitative axioms
  (Clayton recovers probability ratios from event comparisons). The
  unrestricted converse, that every such comparison on two Boolean
  nodes arises from some finite SCM, is false: an indiscrete scale
  (everything equivalent) satisfies those order and effectiveness
  axioms and cannot match empty versus sure under any positive urn.
- Qualitative causal comparisons reuse Clayton at each hard intervention
  (each fixed `do` is a finite urn of observed assignments), together
  with effectiveness; invariance of claims that mention only non-effects
  of the knobs being set; and the sentence that once every direct cause
  of a node is set, two experiments that set those causes to the same
  values and do not set the node itself make the same claims about that
  node. Direct causes are the signature's directed edges. For a finite
  SCM those sentences are corollaries of the existing evaluation, not a
  new calculus: `do` keeps the hidden prior and skips a forced node's
  mechanism; an unforced node prints from current parent values and the
  hidden factors wired to it, so children are recomputed from those
  writings. The three do-rules are not assumptions of this comparison
  and are not proved from these sentences for an arbitrary model of
  them; they remain theorems of an inducing SCM, as qualitative
  equalities of supported conditionals, as above. Every finite SCM
  induces such a scale. Supported kernel conditionals stay undefined
  when the conditioner has zero mass, and are not completed to zero.
  Completeness, that every finite model of the scale is realized by
  some finite SCM, is not proved. This is not causality from urn
  axioms, and not a new identification engine.
- Joint and conditional identification completeness for the stated positive
  model classes, original finite hidden-DAG transfer, and supported-zero
  certificates on each formula's used-conditional domain (the primitive
  tests that formula actually performs). Completeness uses hedge
  countermodels (Pearl–Shpitser forest obstructions); a restricted
  route-ready hedge family is not universal. Observed domains supply two
  distinct values; hidden and private-noise alphabets may be any finite size.
- A supplied partition of a child's labels on which that kernel is
  constant equates those singleton probabilities. Dropping a conditioner
  the kernel does not distinguish is a rewrite of the query, licensed by
  that same-kernel fact. If identification succeeds on both the original
  and the rewritten query, then on any model and reference where that
  same-kernel license holds, the identified values agree. Failure of the
  original is not rewritten into success. The partition is supplied, not
  inferred from data. Completeness still needs two observed values per
  node and support of used conditionals; merging equivalent labels does
  not transfer those hypotheses. This rewrite does not select a unique DAG.
- Finite causal coarse-graining merges disjoint observed-node clusters with
  explicit, possibly partial, intervention maps. The AND/copy example
  preserves full laws on every unique-preimage surgery; AND/swap data
  construct the merge. Exact maps compose along a depth-capped three-grain
  chain. An event-wise rational remainder compares declared interventional
  laws: exact comparisons have zero remainder on every event; the matched
  OR macro has remainder `2/3` (micro probability `1`, macro `1/3`).
  A separate constructor adds coarse-only coordinates. Forcing the new
  coordinate has no representative under its declared micro lift, although
  either coordinate value can occur. Model-pair exactness alone does not
  transfer identification between whole graph model classes. A positive
  Boolean copy-aggregation is exact on every micro intervention, with
  representatives on whole clusters for every macro action, yet the fine
  query is identified and the merged confounded-arrow graph has a hedge
  (a forest witness of non-identifiability). This example permits declared
  shared noise ignored by the actual equations. A catalogue client compares
  actual fine/coarse SCMs with declared protocols and complexity priors.
  These results do not establish a general renormalization-group flow or
  a physical length scale.
- Three nested support-aware relations on finite SCMs. Observational
  agreement is equality of the actual joints, zeros included: a
  conditioner undefined in one joint and defined-zero in the other
  already disagrees. Interventional agreement is equality of
  `P(· | do(a))` on a declared family of hard interventions. Exact
  abstraction is a (possibly one-way) preservation of the full finite
  law along an assignment map, using a partial map ω from micro to
  macro interventions; a `none` entry excludes that micro surgery.
  Exact ω implies interventional agreement on the image of ω; empty
  `do` is observational agreement when it is in that image. Converses
  fail: an observationally matched OR merge of two parents still gives
  macro `1/3` versus micro double-surgery `1`; a copy-chain (`Y` copies
  `X`) can share the observational joint with a bow (confounded `X→Y`)
  and still disagree on `P(Y | do(X))`. This is not classical Markov
  equivalence and does not recover a unique DAG.
- Public finished modes are an SCM plus current belief. Compact `do` (the
  workspace intervention field) and the modal stack live only on workspace
  records. Public 1-cells (edit morphisms) wrap existing operations that
  keep compact `do` empty. Mode-indexed realizations connect identification
  proofs to those executions: the proof can be run; they do not say which
  interventions the mode may perform. Identification of a query may also be
  restricted to a mode's declared allowed interventions, supplied as data,
  not read off the belief table and not taken from compact `do`. A query
  can be identified from the graph and still unaskable in that mode. That
  restriction of the query language is not a hedge (a Pearl–Shpitser
  non-identifiability witness), not a completeness theorem for all modes,
  and not a posterior over graphs.
- Sharp bounds for binary bow queries (confounded `X→Y`), and complete
  rational attainable sets for binary instrumental-variable treatment
  risks and the signed average treatment effect.
- Finite structural representation of a fixed DAG or a projection, not a
  general decision procedure for arbitrary rational weights.
- Exact checking of supplied polynomial bound certificates, and exact
  feasibility and coordinate classification for integer linear equations
  over natural unknowns, with no supplied cutoff. Feasibility computes a
  solution or proves infeasibility. If there is no natural solution, that
  is reported first. Otherwise each selected coordinate is either bounded,
  with a computed solution and an explicit (not necessarily least) bound,
  or unbounded, with a computed base and a nonnegative integer solution
  `h` of the homogeneous equations `A h = 0` that increases that
  coordinate. A successful supplied Petri-net firing word still runs from
  any source with at least as many tokens in each place, reaching the old
  endpoint plus those extra tokens. For each transition and target there
  is a least one-step source that can cover the target; overshoot is
  allowed, exact arrival is not claimed. These procedures do not decide
  Petri-net reachability: firing counts may solve the token-balance
  equations while no actual firing word exists from that marking.
- Exact undefined/zero/positive support analysis for the current formula and
  guard languages, finite causal support-profile coverage, and checked bounded
  proof enumeration and formula selection. A supplied checked query trace
  reconstructs an existing certificate; it does not decide that a witness
  exists.
- Exact attained bounds and point-identification tests for unconditional
  intervention events in the complete-bidirected finite hidden-DAG class
  (every pair of distinct observed nodes is confounded), without fixed
  hidden-alphabet or rational-denominator bounds. Supported conditional
  queries also have exact attained ranges and witnesses for every
  intermediate rational value; evidence support is reported separately.
- Auxiliary constructive analytic values, including real arithmetic,
  logarithms, exponentials and differentiation with explicit error control.
  Probability weights remain finite and rational.
- Observational and interventional Shannon entropy of original hidden-DAG
  assignment records: identifying an entire law identifies its entropy.
  Shannon inequalities are sound exclusion tests.
- Finite Bayesian inference on a catalogue of templates: update a named
  finite-law (`Distro`) prior from observational or interventional finite
  tables, then mix identified values and supplied bounds without collapsing
  disagreement. An exhausted catalogue is unsupported, not a unique DAG.
  Complexity scores are prior mass only. A supplied map of assignments may
  zero an atom (a catalogue hypothesis) that would otherwise match those
  tables. Gating only the observational joint still accepts a copy-chain
  (`Y` copies `X`) whose `P(V)` is invariant under flipping both bits;
  requiring the same map on every experiment, including `do(X)`, rejects
  that chain. Graph-tagged atoms may be kept or dropped one observed graph
  at a time under a supplied node permutation; templates of one hidden DAG
  still share that graph, so that filter is all-or-nothing. Swapping the
  two nodes of a binary bow (confounded `X→Y`) is not a directed-graph
  permutation. An optional depth-capped Boolean partition tree mixes
  already-certified answers; it does not search graphs or identify a query
  left unidentified. This is not a Bayesian posterior over graphs, and it
  is distinct from Shannon entropy of the remaining compatible graphs on
  the same catalogue.
- A declared finite family of hard interventions (set some coordinates
  to a value; empty `do` is observation), optionally the host's full
  finite list with an explicit cap on number of targets, can be searched
  by increasing subset size. That returns a shortest subset that pairwise
  separates listed generative SCMs, with no shorter subset of the same
  family, or reports an inseparable pair with the same predicted laws on
  that family. This is not a unique DAG and not constraint-based graph
  search from conditional independences.

## Living-document maintenance

Keep this file concise and current when important results, useful lessons
from unsuccessful approaches, or project instructions change. Consolidate
or remove outdated entries rather than continually appending details.
Results bullets are theorem-level claims and their qualifications, not
module APIs. Pitfall entries are only approaches another agent might
repeat: status, evidence module, and what would justify revisiting.

This file must stay self-contained. A new agent on a new task should
understand the results, pitfalls and working rules from these pages
alone, without the Lean facades, the thesis text, or extra Markdown.
When a name is required, gloss it in the same bullet (what it is, and
what it is not). Do not add a glossary, a diary, or a second brief.

**Every applied edit to this file requires prior explicit user approval.**
Show the exact proposed changes in chat and wait for approval before
applying them. This applies to all sections. Approval of a task does not
constitute approval of future edits to this file. Distinguish proposed
changes from approved changes.

**Before treating landed work as done** (including marking a `/goal`
complete), either show a short proposed diff for this file, or state
`No AGENTS.md change.` Do not treat the work as done until that proposal
or that sentence is in the same turn. Propose an update when a main
result, scoped refutation, superseded approach, or working rule changed;
rewrite or merge an existing bullet rather than appending a sibling.
Add or rewrite a results bullet only for a theorem-level claim and its
qualifications. Add a pitfall only for a substantive approach another
agent might repeat: one status, one evidence module, and what would
justify revisiting. If the finding is a limit of a published result,
merge it into that result rather than opening a sibling pitfall.

Optional: if other project agents are active, after an approved edit tell
them in chat to reread `lean/AGENTS.md` and quote the approved change.

## Mathematical and working principles

- Only `propext` and `Quot.sound` are permitted transitive kernel axioms.
  No choice, general propositional excluded middle, `sorryAx`,
  `Lean.ofReduceBool` or additional assumed axiom. Supplied finite
  decidability and Boolean/Nat case analysis are allowed.
- Preserve the main results and their meaning, not every historical proof
  script or helper. Prefer shorter, clearer proofs when they establish the
  same result. Obsolete proofs may be removed after checking retained
  end-results and callers; update affected tests to reflect the justified
  replacement rather than freezing the old proof text.
- Do not silently weaken conclusions, add assumptions, or lose supported-zero
  cases or computational guarantees.
- Stay within the requested task. Small supporting extensions to existing
  files are welcome when they are necessary and well justified; ask before
  materially expanding the mathematical scope.
- Read the relevant implementation, question incorrect proposals, clarify
  genuinely unclear tasks, and double-check both changes and conclusions.
- Preserve concurrent changes.
- Distinguish completing an agreed investigation from proving its unresolved
  mathematical claims. State open questions explicitly.

## Structure, comments and documentation

The main entry points are `Thesis.Probability`, `Thesis.Causality` and
`Thesis.CausalTransport`. Use focused foundational imports in implementations;
keep graph/probability foundations below semantic proof assemblies, and do not
use examples as production foundations.
Keep current identification implementations independent of historical
completeness facades; reuse the extracted graph/search foundations.

Kernel axiom policy lives under `Thesis.AxiomPolicy.*` (audit-only; never
import those modules from production or examples). Prefix wrappers walk
`Thesis.Probability.Distros`, the rest of `Thesis.Probability`,
`Thesis.Causality`, `Thesis.CausalTransport`, and the root `Thesis`
facade plus `Thesis.Examples` and coverage. `Thesis.AxiomAudit` collects those wrappers; it does not run a
second full-tree axiom walk. Add a prefix audit only when a substack is
independently imported and worth checking before the next layer. Every
`Thesis.*` production or example module maps to exactly one owning prefix.
Do not add a prefix per long file or per theorem family, and do not add
Entropy, Soundness, Completeness, or Hedge audits.

Comment mathematical purpose, assumptions, support conditions and important
constructive invariants clearly. Keep implementation details with the code;
this file should summarize main results, not enumerate intermediate lemmas.

## No extra documentation files

**Do not recreate separate reference documents, progress diaries or
completed-task ledgers.**

## Known pitfalls and unsuccessful approaches

Record substantive approaches that future agents might otherwise repeat,
not individual failed tactics or temporary compiler errors. Each entry
should state its scope, evidence and what would justify revisiting it.
State each claim so a new agent can check it directly against the cited
module. Gloss any name the claim needs; do not rely on another document
or on undeclared identifiers to explain the obstruction.

Use the appropriate status:
- **Refuted:** a checked counterexample disproves the stated claim.
- **Unresolved:** the attempt did not finish; the claim may still hold.
- **Resource-limited:** checking exceeded tested resources.
- **Superseded:** another approach replaced the old development.

An unfinished proof or timeout is not a disproof. A counterexample to one
construction does not refute the broader theorem. Keep entries concise,
consolidate overlaps, and request approval before changing this section.

- **Refuted — the old identification recursion.** On a positive front-door
  graph (`X→M→Y` with confounding of `X,Y`), its returned formula evaluates
  to `9/16`, while the causal query has value `1/2`. Evidence:
  `Thesis.Examples.IdentificationRegression`.
  Revisit only after changing the incorrect recursion.

- **Refuted — unconditional composition from matching kernel metadata.**
  Matching formula-status (undefined/zero/positive) and conditional-demand
  tables does not justify a proof detour through an undefined conditional.
  Evidence: `Thesis.Examples.NativeKernelInterfaceObstruction`.
  Revisit with an argument accounting for support
  at the active intermediate references; other reconstruction strategies
  are not ruled out.

- **Superseded — fixed-depth failure unpacking as a completeness strategy.**
  Adding further branch nests does not establish the general theorem.
  Current failure extraction handles arbitrary recursion, and the completed
  completeness assembly supplies actual countermodels. Evidence:
  `Thesis.CausalTransport.KernelFailureExtraction` and
  `Thesis.CausalTransport.HedgeChannelCompleteness`. A bounded helper may
  still be useful when required by a concrete caller.

- **Refuted — universal coverage by the tested route-ready hedge family.**
  A hedge is a Pearl–Shpitser forest witness of non-identifiability. The
  tested family requires extra routing hypotheses. A valid hedge exists
  for which even exhaustive alternative-route search finds no member of
  that family. Evidence: `Thesis.Examples.HedgeCarrierRouteObstruction`.
  This limits that construction, not published completeness. Revisit only
  with a changed construction or coverage condition.

- **Refuted — directed-parent channel family as universal conditional
  countermodels.** Every typed small/background parent signal of the
  independent-channel installation can agree on a conditional kernel,
  while a shared-latent pair on the same graph refutes identifiability.
  Evidence: `Thesis.Examples.HedgeChannelLatentBoundary`.
  This limits that construction, not published completeness. Revisit only
  with a changed signal family or coverage condition.

- **Refuted — same-type incoming cut as independent fair noise.** On a
  deterministic copy with degenerate child noise, cutting one parent at
  the same noise type (`cutIncoming`) yields observational entropy 1, not 2.
  Same-type randomization (`randomizeWith`) stays at 1 bit as well.
  Evidence: `Thesis.Examples.CausalEntropy`.
  Extra randomness requires a different noise type, not a same-type
  mechanism rewrite.

- **Refuted — support-only fixed-law classification and finite concrete
  catalogues of every attainable value.** Compatible positive IV laws with
  identical observed support can disagree on point identification. At one
  fixed bow law, an actual model realizes a target value outside any finite
  list of fully weighted models. Evidence:
  `Thesis.Examples.SupportOnlyIdentificationObstruction` and
  `Thesis.Examples.SharedResponseConditionalRanges`. Parameterized structural
  catalogues, endpoint methods and general procedures using rational masses
  are not refuted. Revisit with numerical information or a weaker coverage claim.

- **Refuted — rational constraint data guarantee a rational ideal entropy
  optimizer.** The feasible three-state mean-½ problem has a unique auxiliary
  real optimum that no rational compatible law attains. Evidence:
  `Thesis.Examples.EntropyMeanHalfDiscriminant`.
  Exactly feasible rational approximations and certificates remain available.
  Exact rational attainment requires additional proved hypotheses.

- **Refuted — unrestricted zero-class success equivalence.** Guarded joint ID
  can succeed on an unconfounded `X -> Y` while `do(X)` at an unobserved action
  value is not identified in the class of all finite hidden-DAG models (zeros
  allowed). Evidence: `Thesis.Examples.GuardedHiddenDAGZeroBoundary`. The
  support-qualified soundness/completeness package is unaffected. Revisit
  only with a changed zero-class claim.

- **Refuted — primitive/external action tests as a zero-class repair.**
  Guarded joint ID can succeed on a front-door graph where both models
  have positive observed action probability everywhere, yet `do(X)` is
  still not identified. Evidence:
  `Thesis.Examples.AdmissibleFrontDoorBoundary`.
  Used-conditional qualifications of the printed formula remain essential.
  The support-qualified package is unaffected. Revisit only with a changed
  admissible-domain claim.

- **Unresolved — universal alternative-formula coverage and stopping.**
  Checked search is complete within its declared expression/proof bounds.
  Finite support profiles and local proof replacement do not yet supply a
  universal bound or terminating saturation theorem. Evidence:
  `Thesis.CausalTransport.NativeBoundedSelection` and
  `Thesis.CausalTransport.NativeDerivationReplacement`. Revisit with a
  support-preserving coverage and termination argument.

- **Unresolved — unrestricted arbitrary-graph fixed-law rational identification.**
  Projection-wide finite structural coverage leaves rational weights unbounded.
  Restricted-class and bounded-model procedures do not decide the general case.
  Evidence: `Thesis.CausalTransport.ProjectionTemplateRepresentation` and
  `Thesis.Probability.IndependentBooleanObstruction`; the latter is a
  fixed-mechanism obstruction, not graph-wide impossibility. Revisit with a
  proved rational feasibility/uniqueness procedure or an impossibility reduction
  for the stated causal model class.

## Builds and checks

Use the installed toolchain pinned by `lean/lean-toolchain`. From the
repository root, run the helper tests:

```sh
python3 -B -m unittest discover -s lean/tools -p 'test_*.py'
```

These Python tests do not run Lean. Update them only with the matching source
or helper change; they are not a proof or axiom gate.

Ordinary native builds need no Python wrapper. **Mandatory publish** is
those tests plus two sequential Lake commands:

```sh
cd lean
export LEAN_NUM_THREADS=1
lake build
lake build Thesis.AxiomAudit
```

`lake build` compiles the ordinary library (`Thesis`, `Main`, and the
rest of the default Lake target). `Thesis.AxiomAudit` is the collection
gate: it imports the prefix audits, extra coverage, and the removed-ID-name
check. Kernel axiom policy is the union of those prefix scans (private
proofs included). Distros is compiled as part of ordinary `lake build`;
`Thesis.AxiomPolicy.Distros` only adds the axiom walk for that prefix.

The optional monitored full build, from the repository root, is:

```sh
python3 -B lean/tools/build_local_sequential.py --profile extended --check
```

That helper still only final-gates `lake build` and `Thesis.AxiomAudit`.
For a targeted check with its prerequisites, including an optional
substack axiom prefix that is **not** a publish gate:

```sh
python3 -B lean/tools/build_local_sequential.py --profile extended --phase lean --target Thesis.CausalTransport.Soundness --check
python3 -B lean/tools/build_local_sequential.py --profile extended --phase lean --target Thesis.AxiomPolicy.Distros --check
```

Replace `Thesis.AxiomPolicy.Distros` with `Thesis.AxiomPolicy.Probability`,
`Thesis.AxiomPolicy.Causality`, `Thesis.AxiomPolicy.CausalTransport`, or
`Thesis.AxiomPolicy.Examples` as needed.

Run one compiler family at a time. Use the existing resource limits; ask before
raising them, clearing shared caches or stopping another agent's build. The
monitored route adds memory/time safeguards that ordinary Lake does not.

Check affected modules first. Before publishing Lean changes, run the helper
tests, `lake build`, and `lake build Thesis.AxiomAudit` for the exact
checkpoint. Compilation alone does not establish the axiom policy. Inspect
the final diff and preserve concurrent work when committing or pushing.
