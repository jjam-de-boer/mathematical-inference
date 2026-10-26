# Lean project instructions

## Scope and main results

This project develops an MLTT-inspired finitary probability theory based on
Clayton, Pearl-style causality, and their integration in a simple mode theory.
Probability laws use finite rational weights; zero probabilities and explicit
support for conditionals are part of the framework.

The main implemented results are:

- Finite probability laws, named distributions, moments and related inequalities.
- Entropy and information inequalities, continuity, rational characterization
  and certified finite optimization.
- Soundness of the three do-calculus rules and supported derivations.
- Joint and conditional identification completeness for the stated positive
  model classes, original finite hidden-DAG transfer, and supported-zero
  certificates on their explicit used-conditional domains. Observed domains
  supply two distinct values; hidden and private-noise alphabets may be any
  finite size.
- Mode-indexed realizations connecting causal proofs to actual executions.
- Extensions including binary bow/instrumental-variable sharp bounds,
  fixed-law identification and attainable sets; finite model compression;
  supplied polynomial-certificate checking; and bounded formula selection.
- Exact attained bounds and point-identification tests for unconditional
  intervention events in the complete-bidirected finite hidden-DAG class,
  without fixed hidden-alphabet or rational-denominator bounds.
- Auxiliary constructive analytic values, including real arithmetic,
  logarithms, exponentials and differentiation with explicit error control.
  Probability weights remain finite and rational.
- Observational and interventional Shannon entropy of original hidden-DAG
  assignment records: identifying an entire law identifies its entropy.
  Shannon inequalities are sound exclusion tests, not substitutes for a
  Bayesian graph posterior or Körner graph entropy. Remaining uncertainty
  among a finite catalogue of graph hypotheses, given data and supplied
  identifiability, is Shannon entropy of that catalogue; it does not run
  ID/IDC and is not a graph posterior.

## Living-document maintenance

Keep this file concise and current when important results, useful lessons
from unsuccessful approaches, or project instructions change. Consolidate
or remove outdated entries rather than continually appending details.

**Every edit to this file requires prior explicit user approval.**
Show the exact proposed changes in chat and wait for approval before
applying them. This applies to all sections, including achieved results,
failed approaches, build commands and working rules. Approval of a task
does not constitute approval of future edits to this file.

When starting and finishing work that changes this file, notify the other
active project agents. Distinguish proposed changes from approved changes.
After applying approved changes, send the changed guidance and ask the
affected agents to reread this file.

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

## Structure, comments and documentation

The main entry points are `Thesis.Probability`, `Thesis.Causality` and
`Thesis.CausalTransport`. Use focused foundational imports in implementations;
keep graph/probability foundations below semantic proof assemblies, and do not
use examples as production foundations.

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

Use the appropriate status:
- **Refuted:** a checked counterexample disproves the stated claim.
- **Unresolved:** the attempt did not finish; the claim may still hold.
- **Resource-limited:** checking exceeded tested resources.
- **Superseded:** another approach replaced the old development.

An unfinished proof or timeout is not a disproof. A counterexample to one
construction does not refute the broader theorem. Keep entries concise,
consolidate overlaps, and request approval before changing this section.

- **Refuted — the old identification recursion.** On a positive front-door
  example, its returned formula evaluates to `9/16`, while the causal query
  has value `1/2`. Evidence: `Thesis.Examples.IdentificationRegression`,
  particularly `legacyEngineFormula_not_equivalent`. Revisit only after
  changing the incorrect recursion.

- **Refuted — unconditional composition from matching kernel metadata.**
  Matching formula-status and conditional-demand metadata does not justify
  a proof detour through an undefined conditional. Evidence:
  `Thesis.Examples.NativeKernelInterfaceObstruction`,
  particularly `conditional_demand_does_not_compose` and
  `carrier_detour_rejected`. Revisit with an argument accounting for support
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
  A valid hedge exists for which even the exhaustive alternative-route
  search finds no member of that family. Evidence:
  `Thesis.Examples.HedgeCarrierRouteObstruction`,
  particularly `no_carrier_route_coverage` and
  `no_outer_avoiding_routes_for_any_hedge_selection`. This limits that
  construction, not published completeness. Revisit only with a changed
  construction or coverage condition.

- **Refuted — same-type incoming cut as independent fair noise.** On a
  deterministic copy with degenerate child noise, `cutIncoming` yields
  observational entropy 1, not 2. Evidence:
  `Thesis.Examples.CausalEntropy.cutIncoming_not_independent_fair`. Extra
  randomness requires a different noise type, not `withMechanism`.

## Builds and checks

Use the installed toolchain pinned by `lean/lean-toolchain`. From the
repository root, run the helper tests:

```sh
python3 -B -m unittest discover -s lean/tools -p 'test_*.py'
```

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
