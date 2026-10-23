# Mathematical inference: science and logic

This repository holds Jelmer de Boer's *Mathematical inference: science and
logic*: the Master's thesis in Artificial Intelligence submitted to the Open
University in 2026, and a book manuscript based on that thesis.

The work develops a finite, constructive account of mathematical inference,
connecting probability, Pearl-style causal models and explicit epistemic-state
changes. Selected constructions and proofs are checked in Lean 4.

## Read the texts

- [Submitted thesis](latex/Thesis_Jelmer_de_Boer.pdf)
- [Book manuscript](latex/mathematical_inference.pdf)

## Lean development

The probability framework uses finite rational records, permits zero masses,
and retains explicit support for conditional probabilities. It includes named
distributions, entropy and certified rational optimization, causal ID/IDC
soundness and completeness with their stated qualifications, and modal
integration. Auxiliary analytic values do not change the probability weights.

Public entry points are `Thesis.Probability`, `Thesis.Causality` and
`Thesis.CausalTransport`. The tenure-track example combines these components.

There are three canonical Lean documents, kept together:

- [Agent and build instructions](lean/AGENTS.md): policy, safe local commands,
  verification and the current maintenance ledger.
- [Mathematical reference](lean/REFERENCE.md): theorem coverage, assumptions,
  distribution/entropy details, research boundaries and source reading order.
- [Historical evidence](lean/HISTORY.md): preserved development records and
  measurements, clearly separated from current instructions.

## Build and verify

Use the installed toolchain selected by `lean/lean-toolchain`. There are no
third-party Lake dependencies. Ordinary native builds need no Python wrapper:

```sh
cd lean
export LEAN_NUM_THREADS=1
lake build
lake build Thesis.AxiomAudit
lake build Thesis.ConstructiveAlgebraAudit
lake build Thesis.DistroAxiomAudit
```

Run only one build at a time. The native route has the committed per-compiler
limits, not an aggregate-memory or wall-time watchdog; the
[operating guide](lean/AGENTS.md#builds-and-checks) documents the monitored option.

The transitive axiom policy permits only `propext` and `Quot.sound`.
Compilation alone does not establish that policy. CI checks complete builds,
regressions and all audit gates for the exact published checkpoint.

## Soundness and completeness boundaries

The three do-calculus rules are proved sound under the derivation's local
support. Positive-class joint/conditional completeness and original finite
hidden-DAG countermodels are constructed, with two supplied distinct observed
labels and arbitrary finite hidden/private-noise alphabets.

The supported-zero package is also inhabited. Its formulas apply on their
explicit used-conditional domains; conditional targets additionally require
their original causal conditioner. Undefined values are not completed by
assigning `0 / 0 = 0`.

These results do not assert universal alternative-formula applicability,
unrestricted fixed-observed-law identification, or general multiworld
counterfactual completeness. See the [precise theorem coverage](lean/REFERENCE.md#causal-results).
