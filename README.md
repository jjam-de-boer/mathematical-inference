# Mathematical inference: science and logic

This repository holds Jelmer de Boer's *Mathematical inference: science and
logic*: the Master's thesis in Artificial Intelligence submitted to the Open
University in 2026, and a book manuscript based on that thesis.

The work develops a finite, constructive account of mathematical inference,
connecting probability, Pearl-style causal models and explicit epistemic-state
changes. Selected constructions and proofs are checked in Lean 4.

## Read the texts

- [Submitted thesis](documents/thesis/Thesis_Jelmer_de_Boer.pdf)
- [Book manuscript](documents/book/mathematical_inference.pdf)

## Repository layout

```text
code/
  lean/               Lean formalisation and build tools
  agda/               Reserved for future Agda development
documents/
  thesis/             Submitted Master's thesis
  book/               Mathematical inference book manuscript
  papers/             Reserved for future papers
```

## Lean development

The probability framework uses finite rational records, permits zero masses,
and retains explicit support for conditional probabilities. It includes named
distributions, entropy and certified rational optimization, causal ID/IDC
soundness and completeness with their stated qualifications, and modal
integration. Auxiliary analytic values do not change the probability weights.

Public entry points are `Thesis.Probability`, `Thesis.Causality` and
`Thesis.CausalTransport`. The tenure-track example combines these components.

The [Lean project instructions](code/lean/AGENTS.md) describe the current
results, assumptions, research boundaries and safe build commands. Source
reading guidance is also provided in the public entry-point modules.

## Build and verify

Use the installed toolchain selected by `code/lean/lean-toolchain`. There are no
third-party Lake dependencies. From the repository root, run the helper tests:

```sh
python3 -B -m unittest discover -s code/lean/tools -p 'test_*.py'
```

Then build and audit the Lean project:

```sh
cd code/lean
export LEAN_NUM_THREADS=1
lake build
lake build Thesis.AxiomAudit
```

Run only one build at a time. The native route has the committed per-compiler
limits, not an aggregate-memory or wall-time watchdog; the
[operating guide](code/lean/AGENTS.md#builds-and-checks) documents the monitored option.

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
counterfactual completeness. See the [current results and qualifications](code/lean/AGENTS.md#scope-and-main-results).
