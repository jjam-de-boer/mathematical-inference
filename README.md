# Thesis

This repository is organized into three working areas:

- `lean/`: Lean source and Lake project files. Lean source/configuration is tracked by git; downloaded dependencies, build outputs, and Lake cache state are ignored.
- `latex/`: LaTeX working directory. The local source/build files are ignored; `latex/main.pdf` is the tracked final thesis PDF.
- `papers/`: local scientific paper library. The extracted paper folders are ignored by git. The `fraud.zip` and `fraud_two.zip` archives are merged locally into `papers/fraud/`.

Zip archives are not tracked.

## Lean formalisation

The Lean project is self-contained apart from the pinned Lean toolchain and
Lean's `Std` library; `lean/lake-manifest.json` declares no third-party
packages.  The three stable entry points are:

- `Thesis.Probability` for finite constructive probability;
- `Thesis.Causality` for intrinsic finite SCMs, modal edits, and
  counterfactual semantics; and
- `Thesis.CausalTransport` for the finite-source correspondence and the
  explicit interfaces to externally published causal results.

From `lean/`, run `lake build` to check the public development.  The focused
constructive-extensional audit is intentionally separate, because it prints
its results rather than supplying program code:

```sh
lake env lean Thesis/AxiomAudit.lean
```

The audit checks representative probability, causal, transport, modal, and
example declarations.  It is expected to report only `propext` and
`Quot.sound` (or no axioms) for that surface.  It does not turn external
completeness, global-Markov, or d-separation-equivalence results into Lean
axioms: those results are explicit parameters in the transport interfaces.
