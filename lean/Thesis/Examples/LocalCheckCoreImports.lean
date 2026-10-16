import Thesis.Probability.Core

/-!
# Probability-core import-only resource baseline

There are deliberately no declarations after this import. Reuse of the core
must first pass the isolated helper's cache-validation gate. Compare this case
with `LocalCheckBaseline`, `LocalCheckDefinition` and `LocalCheckFiniteDecision`
to distinguish importing an environment from checking different new terms.
Only the selected fixture is compiled, never its missing or stale dependencies.
-/
