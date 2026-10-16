import Thesis.Probability.Core

namespace Thesis.Examples.LocalCheckBaseline

/-!
# Minimal probability-core import baseline for capped local checks

This fixture has no finite search, transportation recursion or causal graph
construction. Its sole proof applies an existing reflexivity theorem. Checking
it against a validated cached core distinguishes the import/kernel baseline
from elaboration of a substantial new proof. It is a resource diagnostic,
not a timing assertion or a substitute for checking the requested module.
-/

theorem one_equivalent_one : Probability.QProb.Equiv Probability.QProb.one Probability.QProb.one :=
  Probability.QProb.equiv_refl _

end Thesis.Examples.LocalCheckBaseline
