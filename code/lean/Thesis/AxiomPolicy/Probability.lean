import Thesis.Probability
import Thesis.AxiomPolicy.Elaborator

open Lean Elab Command

/-!
# Prefix axiom audit for probability outside Distros

Includes Core, constructive reals, exact logarithms and the Probability
facade.  Excludes `Thesis.Probability.Distros*`, which `Distros` already
scans.
-/

run_cmd do
  Thesis.AxiomPolicy.audit Thesis.AxiomPolicy.probability "Probability"
