import Thesis.Probability.Distros
import Thesis.AxiomPolicy.Elaborator

open Lean Elab Command

/-!
# Prefix axiom audit for named distributions

Early private-proof scan of `Thesis.Probability.Distros` and its children.
The rest of `Thesis.Probability` is a separate wrapper so Distros remain an
independently imported fail-fast root.
-/

run_cmd do
  Thesis.AxiomPolicy.audit Thesis.AxiomPolicy.distros "Distros"
