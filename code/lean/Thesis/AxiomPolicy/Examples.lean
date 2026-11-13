import Thesis
import Thesis.AxiomPolicy.Coverage
import Thesis.AxiomPolicy.Elaborator

open Lean Elab Command

/-!
# Prefix axiom audit for examples and policy-only regressions

Imports the ordinary `Thesis` facade together with `Coverage`, then scans
`Thesis.Examples*` and the root `Thesis` barrel module.
-/

run_cmd do
  Thesis.AxiomPolicy.audit Thesis.AxiomPolicy.examples "Examples"
