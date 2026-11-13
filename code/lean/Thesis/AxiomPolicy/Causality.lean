import Thesis.Causality
import Thesis.AxiomPolicy.Elaborator

open Lean Elab Command

/-!
# Prefix axiom audit for finite causal foundations
-/

run_cmd do
  Thesis.AxiomPolicy.audit Thesis.AxiomPolicy.causality "Causality"
