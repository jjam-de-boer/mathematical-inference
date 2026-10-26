import Thesis.CausalTransport
import Thesis.AxiomPolicy.Elaborator

open Lean Elab Command

/-!
# Prefix axiom audit for soundness, completeness and native models
-/

run_cmd do
  Thesis.AxiomPolicy.audit Thesis.AxiomPolicy.causalTransport "CausalTransport"
