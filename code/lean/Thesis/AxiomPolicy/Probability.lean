import Thesis.Probability
import Thesis.Probability.FiniteRecordDefaults
import Thesis.Probability.FourLabelTransportationAggregation
import Thesis.Probability.FourLabelTransportationScaling
import Thesis.AxiomPolicy.Elaborator

open Lean Elab Command

/-!
# Prefix axiom audit for probability outside Distros

Includes the Probability facade and the optional rational transportation
roots and finite record defaults outside that facade. The latter imports
let this pass visit their private proofs directly. `Distros` separately
scans the named distribution prefix.
-/

run_cmd do
  Thesis.AxiomPolicy.audit Thesis.AxiomPolicy.probability "Probability"
