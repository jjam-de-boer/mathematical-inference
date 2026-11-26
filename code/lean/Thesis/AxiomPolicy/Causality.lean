import Thesis.Causality
import Thesis.Causality.CForestConstruction
import Thesis.Causality.DerivationContext
import Thesis.Causality.IdentificationOutcomeTraces
import Thesis.Causality.InterventionalCounterexample
import Thesis.Causality.ProbabilityStatusSupport
import Thesis.Causality.TermSupport
import Thesis.AxiomPolicy.Elaborator

open Lean Elab Command

/-!
# Prefix axiom audit for finite causal foundations

Import the foundation facade and optional support, counterexample and
trace modules outside it. A module can be available to later semantic
proofs without being visible to this pass. These explicit imports make
its public and private declarations visible to the owning scan.
-/

run_cmd do
  Thesis.AxiomPolicy.audit Thesis.AxiomPolicy.causality "Causality"
