import Thesis.AxiomPolicy.Examples
import Lean.Elab.Command

open Lean Elab Command

/-!
# Removed unqualified identification names

The negative example retains explicitly qualified `Legacy` programs.
Those names must not reappear as `Thesis.Causality.identifyFuel` (and the
other removed entry points) anywhere in the complete imported development.
This is not an axiom walk and is not the modern-engine isolation check in
`Thesis.Examples.IdentificationAPIIsolation`.
-/

run_cmd do
  let env ← getEnv
  for removed in #[`Thesis.Causality.identifyFuel,
      `Thesis.Causality.identifyJoint,
      `Thesis.Causality.identifyConditional,
      `Thesis.Causality.PublishedJointTraceCompiler] do
    if env.contains removed then
      throwError m!"removed unsafe identification API is present: {removed}"
