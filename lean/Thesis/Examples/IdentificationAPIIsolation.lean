import Thesis.Causality.ConditionalIdentificationKernel
import Lean.Elab.Command

/-!
# Modern identification does not import the refuted legacy program

This is an import-boundary regression, not a semantic identification proof.
It deliberately imports only the current conditional engine, which in turn
imports the current joint engine and their shared finite search data.  That
ordinary dependency closure must not reintroduce the historical recursion.

The front-door fixture in `IdentificationRegression` separately opts into
the legacy implementation to retain its checked counterexample.  Preserving
that fixture must not restore the old unqualified executable names or make
modern clients depend on the obsolete program.

The checks inspect Lean's declaration environment at elaboration time.  They
do not add logical axioms, decide an arbitrary proposition, or substitute a
runtime decision for a kernel-checked mathematical proof.  The full build
imports this module so a future accidental legacy dependency fails CI.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- Both supported entry points must remain available through this import.
  for supported in #[`Thesis.Causality.identifyJointKernel,
      `Thesis.Causality.identifyConditionalKernel] do
    unless env.contains supported do
      throwError m!"missing supported identification API: {supported}"
  -- Neither the removed public names nor the opt-in legacy programs belong
  -- to the current engines' declaration environment.
  for obsolete in #[`Thesis.Causality.identifyFuel,
      `Thesis.Causality.identifyJoint,
      `Thesis.Causality.identifyConditional,
      `Thesis.Causality.Legacy.identifyFuel,
      `Thesis.Causality.Legacy.identifyJoint,
      `Thesis.Causality.Legacy.identifyConditional] do
    if env.contains obsolete then
      throwError m!"legacy identification leaked into modern API: {obsolete}"
  -- Checking declarations alone would miss an empty forwarding import.
  -- Forbid the entire explicit legacy module family at this boundary.
  for moduleName in env.header.moduleNames do
    if moduleName.toString.startsWith "Thesis.Causality.Legacy." then
      throwError m!"modern identification imports legacy module: {moduleName}"
