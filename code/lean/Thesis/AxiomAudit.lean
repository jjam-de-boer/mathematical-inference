import Thesis.AxiomPolicy.Distros
import Thesis.AxiomPolicy.Probability
import Thesis.AxiomPolicy.Causality
import Thesis.AxiomPolicy.CausalTransport
import Thesis.AxiomPolicy.Examples
import Thesis.AxiomPolicy.IdentificationNames
import Thesis.AxiomPolicy.Elaborator

open Lean Elab Command

/-!
# Collection gate for the kernel-axiom policy

Prefix audits already walked their private proofs.  This module imports
those wrappers, the extra-example coverage, and the removed-identification
name check.  It does not run a second `collectAxioms` pass.  It does fail if
an imported mathematical `Thesis.*` module sits outside every prefix.

The ordinary library remains usable without this target.  Continuous
integration and the sequential helper build it explicitly after `lake build`.
-/

run_cmd do
  Thesis.AxiomPolicy.assertPrefixCoverage
