import Thesis
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Enforced kernel-axiom audit

Every declaration owned by an imported `Thesis.*` module is checked at build
time.  Its transitive kernel-axiom dependencies may contain only `propext` and
`Quot.sound`, which arise from Lean's extensional infrastructure.  Any other
dependency, including `Classical.choice`, `Lean.ofReduceBool`, `sorryAx`, or an
additional assumed axiom, makes this module fail to elaborate.

The audit is a separate build target so the ordinary library remains usable
without running a project-policy check.  Continuous integration builds this
module explicitly.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (declName, _) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? declName | continue
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    unless moduleName.toString.startsWith "Thesis" do continue
    checked := checked + 1
    let axioms ← Lean.collectAxioms declName
    let forbidden := axioms.filter fun axiomName =>
      axiomName != `propext && axiomName != `Quot.sound
    unless forbidden.isEmpty do
      violations := violations.push (declName, forbidden)
  unless violations.isEmpty do
    let sortedViolations := violations.qsort fun left right =>
      Name.quickLt left.1 right.1
    throwError m!"imported Thesis declarations depend on forbidden axioms:\n{sortedViolations.toList}"
  logInfo m!"axiom policy checked {checked} imported Thesis declarations"
