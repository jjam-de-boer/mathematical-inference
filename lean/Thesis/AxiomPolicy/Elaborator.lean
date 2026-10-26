import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace Thesis
namespace AxiomPolicy

/-- Audit-policy modules are not an ownership prefix of the mathematical tree. -/
def isPolicyModule (path : String) : Bool :=
  path == "Thesis.AxiomAudit" || path.startsWith "Thesis.AxiomPolicy"

def distros (path : String) : Bool :=
  path == "Thesis.Probability.Distros" ||
    path.startsWith "Thesis.Probability.Distros."

def probability (path : String) : Bool :=
  (path == "Thesis.Probability" || path.startsWith "Thesis.Probability.") &&
    !distros path

def causality (path : String) : Bool :=
  path == "Thesis.Causality" || path.startsWith "Thesis.Causality."

def causalTransport (path : String) : Bool :=
  path == "Thesis.CausalTransport" || path.startsWith "Thesis.CausalTransport."

def examples (path : String) : Bool :=
  path == "Thesis" || path == "Thesis.Examples" ||
    path.startsWith "Thesis.Examples."

/-- Each mathematical `Thesis.*` source belongs to exactly one prefix audit. -/
def owner? (path : String) : Option String :=
  if isPolicyModule path then none
  else if distros path then some "distros"
  else if probability path then some "probability"
  else if causality path then some "causality"
  else if causalTransport path then some "causalTransport"
  else if examples path then some "examples"
  else none

def permittedAxiom (name : Name) : Bool :=
  name == `propext || name == `Quot.sound

/-- Follow one `Classical.choice` edge through the private environment. -/
def choicePath (fuel : Nat) (name : Name) : CommandElabM (List Name) := do
  let env ← getEnv
  match fuel with
  | 0 => return [name]
  | fuel + 1 =>
    if name == `Classical.choice then return [name]
    let some info := env.find? name | return [name]
    let body := match info with
      | .thmInfo value => value.value
      | .defnInfo value => value.value
      | .opaqueInfo value => value.value
      | _ => info.type
    let dependencies := body.getUsedConstants ++ info.type.getUsedConstants
    for dependency in dependencies do
      let axioms ← Lean.collectAxioms dependency
      if axioms.contains `Classical.choice then
        return name :: (← choicePath fuel dependency)
    return [name]

/-- Private-proof axiom walk for declarations owned by `keep` sources. -/
def audit (keep : String → Bool) (subject : String) : CommandElabM Unit := do
  setEnv ((← getEnv).setExporting false)
  let env ← getEnv
  let mut checked := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (declName, _) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? declName | continue
    let ownerName := env.header.moduleNames[moduleIdx.toNat]!
    unless keep ownerName.toString do continue
    checked := checked + 1
    let axioms ← Lean.collectAxioms declName
    let forbidden := axioms.filter fun axiomName => !permittedAxiom axiomName
    unless forbidden.isEmpty do
      violations := violations.push (declName, forbidden)
  unless violations.isEmpty do
    for (name, axioms) in violations do
      if axioms.contains `Classical.choice then
        logInfo m!"forbidden dependency path: {← choicePath 12 name}"
    let sorted := violations.qsort fun left right => Name.quickLt left.1 right.1
    throwError m!"{subject} declarations depend on forbidden axioms:\n{sorted.toList}"
  logInfo m!"{subject} axiom policy checked {checked} declarations"

/-- Fail if an imported `Thesis.*` mathematical source has no prefix owner. -/
def assertPrefixCoverage : CommandElabM Unit := do
  let env ← getEnv
  let mut missing : Array Name := #[]
  for ownerName in env.header.moduleNames do
    let path := ownerName.toString
    unless path == "Thesis" || path.startsWith "Thesis." do continue
    if isPolicyModule path then continue
    if (owner? path).isNone then
      missing := missing.push ownerName
  unless missing.isEmpty do
    throwError m!"Thesis sources outside every axiom-policy prefix:\n{missing.toList}"

end AxiomPolicy
end Thesis
