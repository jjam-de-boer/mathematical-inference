import Thesis.Probability.Distros
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Early constructive-policy gate for distribution extensions. The complete
project-wide audit remains required after the full build. -/
open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let rec path (fuel : Nat) (name : Name) : CommandElabM (List Name) := do
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
          return name :: (← path fuel dependency)
      return [name]
  let mut checked := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (name, _) in env.constants do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[index.toNat]!
    unless moduleName.toString.startsWith "Thesis.Probability.Distros" do continue
    checked := checked + 1
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun axiomName => axiomName != `propext && axiomName != `Quot.sound
    unless forbidden.isEmpty do
      violations := violations.push (name, forbidden)
  unless violations.isEmpty do
    for (name, axioms) in violations do
      if axioms.contains `Classical.choice then logInfo m!"forbidden dependency path: {← path 12 name}"
    throwError m!"distribution declarations depend on forbidden axioms:\n{violations.toList}"
  logInfo m!"distribution axiom policy checked {checked} declarations"
