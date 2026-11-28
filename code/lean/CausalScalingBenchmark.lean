import Thesis.Examples.CausalAbstractionOrbits

/-!
Run with `lake env lean --run CausalScalingBenchmark.lean` from the Lean
project directory. The report uses actual solver results and displays the
fine observational laws of the endpoint models. Generation counts record
complete response tables enumerated. Solver sizes count the unknown masses
and initial linear inequalities before elimination.
-/

open Thesis
open Probability Causality Causality.CausalAbstractionInverse
open Causality.CausalScaleSelection Causality.ModelDescriptionCost
open Thesis.Examples.CausalAbstractionInverse
open Thesis.Examples.CausalScaleSelection
open Thesis.Examples.CausalAbstractionOrbits
open Thesis.Examples.CausalAbstractionSynthesis (compactSignature)

private def massText (mass : QProb) : String :=
  let (numerator, denominator) := reducedMass mass
  if denominator = 1 then toString numerator else s!"{numerator}/{denominator}"

private def widthEndpoint (value : SignedRatio) : String :=
  let reduced := reducedMass ⟨value.num.natAbs, value.den, value.den_pos⟩
  let sign := if value.num < 0 then "-" else ""
  if reduced.2 = 1 then s!"{sign}{reduced.1}" else s!"{sign}{reduced.1}/{reduced.2}"

private def lawText (model : ExactModel fine) : String :=
  String.intercalate ", " (fine.assignmentEnumeration.map fun state =>
    let bit := fun b : Bool => if b then "1" else "0"
    let probability := model.interventionalValue (HardIntervention.empty fine).value
      (FiniteProbRecord.singletonEvent state)
    s!"{bit (state (0 : Fin 2))}{bit (state (1 : Fin 2))}={massText probability}")

private def showAnswer (scale : Specification fine compactSignature) (label : String)
    (query : EventQuery fine) (result : scale.QueryResult query) : IO Unit := do
  match result with
  | .invalid _ => IO.println s!"  {label} has an invalid experiment protocol"
  | .incompatible .. => IO.println s!"  {label} has incompatible measurements"
  | .point _ sharp _ =>
    IO.println s!"  {label} = {massText (query.value sharp.lowerModel)}"
    IO.println s!"    fine witness ({lawText sharp.lowerModel})"
  | .interval _ sharp _ =>
    IO.println s!"  {label} is in [{massText (query.value sharp.lowerModel)}, {massText (query.value sharp.upperModel)}]"
    IO.println s!"    lower fine witness ({lawText sharp.lowerModel})"
    IO.println s!"    upper fine witness ({lawText sharp.upperModel})"

private def settings : List (HardIntervention fine × String) :=
  [(.empty fine, "observation"), (bothForced, "do(both=true)"), (forceFirst, "do(first=true)")]

private def showSizes (scale : Specification fine compactSignature) : IO Unit := do
  let (full, orbits, rows, orbitRows) := sizes scale
  IO.println s!"  Table generation enumerates {full} tables in both paths"
  IO.println s!"  Full solver has {full} masses and {rows} initial inequalities"
  IO.println s!"  Orbit solver has {orbits} masses and {orbitRows} initial inequalities"

private def showCandidate (name : String) (scale : Specification fine compactSignature) : IO Unit := do
  let candidate := priced scale
  let covered := settings.filterMap fun item => if candidate.Covers item.1 then some item.2 else none
  let experiments := String.intercalate ", " covered
  IO.println s!"  {name} (cost {candidate.cost}) covers {experiments}"
  match candidate.check workload with
  | .pass _ => IO.println "    Meets coverage and exact-answer requirements"
  | .fail (.missingExperiment ..) => IO.println "    Fails coverage for do(both=true)"
  | .fail (.query _ _ (.tooWide lower upper) _) =>
    IO.println s!"    Second parent has range [{widthEndpoint lower}, {widthEndpoint upper}] with zero width required"
  | .fail _ => IO.println "    Fails the declared workload"

def main : IO Unit := do
  IO.println "Symmetric AND protocol"
  showSizes spec
  showAnswer spec "P(both true)" observedBothTrue (spec.solveQueryWithOrbits rootSwap observedBothTrue)
  showAnswer spec "P(either true)" eitherRoot (spec.solveQueryWithOrbits rootSwap eitherRoot)
  match spec.solveConditionalWithOrbits rootSwap neitherRoot observedBothTrue with
  | .supported _ result (.possible ..) =>
    IO.println s!"  P(both true | neither true) = {massText (result.lower.value observedBothTrue)} when defined"
    IO.println "    A compatible model has zero evidence probability"
  | _ => IO.println "  Conditional fixture did not produce its expected support report"
  IO.println "Protocol with the first parent set true in an additional experiment"
  showSizes singlesOutFirst
  showAnswer singlesOutFirst "P(first true)" firstRoot
    (singlesOutFirst.solveQueryWithOrbits rootSwap firstRoot)
  showAnswer singlesOutFirst "P(second true)" secondRoot
    (singlesOutFirst.solveQueryWithOrbits rootSwap secondRoot)
  IO.println "Scale selection"
  showCandidate "Observation only" observeOnly
  showCandidate "Original AND merge" spec
  showCandidate "AND merge with an additional experiment" singlesOutFirst
  match winnerCost with
  | none => IO.println "  Every candidate fails"
  | some cost => IO.println s!"  Least feasible cost is {cost}"
  IO.println "Counterfactual check on two models with identical single-world laws"
  IO.println s!"  P(treatment changes outcome in the same unit) is {massText (changesOutcome.value (pairedModel false))} versus {massText (changesOutcome.value (pairedModel true))}"
