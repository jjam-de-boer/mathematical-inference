import Init.System.IO
import Thesis.Examples.InferenceWorkflow

/-!
Runnable finite inference example. After the ordinary build, execute
`lake env lean --run InferenceWorkflow.lean` from the Lean project directory.
The imported library computes the displayed values and checks the associated
sampling, certification, symmetry and abstraction theorems.
-/

def main : IO Unit := do
  for line in Thesis.Examples.InferenceWorkflow.lines do
    IO.println line
