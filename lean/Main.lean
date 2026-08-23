import Thesis

/-!
Executable build target for the complete Lean library and example.
-/

def main : IO Unit :=
  IO.println "Thesis formalization compiled."
