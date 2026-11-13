import Init.System.IO

/-!
Executable smoke test for the complete Lean library and examples.

The executable's explicit `needs = ["Thesis"]` Lake prerequisite checks the
unchanged full proof facade before this file is built. The executable itself
only prints the message below, so importing that facade here would needlessly
compile and link every proof-library definition and regression as machine code.
Keeping the build prerequisite separate preserves proof checking while making
ordinary Lake builds substantially smaller. The full axiom audit remains its
own explicit verification target.
-/

def main : IO Unit :=
  IO.println "Thesis formalization compiled."
