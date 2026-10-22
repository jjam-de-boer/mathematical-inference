import Thesis.Examples.UncertaintyMeasure
import Thesis.Examples.EntropyMeanHalf
import Thesis.Examples.LogLinearEntropy
import Thesis.Examples.EntropyOptimize
import Thesis.Examples.EntropyContinuity
import Thesis.Examples.EntropyMoments
import Thesis.Examples.EntropySmallMass
import Thesis.Examples.EntropyConcavity
import Thesis.Examples.EntropyBounds
import Thesis.Examples.EntropyGibbsEquality
import Thesis.Examples.EntropyGibbs
import Thesis.Examples.FiniteAMGM
import Thesis.Examples.Entropy
import Thesis.Examples.ExactLog
import Thesis.Examples.RationalValues
import Thesis.Examples.IntegerLinearAlgebra
import Thesis.Examples.IntegerNullspace
import Thesis.Examples.FiniteRatioMinimum
import Thesis.Examples.AffineSupportReduction
import Thesis.Examples.FiniteIntegerCompression
import Thesis.Examples.FiniteRationalCompression
import Thesis.Examples.FiniteSourceCompression
import Thesis.Examples.FiniteProductReplacement
import Thesis.Examples.FiniteProductSourceCompression
import Thesis.Examples.RationalMonomial
import Thesis.Examples.RationalPolynomialIdentity
import Thesis.Examples.PolynomialBoundCertificate
import Thesis.Examples.FiniteProbabilityPolynomial
import Thesis.Examples.FiniteProbabilityPolynomialEncoding
import Thesis.Examples.FiniteProbabilityPolynomialCertificates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Early axiom check for the constructive arithmetic dependency closure

This small gate runs before the expensive whole-project build.  Standard
arithmetic constructions can have forbidden transitive proof dependencies
even when their data operations execute constructively; compilation alone
does not establish the project's axiom policy.  Checking the actual new
helper declarations first catches such mistakes without rebuilding all causal
modules before diagnosis.

The full `Thesis.AxiomAudit` remains mandatory and unchanged.  This early
subset check does not substitute for that gate or exclude any declaration
from the later project-wide scan.  Both allow exactly `propext` and `Quot.sound`.
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
    throwError m!"constructive algebra declarations depend on forbidden axioms: {violations.toList}"
  logInfo m!"early algebra axiom policy checked {checked} imported Thesis declarations"
