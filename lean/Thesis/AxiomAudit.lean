import Thesis.Examples.ConstructiveRealOrder
import Thesis.Examples.ConstructiveRealCauchy
import Thesis.Examples.ConstructiveRealAlgebra
import Thesis.Examples.ConstructiveRealMultiplication
import Thesis.Examples.RationalNorm
import Thesis.Examples.ConstructiveRealLimits
import Thesis.Examples.ConstructiveReal
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
import Thesis
import Thesis.Examples.ConditionalReadoutFailure
import Thesis.Examples.ConditionalReadoutPaths
import Thesis.Examples.DistributionLaws
import Thesis.Examples.DistributionExtensions
import Thesis.Examples.DistroRealization
import Thesis.Examples.DistroPartialMoments
import Thesis.Examples.DistroRanks
import Thesis.Examples.BooleanChannelExpansion
import Thesis.Examples.FiniteProductBalance
import Thesis.Examples.PairRootChannels
import Thesis.Examples.LocalCheckBaseline
import Thesis.Examples.LocalCheckImports
import Thesis.Examples.LocalCheckCoreImports
import Thesis.Examples.LocalCheckDefinition
import Thesis.Examples.LocalCheckRetainedDependency
import Thesis.Examples.LocalCheckFiniteDecision
import Thesis.Examples.PositiveModal
import Thesis.Examples.SupportedModal
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

The optional exact readout-failure/path regressions are imported here rather
than by the ordinary smoke facade.  Their expanded-graph decision proofs can
need more kernel memory than a capped local module check.  The full CI policy
gate therefore checks their compilation and transitive axioms as well, without
making lightweight semantic clients import those expensive computations.

The small local-check fixtures intentionally separate imports, a reused
reflexivity proof, a recursive definition and a finite kernel decision. They
are resource diagnostics, but any declarations they add still belong inside
this same transitive axiom policy rather than outside the verification gate.

The standalone channel-expansion, product-balance and pair-root regressions
are also policy-gate imports. Their underlying library lemmas already belong
to the public facade, but that alone does not elaborate these separate test
files. Importing the tests here checks both their exact computations and
their transitive axioms without enlarging ordinary library clients.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- Historical traces and the counterexample fixture deliberately retain
  -- explicitly qualified Legacy declarations.  Their import must never
  -- restore the removed unsafe ordinary API, even through a compatibility
  -- alias or a forwarding module elsewhere in the complete development.
  for removed in #[`Thesis.Causality.identifyFuel,
      `Thesis.Causality.identifyJoint,
      `Thesis.Causality.identifyConditional,
      `Thesis.Causality.PublishedJointTraceCompiler] do
    if env.contains removed then
      throwError m!"removed unsafe identification API is present: {removed}"
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
