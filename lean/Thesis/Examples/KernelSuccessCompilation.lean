import Thesis.CausalTransport.CompletenessAssembly
import Thesis.Examples.KernelProductCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentKernelSuccessCompilation

open Probability
open FrontDoorIdentification
open CurrentKernelCompilation
open CurrentKernelComponentCompilation
open CurrentKernelRecursionCompilation

/-!
# Regression checks for the structural current-kernel success compiler

These examples invoke the generic fuel induction directly.  Unlike the
branch-level regressions, they supply neither independently compiled child
certificates nor a hand-assembled sequence of pruning/extraction operations.
Each input is an actual successful engine equation, and the resulting formula
is the exact expression returned by that run.

The front-door and mediator queries exercise product recursion, containing
components, ancestral pruning, and nonempty action augmentation.  Their
semantic checks range over every positive compatible model and every
assignment, not merely the numerical model used to expose the old engine's
defect.  A recursive invocation with a gapped host and a nonempty external
action checks the input invariant away from the public observational root.
Empty outcomes and the zero-node signature retain their literal marginals
and everywhere-positive target witnesses.
-/

/-! ## The full front-door result now has a general published certificate -/

/-- The compiler reads the actual front-door success equation; all recursive
certificates and support witnesses are produced by its fuel induction. -/
noncomputable def frontDoorCertificate :
    PublishedJointCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness query :=
  identifyJointKernelPublishedCertificate (C := GraphModelClass.positive graph) graph.dSeparationCorrectness
    (fun member => member.2) query kernelEngine_identified

theorem frontDoorCertificate_formula : frontDoorCertificate.formula = kernelEngineFormula := rfl

/-- This strengthens the earlier single-model value regression to correctness
of the complete returned formula throughout the positive compatible class. -/
noncomputable def frontDoor_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model query.sourceTerm kernelEngineFormula reference :=
  identifyJointKernel_identified_soundAt (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    query kernelEngine_identified model member reference

theorem frontDoor_identifiable : (GraphModelClass.positive graph).identifiable query :=
  identifyJointKernel_identified_identifiable (C := GraphModelClass.positive graph) graph.dSeparationCorrectness
    (fun member => member.2) query kernelEngine_identified

/-! ## Augmentation and the independently checked two-component query -/

/-- The mediator query's nonempty additional action is handled by the same
compiler, with no caller-supplied rule-3 separation or nested certificate. -/
noncomputable def mediatorCertificate :
    PublishedJointCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness mediatorQuery :=
  identifyJointKernelPublishedCertificate (C := GraphModelClass.positive graph) graph.dSeparationCorrectness
    (fun member => member.2) mediatorQuery kernelMediator_identified

theorem mediatorCertificate_formula : mediatorCertificate.formula = kernelMediatorFormula := rfl

noncomputable def mediator_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model mediatorQuery.sourceTerm kernelMediatorFormula reference :=
  identifyJointKernel_identified_soundAt (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    mediatorQuery kernelMediator_identified model member reference

/-- Recompile the existing two-component regression automatically.  Its
previous explicit child certificates are not passed to this constructor. -/
noncomputable def splitCertificate :
    PublishedJointCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness CurrentKernelSplitCompilation.jointQuery :=
  identifyJointKernelPublishedCertificate (C := GraphModelClass.positive graph) graph.dSeparationCorrectness
    (fun member => member.2) CurrentKernelSplitCompilation.jointQuery
    CurrentKernelSplitCompilation.engine_identified

theorem splitCertificate_formula :
    splitCertificate.formula = CurrentKernelSplitCompilation.engineFormula := rfl

/-! ## A genuinely recursive gapped input keeps its external intervention -/

/-- Invoke the program inside the extracted `{X,Y}` host.  The external
mediator action remains fixed while the local `X` action is pruned. -/
noncomputable def gappedEngineFormula : ProbabilityTerm signature :=
  match identifyKernelFuel (kernelIdentificationFuel signature) graph gappedHost
      (NodeSet.singleton y) (NodeSet.singleton x) containingInput.certificate.formula with
  | .identified term => term
  | _ => .zero

set_option maxRecDepth 100000 in
theorem gappedEngine_identified :
    identifyKernelFuel (kernelIdentificationFuel signature) graph gappedHost
      (NodeSet.singleton y) (NodeSet.singleton x) containingInput.certificate.formula =
      .identified gappedEngineFormula := by rfl

/-- The general recursive interface constructs every nested input itself,
starting from the already extracted and certified current expression. -/
noncomputable def gappedCompilation :=
  identifyKernelFuelPublishedCompilation (kernelIdentificationFuel signature)
    containingInput (fun member => member.2) (NodeSet.singleton x) (NodeSet.singleton y)
    (NodeSet.singleton_subset_of_mem (by decide : gappedHost x = true))
    (NodeSet.singleton_subset_of_mem (by decide : gappedHost y = true))
    (NodeSet.disjoint_singletons_of_ne (by decide)) gappedEngine_identified

theorem gappedCompilation_formula : gappedCompilation.certificate.formula = gappedEngineFormula :=
  gappedCompilation.formula_eq

/-- Source actions include both the external mediator and the local `X`.
The supported derivation therefore checks the recursive source kernel, not
the observational distribution of the smaller induced host. -/
noncomputable def gappedCompilation_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨NodeSet.singleton y,
        NodeSet.union (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost))
          (NodeSet.singleton x), NodeSet.empty⟩) gappedEngineFormula reference := by
  let certificate := (gappedCompilation.certificate.reindex rfl gappedCompilation.formula_eq.symm).compile
  exact certificate.derivation.denotational_soundAt (graph.publishedSoundness.primitive model member.1)
    (certificate.supported model member reference
      (member.2.kernelPositiveSupportedValue
        ⟨NodeSet.singleton y,
          NodeSet.union (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost))
            (NodeSet.singleton x), NodeSet.empty⟩ reference).toSupported)

/-! ## Empty outcomes and a genuinely empty observed signature -/

/-- A nonempty local intervention with no outcomes first prunes its host;
the recursive empty-host input is generated by the compiler, not supplied. -/
def emptyOutcomeQuery : JointKernelQuery signature :=
  ⟨NodeSet.empty, NodeSet.singleton x, NodeSet.disjoint_empty_right _⟩

def emptyOutcomeEngineFormula : ProbabilityTerm signature :=
  match identifyJointKernel graph emptyOutcomeQuery with
  | .identified term => term
  | _ => .zero

set_option maxRecDepth 100000 in
theorem emptyOutcomeEngine_identified :
    identifyJointKernel graph emptyOutcomeQuery = .identified emptyOutcomeEngineFormula := by rfl

noncomputable def emptyOutcomeCompilation :=
  identifyJointKernelPublishedCompilation (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2) emptyOutcomeQuery emptyOutcomeEngine_identified

/-- Empty selections do not turn a target into an unsupported zero.  The
actual returned nested marginal stays strictly positive at every assignment. -/
noncomputable def emptyOutcome_positiveAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityResult.PositiveSupportedValue (emptyOutcomeEngineFormula.denote model reference) :=
  emptyOutcomeCompilation.positive model member reference

/-- The zero-node public query is well formed without selecting any observed
vertex, representative component, or value-rich two-state coordinate. -/
def zeroQuery : JointKernelQuery zeroSignature :=
  ⟨NodeSet.empty, NodeSet.empty, NodeSet.disjoint_empty_left _⟩

def zeroEngineFormula : ProbabilityTerm zeroSignature :=
  match identifyJointKernel zeroGraph zeroQuery with
  | .identified term => term
  | _ => .zero

theorem zeroEngine_identified : identifyJointKernel zeroGraph zeroQuery = .identified zeroEngineFormula := by rfl

noncomputable def zeroCertificate :
    PublishedJointCertificate (GraphModelClass.positive zeroGraph)
      zeroGraph.dSeparationCorrectness zeroQuery :=
  identifyJointKernelPublishedCertificate (C := GraphModelClass.positive zeroGraph) zeroGraph.dSeparationCorrectness
    (fun member => member.2) zeroQuery zeroEngine_identified

theorem zeroCertificate_formula : zeroCertificate.formula = zeroEngineFormula := rfl

/-- Zero fuel is still the explicit sentinel.  The success compiler does not
invent a certificate for an unfinished computation or silently add fuel. -/
theorem zeroFuel_unfinished : identifyKernelFuel 0 graph NodeSet.full query.outcome query.action
    (observationalJointTerm signature) = .unfinished := rfl

end CurrentKernelSuccessCompilation
end Examples
end Causality
end Thesis
