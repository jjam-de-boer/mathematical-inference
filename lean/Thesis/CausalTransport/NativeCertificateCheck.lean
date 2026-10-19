import Thesis.Causality.DerivationCode
import Thesis.CausalTransport.NativeDerivationSupportCheck
import Thesis.CausalTransport.NativeSupportGuard
import Thesis.CausalTransport.HiddenDAGSoundness
import Thesis.CausalTransport.ObservationalFormulaSupport

namespace Thesis.Causality

open Probability

/-!
# Opt-in native formula certificates with serialized support guards

Untrusted input contains a coded source, a coded proof and a finite observable
guard table. The checker decodes the proof, verifies its actual source and
action-free output, then checks its recursive support demand across *every*
matching causal support profile. The two public entry points cover either
one fixed full hidden DAG or all finite hidden DAGs at a fixed projection.

The proof language includes the entire existing executable do-calculus
derivation syntax. A separate top-level `actionOne` leaf reuses the proved
distribution-specific identity; it is never an unguarded do-calculus rule.
Its probability-one obligation is checked alongside the other support
demands. No user-provided semantic proof enters the serialized code.

Original source support remains an explicit application premise, notably for
conditional targets. Printed availability alone cannot fill a null causal
conditioner. The old two-guard formula API is unchanged. These additions do
not enumerate proof trees, select formulas, certify arbitrary Lean semantic
proofs, or settle the universal stopping/coverage question.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace ProbabilityCode

inductive NativeProofCode where
  | derivation (code : DerivationCode)
  | actionOne (kernel : KernelCode)
  deriving Repr, DecidableEq

inductive CheckedNativeProof (graph : ObservedGraph S) where
  | derivation (checked : CheckedDerivation graph)
  | actionOne (kernel : Kernel S)

def NativeProofCode.check (graph : ObservedGraph S) : NativeProofCode → Option (CheckedNativeProof graph)
  | .derivation code => return .derivation (← code.check graph)
  | .actionOne code => return .actionOne (← code.decode S)

namespace CheckedNativeProof

def left : CheckedNativeProof graph → ProbabilityTerm S
  | .derivation checked => checked.left
  | .actionOne kernel => .kernel kernel

def right : CheckedNativeProof graph → ProbabilityTerm S
  | .derivation checked => checked.right
  | .actionOne kernel => .kernel ⟨kernel.outcome, NodeSet.empty, kernel.condition⟩

def endpoints (proof : CheckedNativeProof graph) : NativeSupportGuard.Demand S := fun _ model reference =>
  (model.termDenote proof.left reference).isSome && (model.termDenote proof.right reference).isSome

/-- Source and printed support are separate application premises. The guard
therefore needs extra obligations only on profiles where both endpoints have
values; null original conditioners are not silently removed or filled. -/
def demand (proof : CheckedNativeProof graph) : NativeSupportGuard.Demand S := fun projection model reference =>
  if proof.endpoints projection model reference then
    match proof with
    | .derivation checked => HiddenDAGLocalDerivationSupport.check model reference checked.derivation
    | .actionOne kernel => (ObservationalFormulaGuard.actionOne kernel.action).check model.observationalDist reference
  else true

private theorem term_isSome_eq {leftModel : FiniteHiddenDAGSCM S P} {rightModel : FiniteHiddenDAGSCM S Q}
    (same : CausalSupportAgreement leftModel rightModel) (term : ProbabilityTerm S) (reference : S.Assignment) :
    (leftModel.termDenote term reference).isSome = (rightModel.termDenote term reference).isSome := by
  rw [← ProbabilityResult.status_isDefined, ← ProbabilityResult.status_isDefined, same.term_status term reference]

theorem demand_invariant (proof : CheckedNativeProof graph) : NativeSupportGuard.Invariant proof.demand := by
  intro leftProjection rightProjection leftModel rightModel same reference
  have sameEndpoints : proof.endpoints leftProjection leftModel reference = proof.endpoints rightProjection rightModel reference := by
    simp only [endpoints, term_isSome_eq same]
  cases proof with
  | derivation checked =>
      simp only [demand, sameEndpoints,
        HiddenDAGLocalDerivationSupport.check_eq_of_agreement same reference checked.derivation]
  | actionOne kernel =>
      have sameGuard : (ObservationalFormulaGuard.actionOne kernel.action).check leftModel.observationalDist reference =
          (ObservationalFormulaGuard.actionOne kernel.action).check rightModel.observationalDist reference := by
        rw [← ObservationalFormulaGuard.checkSupport_exact, ← ObservationalFormulaGuard.checkSupport_exact,
          same.observational_support]
      simp only [demand, sameEndpoints, sameGuard]

noncomputable def soundAt (proof : CheckedNativeProof graph) (model : FiniteHiddenDAGSCM S P)
    (graphEqual : graph = P.observedGraph) (reference : S.Assignment) (sourceSupported : model.TermSupportedAt proof.left reference)
    (printedSupported : model.TermSupportedAt proof.right reference) (checked : proof.demand P model reference = true) :
    model.TermEquivalentAt proof.left proof.right reference := by
  cases graphEqual
  have endpointsChecked : proof.endpoints P model reference = true :=
    Bool.and_eq_true_iff.mpr ⟨ProbabilityResult.supported_isSome sourceSupported,
      ProbabilityResult.supported_isSome printedSupported⟩
  cases proof with
  | derivation accepted =>
      have supported : HiddenDAGLocalDerivationSupport.check model reference accepted.derivation = true := by
        simpa only [demand, endpointsChecked, if_true] using checked
      exact accepted.derivation.hiddenDAG_denotational_soundAt
        (HiddenDAGLocalDerivationSupport.ofCheck model reference accepted.derivation supported)
  | actionOne kernel =>
      have guardAccepted : (ObservationalFormulaGuard.actionOne kernel.action).check model.observationalDist reference = true := by
        simpa only [demand, endpointsChecked, if_true] using checked
      exact model.kernel_eq_observational_of_action_one kernel reference
        ((ObservationalFormulaGuard.check_actionOne_iff kernel.action model.observationalDist reference).mp guardAccepted)

end CheckedNativeProof

structure NativeCertificateCode where
  source : TermCode
  proof : NativeProofCode
  guard : NativeSupportGuard.Code
  deriving Repr, DecidableEq

/-- Proof fields are produced by the checker. In particular, guard safety
is a successful finite check, not an externally supplied interpretation law. -/
structure CheckedNativeFormula (graph : ObservedGraph S) (profiles : List (NativeTemplateInstance Q)) where
  source : ProbabilityTerm S
  proof : CheckedNativeProof graph
  source_eq : proof.left = source
  actionFree : proof.right.ActionFree
  guard : NativeSupportGuard.Code
  guardChecked : NativeSupportGuard.check profiles proof.demand guard = true

def NativeCertificateCode.checkOn (graph : ObservedGraph S) (profiles : List (NativeTemplateInstance Q))
    (code : NativeCertificateCode) : Option (CheckedNativeFormula graph profiles) := do
  let source ← code.source.decode S
  let proof ← code.proof.check graph
  if sourceSame : proof.left = source then
    if actionFree : proof.right.actionFreeCheck = true then
      if checked : NativeSupportGuard.check profiles proof.demand code.guard = true then
        pure ⟨source, proof, sourceSame, (ProbabilityTerm.actionFreeCheck_exact proof.right).mp actionFree, code.guard, checked⟩
      else none
    else none
  else none

def NativeCertificateCode.checkFixed (projection : FiniteLatentProjection S) (code : NativeCertificateCode) :=
  code.checkOn projection.observedGraph projection.completeSupportCatalogue

def NativeCertificateCode.checkProjected (graph : ObservedGraph S) (code : NativeCertificateCode) :=
  code.checkOn graph graph.cliqueRootProjection.completeSupportCatalogue

namespace CheckedNativeFormula

def formula (checked : CheckedNativeFormula graph profiles) : ProbabilityTerm S := checked.proof.right

def available (checked : CheckedNativeFormula graph profiles) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) : Bool :=
  NativeSupportGuard.accepts checked.guard record reference &&
    (checked.formula.observationalDenote record reference).isSome

/-- The generic lemma exposes its coverage argument so small verified lists
can also be used. The fixed/projection-wide adapters below supply the full
constructed coverage theorem automatically. -/
noncomputable def soundAt (checked : CheckedNativeFormula graph profiles)
    (model : FiniteHiddenDAGSCM S P)
    (graphEqual : graph = P.observedGraph)
    (covered : ∃ entry, entry ∈ profiles ∧ CausalSupportAgreement entry.model model)
    (reference : S.Assignment) (sourceSupported : model.TermSupportedAt checked.source reference)
    (accepted : checked.available model.observationalDist reference = true) :
    model.TermEquivalentAt checked.source checked.formula reference := by
  have atGuard := (Bool.and_eq_true_iff.mp accepted).1
  have printed : model.TermSupportedAt checked.proof.right reference :=
    ProbabilityResult.supportedOfIsSome _ (by
      rw [← ProbabilityTerm.observationalDenote_eq_native model checked.proof.right checked.actionFree reference]
      exact (Bool.and_eq_true_iff.mp accepted).2)
  have demanded := NativeSupportGuard.soundAt profiles checked.proof.demand checked.proof.demand_invariant
    checked.guard checked.guardChecked model covered reference atGuard
  have source : model.TermSupportedAt checked.proof.left reference := by
    rw [checked.source_eq]
    exact sourceSupported
  have equivalent := checked.proof.soundAt model graphEqual reference source printed demanded
  simpa only [checked.source_eq] using equivalent

noncomputable def fixed_soundAt (checked : CheckedNativeFormula P.observedGraph P.completeSupportCatalogue)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (sourceSupported : model.TermSupportedAt checked.source reference)
    (accepted : checked.available model.observationalDist reference = true) :
    model.TermEquivalentAt checked.source checked.formula reference :=
  checked.soundAt model rfl model.completeSupportCatalogue_covers reference sourceSupported accepted

private theorem graph_eq_of_edges {left right : ObservedGraph S}
    (same : ∀ first second, left.bidirected first second = right.bidirected first second) : left = right := by
  cases left with
  | mk first firstSymmetric firstIrreflexive =>
      cases right with
      | mk second secondSymmetric secondIrreflexive =>
          have equal : first = second := funext (fun node => funext (same node))
          cases equal
          rfl

/-- Soundness on every original finite hidden DAG with this projection,
not only on the fixed clique-root graph used to check its support profiles. -/
noncomputable def projected_soundAt {graph : ObservedGraph S}
    (checked : CheckedNativeFormula graph graph.cliqueRootProjection.completeSupportCatalogue)
    (original : ProjectedHiddenDAGModel graph) (reference : S.Assignment)
    (sourceSupported : original.model.TermSupportedAt checked.source reference)
    (accepted : checked.available original.model.observationalDist reference = true) :
    original.model.TermEquivalentAt checked.source checked.formula reference := by
  have equal : original.projection.observedGraph = graph := graph_eq_of_edges original.projected
  exact checked.soundAt original.model equal.symm original.completeSupportCatalogue_covers reference sourceSupported accepted

end CheckedNativeFormula
end ProbabilityCode
end Thesis.Causality
