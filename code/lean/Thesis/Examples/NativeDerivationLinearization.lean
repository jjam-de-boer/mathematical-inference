import Thesis.CausalTransport.NativeLinearizedCertificate
import Thesis.Examples.NativeCertificateCheck

namespace Thesis.Causality.Examples.NativeDerivationLinearization

open Probability ProbabilityCode NativeSupportProfiles

/-!
# Nontrivial native linearization at zero and positive weights

The inner chain/inverse-chain loop has equal supported endpoints at the
declared null reference, but an unsupported intermediate. Its zero-weighted
parent must remain accepted after a genuine AC weight step followed by both
factor steps. Replacing that weight by one must instead retain the failure.
Strict marginal and fixed-reference frames test the less visible recursive
support obligations. These are small literal proofs, never full searches.

The certificate examples separately preserve the existing observable guard,
formula, null conditional-source boundary and top-level action-one leaf.
They use symbolic preservation theorems for decoded proofs whose syntactic
equalities can contain extensionality transports; no native decision axiom
or guessed reduction of such proof transports is used.
-/

def unitTerm : ProbabilityTerm signature := .kernel ⟨NodeSet.empty, NodeSet.empty, NodeSet.empty⟩

def chain := DoCalculusDerivation.chain (G := projection.observedGraph)
  (NodeSet.empty : NodeSet signature) NodeSet.empty NodeSet.full NodeSet.empty
  (FourWayDisjoint.emptyActionConditioning NodeSet.empty NodeSet.full (NodeSet.disjoint_empty_left _))

def strictLoop := DoCalculusDerivation.trans chain (.symm chain)

def zeroWeightStep := DoCalculusDerivation.multiplyComm (G := projection.observedGraph) .zero unitTerm
def positiveWeightStep := DoCalculusDerivation.multiplyComm (G := projection.observedGraph) unitTerm unitTerm
def zeroGuardedLoop := DoCalculusDerivation.weightedMultiplyCongr zeroWeightStep strictLoop
def positiveGuardedLoop := DoCalculusDerivation.weightedMultiplyCongr positiveWeightStep strictLoop
def nullIdentity := DoCalculusDerivation.refl (G := projection.observedGraph) nullConditional

theorem strict_loop_has_both_steps : strictLoop.linearize.length = 2 := by decide +kernel
theorem guarded_loop_keeps_weight_and_factor_steps : zeroGuardedLoop.linearize.length = 3 := by decide +kernel

/-- A zero-step path is not an exemption from original-source support. -/
theorem empty_null_path_still_rejected :
    nullIdentity.linearize.checkVertices entry.model (reference 2) = false := by decide +kernel

theorem strict_null_loop_rejected :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2) strictLoop = false := by decide +kernel

theorem strict_null_path_rejected :
    strictLoop.linearize.checkVertices entry.model (reference 2) = false := by decide +kernel

theorem supported_strict_path :
    strictLoop.linearize.checkVertices entry.model (reference 0) = true := by decide +kernel

theorem zero_weight_preserves_whole_loop :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2) zeroGuardedLoop = true := by decide +kernel

/-- Both the weight change and the two factor steps really occur. The
factor's undefined intermediate remains harmless only under a defined zero. -/
theorem zero_weight_path_supported :
    zeroGuardedLoop.linearize.checkVertices entry.model (reference 2) = true := by decide +kernel

theorem positive_weight_retains_failure :
    positiveGuardedLoop.linearize.checkVertices entry.model (reference 2) = false := by decide +kernel

theorem positive_weight_supported_reference :
    positiveGuardedLoop.linearize.checkVertices entry.model (reference 0) = true := by decide +kernel

def strictMarginal := DoCalculusDerivation.marginalizeCongr NodeSet.full strictLoop
def guardedMarginal := DoCalculusDerivation.marginalizeCongr NodeSet.full zeroGuardedLoop
def fixedNull := DoCalculusDerivation.evaluateAtCongr (reference 2) strictLoop
def fixedSupported := DoCalculusDerivation.evaluateAtCongr (reference 0) strictLoop

theorem marginal_visits_null_substitution :
    strictMarginal.linearize.checkVertices entry.model (reference 0) = false := by decide +kernel

theorem weighted_marginal_keeps_zero_branch :
    guardedMarginal.linearize.checkVertices entry.model (reference 0) = true := by decide +kernel

theorem evaluation_uses_fixed_null_reference :
    fixedNull.linearize.checkVertices entry.model (reference 0) = false := by decide +kernel

theorem evaluation_uses_fixed_supported_reference :
    fixedSupported.linearize.checkVertices entry.model (reference 2) = true := by decide +kernel

/-- Reconstruct the entire old recursive support tree, not merely endpoint
availability. The imported theorem covers arbitrary derivation depth. -/
theorem zero_weight_reinterpreted_check :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2)
      zeroGuardedLoop.linearize.toDerivation = true :=
  zeroGuardedLoop.linearize_toDerivation_check entry.model (reference 2) zero_weight_preserves_whole_loop

open NativeCertificateCheck

def linearGood := good.linearized rfl
def linearNullSource := nullSource.linearized rfl

theorem same_guard : linearGood.guard = good.guard := good.linearized_guard rfl
theorem same_formula : linearGood.formula = good.formula := good.linearized_formula rfl
theorem same_availability (record : FiniteProbRecord signature.Assignment) (referenceValue : signature.Assignment) :
    linearGood.available record referenceValue = good.available record referenceValue :=
  good.linearized_available rfl record referenceValue

theorem accepted_null_outcome_retained : linearGood.available entry.model.observationalDist (reference 2) = true := by
  rw [same_availability]
  exact good_available

theorem original_null_source_still_unsupported :
    ¬ Nonempty (entry.model.TermSupportedAt linearNullSource.source (reference 2)) := null_source_has_no_support

theorem printed_null_source_formula_still_available :
    linearNullSource.available entry.model.observationalDist (reference 2) = true := by
  unfold linearNullSource
  rw [CheckedNativeFormula.linearized_available]
  decide +kernel

example (kernel : Kernel signature) :
    (CheckedNativeProof.actionOne (graph := projection.observedGraph) kernel).linearized = .actionOne kernel := rfl

end Thesis.Causality.Examples.NativeDerivationLinearization
