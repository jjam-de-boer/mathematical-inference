import Thesis.CausalTransport.NativeCertificateCheck
import Thesis.Examples.NativeSupportProfiles

namespace Thesis.Causality.Examples.NativeKernelInterfaceObstruction

open Probability ProbabilityCode NativeSupportProfiles

/-!
# A null carrier obstructs unconditional composition of kernel interfaces

This is a small counterexample to one proposed normal-form argument, not a
counterexample to causal soundness, universal coverage, or every possible
finite search. The existing checker is behaving correctly throughout.

Write `K = P(empty | Z)`, `U = P(empty)` and `V = U * U`. Rule 1 gives
`K -> U`; an empty-set chain step gives `U -> V`. The two candidates from
`K` have identical formula-status and conditional-demand metadata at every
reference of every native model, not just on a chosen finite profile list.
Their observable guard may accept a null value of `Z`: original source
support remains a separate soundness premise, so this never assigns a value
to the undefined original conditional.

The tempting interface substitution `U -> K -> V` is nevertheless rejected
at that null reference, even though the direct `U -> V` proof is supported.
Conditional demand is vacuous when an endpoint is undefined; it is not a
transitive relation on intermediate expressions. Identical metadata cannot
justify that particular carrier detour. The formulas are distinct syntax,
so this is not merely deletion of a reflexive proof loop.

The final two examples retain the asymmetric weighted boundary: a defined
zero may hide the whole detour, whereas a positive weight may not. A repair
must therefore track the actually active references, rather than requiring
every syntactically mentioned kernel to be supported everywhere. No solver,
large catalogue enumeration or new probability equation is introduced.
-/

def carrier : Kernel signature := ⟨NodeSet.empty, NodeSet.empty, NodeSet.full⟩
def unitTerm : ProbabilityTerm signature := .kernel ⟨NodeSet.empty, NodeSet.empty, NodeSet.empty⟩
def productTerm : ProbabilityTerm signature := .multiply unitTerm unitTerm

def eraseNullCondition : DoCalculusDerivation projection.observedGraph (.kernel carrier) unitTerm :=
  .doRule (.rule1 NodeSet.empty NodeSet.empty NodeSet.full NodeSet.empty
    (FourWayDisjoint.emptyActionConditioning NodeSet.empty NodeSet.full (NodeSet.disjoint_empty_left _))
    (by
      change projection.observedGraph.dSeparated (.bar NodeSet.empty) NodeSet.empty NodeSet.full
        (NodeSet.union NodeSet.empty NodeSet.empty) = true
      decide +kernel))

def expandUnit : DoCalculusDerivation projection.observedGraph unitTerm productTerm :=
  .chain NodeSet.empty NodeSet.empty NodeSet.empty NodeSet.empty
    (FourWayDisjoint.emptyActionConditioning NodeSet.empty NodeSet.empty (NodeSet.disjoint_empty_left _))

def toProduct := eraseNullCondition.trans expandUnit
def carrierDetour := eraseNullCondition.symm.trans toProduct

def unitCandidate : CheckedNativeProof projection.observedGraph :=
  .derivation ⟨.kernel carrier, unitTerm, eraseNullCondition⟩

def productCandidate : CheckedNativeProof projection.observedGraph :=
  .derivation ⟨.kernel carrier, productTerm, toProduct⟩

def reverseCandidate : CheckedNativeProof projection.observedGraph :=
  .derivation ⟨unitTerm, .kernel carrier, eraseNullCondition.symm⟩

def detourCandidate : CheckedNativeProof projection.observedGraph :=
  .derivation ⟨unitTerm, productTerm, carrierDetour⟩

/-- The primitive leaf's conditional demand is automatically satisfied
whenever its endpoints are defined, and is vacuous otherwise. -/
theorem unit_demand_always {P : FiniteLatentProjection signature}
    (model : FiniteHiddenDAGSCM signature P) (value : signature.Assignment) :
    unitCandidate.demand P model value = true := by
  change (if (model.termDenote (.kernel carrier) value).isSome && (model.termDenote unitTerm value).isSome then
    ((model.termDenote (.kernel carrier) value).isSome && (model.termDenote unitTerm value).isSome) && true else true) = true
  split
  · next accepted => rw [accepted]; rfl
  · rfl

/-- A defined strict square requires its factor. Thus the additional chain
step imposes no new conditional demand on this candidate from `K`. This
calculation is uniform in native models and never expands a profile list. -/
theorem product_demand_always {P : FiniteLatentProjection signature}
    (model : FiniteHiddenDAGSCM signature P) (value : signature.Assignment) :
    productCandidate.demand P model value = true := by
  change (if (model.termDenote (.kernel carrier) value).isSome &&
      (ProbabilityResult.multiply (model.termDenote unitTerm value) (model.termDenote unitTerm value)).isSome then
    ((model.termDenote (.kernel carrier) value).isSome &&
      (ProbabilityResult.multiply (model.termDenote unitTerm value) (model.termDenote unitTerm value)).isSome) &&
      ((((model.termDenote (.kernel carrier) value).isSome && (model.termDenote unitTerm value).isSome) && true) &&
        (((model.termDenote unitTerm value).isSome &&
          (ProbabilityResult.multiply (model.termDenote unitTerm value) (model.termDenote unitTerm value)).isSome) && true))
    else true) = true
  cases model.termDenote (.kernel carrier) value <;> cases model.termDenote unitTerm value <;> rfl

/-- Idempotence of the three-valued *status* of a strict square does not
assert numerical idempotence of arbitrary probabilities. -/
theorem formula_statuses_agree {P : FiniteLatentProjection signature}
    (model : FiniteHiddenDAGSCM signature P) (value : signature.Assignment) :
    ProbabilityResult.status (model.termDenote unitCandidate.right value) =
      ProbabilityResult.status (model.termDenote productCandidate.right value) := by
  change ProbabilityResult.status (model.termDenote unitTerm value) =
    ProbabilityResult.status (ProbabilityResult.multiply (model.termDenote unitTerm value) (model.termDenote unitTerm value))
  rw [ProbabilityResult.status_multiply]
  cases ProbabilityResult.status (model.termDenote unitTerm value) <;> rfl

/-- Any key consisting only of the common carrier, complete formula-status
table and conditional-demand table sees the same metadata. This holds for
every model/reference, hence also for every supplied complete catalogue. It
does not say that every possible richer interface has the same key. -/
theorem candidate_metadata_agree {P : FiniteLatentProjection signature}
    (model : FiniteHiddenDAGSCM signature P) (value : signature.Assignment) :
    unitCandidate.left = productCandidate.left ∧
      (ProbabilityResult.status (model.termDenote unitCandidate.right value), unitCandidate.demand P model value) =
      (ProbabilityResult.status (model.termDenote productCandidate.right value), productCandidate.demand P model value) := by
  exact ⟨rfl, by rw [formula_statuses_agree model value, unit_demand_always model value, product_demand_always model value]⟩

def profiles : List (NativeTemplateInstance projection) := [entry.uniformSupport]
def nullCell : NativeSupportGuard.Cell := ⟨[true, true, false], 2⟩

def unitFormula : CheckedNativeFormula projection.observedGraph profiles where
  source := .kernel carrier
  proof := unitCandidate
  source_eq := rfl
  actionFree := by intro _; rfl
  guard := [nullCell]
  guardChecked := by decide +kernel

def productFormula : CheckedNativeFormula projection.observedGraph profiles where
  source := .kernel carrier
  proof := productCandidate
  source_eq := rfl
  actionFree := by constructor <;> intro _ <;> rfl
  guard := [nullCell]
  guardChecked := by decide +kernel

theorem formulas_are_distinct : unitTerm ≠ productTerm := by intro impossible; cases impossible
theorem same_observable_guard : unitFormula.guard = productFormula.guard := rfl

/-- Both printed formulas are available, but neither supplies the missing
support of the original conditional source. Existing soundness keeps that
premise explicit; no causal value is inferred from this availability test. -/
theorem both_formulas_available :
    unitFormula.available entry.model.observationalDist (reference 2) = true ∧
      productFormula.available entry.model.observationalDist (reference 2) = true := by
  constructor <;> decide +kernel

theorem carrier_is_undefined :
    (entry.model.termDenote (.kernel carrier) (reference 2)).isSome = false := by decide +kernel

theorem direct_proof_supported :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2) expandUnit = true := by decide +kernel

theorem conditional_demand_does_not_compose :
    reverseCandidate.demand projection entry.model (reference 2) = true ∧
      productCandidate.demand projection entry.model (reference 2) = true ∧
      detourCandidate.demand projection entry.model (reference 2) = false := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

theorem carrier_detour_rejected :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2) carrierDetour = false := by decide +kernel

/-- At a supported carrier reference the same detour is legitimate. The
failure above is about the active support boundary, not invalid syntax. -/
theorem supported_carrier_detour_passes :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 0) carrierDetour = true := by decide +kernel

theorem zero_weight_can_hide_detour :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2)
      (.weightedMultiplyCongr (.refl .zero) carrierDetour) = true := by decide +kernel

theorem positive_weight_cannot_hide_detour :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2)
      (.weightedMultiplyCongr (.refl unitTerm) carrierDetour) = false := by decide +kernel

end Thesis.Causality.Examples.NativeKernelInterfaceObstruction
