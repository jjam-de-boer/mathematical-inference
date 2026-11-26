import Thesis.CausalTransport.CertifiedModeInference
import Thesis.Causality.BinaryBowModel
import Thesis.Causality.CurrentBeliefCounterfactual

namespace Thesis.Examples.CurrentBeliefInference
open Probability Causality Causality.BinaryBow

/-!
# A selected belief cannot inherit the population graph's identification

The population model has two independent fair sources, with X = U_X and
Y = X xor U_Y. Its directed graph is X → Y and it has no shared source.
The mode's current information instead assigns weights 1,3,3,1 to the four
source assignments. This is a legitimate finite epistemic belief, and its
observed law is still strictly positive. It no longer has independent sources.

Reading the population adjustment formula from that updated observed table
gives 3/4, whereas intervening on X while retaining the current belief gives
1/2. The regression therefore tests a semantic disagreement, not merely an
undefined conditional. The public population API reads its proper prior and
returns 1/2 with a certificate. Current-belief evaluation also gives 1/2; its
conservative confounded graph does not claim the original identification.
-/

def fair : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- Each source belongs to just its corresponding observed mechanism.
The XOR equation below uses the allowed X parent as well as Y's private bit. -/
def privateSources : LatentExtension signature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq _ := inferInstance
  incident source child := decide (source.val = child.val)

def population : ExactModel signature where
  latent := privateSources
  factor _ := fair
  prior := FiniteProduct.record 2 (fun _ => Bool) (fun _ => fair)
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism child parents inputs :=
    if atX : child = x then inputs child (by simp [privateSources])
    else Bool.xor
      (parents x (by
        rcases node_cases child with same | same
        · exact (atX same).elim
        · simp [signature, x, y, same]))
      (inputs child (by simp [privateSources]))

def latentState (first second : Bool) : privateSources.Assignment :=
  fun index => if index.val = 0 then first else second

/-- Positive correlated information on the same source assignments. This
does not replace the independent generative prior stored in `population`. -/
def belief : FiniteProbRecord privateSources.Assignment where
  atoms := [(latentState false false, 1), (latentState false true, 3),
    (latentState true false, 3), (latentState true true, 1)]
  den := 8
  den_pos := by decide
  total_mass := rfl

def policy : ModeQueryPolicy signature where
  mode := ⟨population, belief⟩
  intervenable := NodeSet.full

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  action_outcome_disjoint := by
    intro node selected
    have same := (NodeSet.singleton_eq_true_iff x node).mp selected
    subst node
    decide +kernel

def reference : signature.Assignment := fun _ => true

/-- A Boolean comparison lets kernel reduction check a partial result
without requiring equality of arbitrary unreduced rational presentations. -/
def valueIs (result : ProbabilityResult.Result) (numerator denominator : Nat) : Bool :=
  match result with
  | none => false
  | some value => decide (value.num * denominator = numerator * value.den)

/-- Turn the executable comparison into Type-valued partial equality by
inspecting the actual result. No decidability of a proof-carrying equality
type and no classical witness extraction is assumed. -/
def equivalentOfValueIs (result : ProbabilityResult.Result) (expected : QProb)
    (checked : valueIs result expected.num expected.den = true) :
    ProbabilityResult.Equivalent result (some expected) := by
  cases result with
  | none => cases checked
  | some value => exact .value (of_decide_eq_true checked)

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def populationFormula : ProbabilityTerm signature :=
  match identifyJointKernel policy.graph query with
  | .identified term => term
  | _ => .zero

/-- The previously unsafe population-formula/current-table combination is
numerically defined but computes the wrong semantic target. -/
theorem old_combination_three_quarters :
    valueIs (populationFormula.observationalDenote policy.currentObservationalLaw reference) 3 4 = true := by
  decide +kernel

/-- Graphical population identification now uses the population table and
retains its class-indexed proof. The unrelated current belief cannot alter it. -/
theorem certified_population_half :
    valueIs (policy.identifyJoint query reference none none).identifiedValue 1 2 = true := by
  decide +kernel

/-- Direct evaluation of the current epistemic target agrees with actual
execution under the correlated belief, independently of graphical ID. -/
theorem evaluated_current_half :
    valueIs (policy.evaluateCurrentJoint query reference) 1 2 = true := by
  decide +kernel

theorem executed_current_half : QProb.Equiv
    (policy.mode.currentInterventionalValue
      ((HardIntervention.empty signature).set x true) (fun assignment => assignment y))
    ⟨1, 2, by decide⟩ := by
  decide +kernel

/-- The shared-source representation has the bow obstruction, so its ID
branch correctly refrains from certifying the population adjustment formula. -/
theorem conservative_current_not_identified :
    (policy.identifyCurrentJoint query reference).isIdentified = false := by
  decide +kernel

/-- There cannot be an applied certificate replacing this query by zero:
its soundness theorem would equate the supported value 1/2 with zero. This
tests the former override hole independently of the engine's own branch. -/
theorem no_zero_certificate :
    ¬ ∃ answer : CertifiedQuery.FormulaCertificate.At query.sourceTerm population reference,
      answer.certificate.formula = .zero := by
  rintro ⟨answer, zero⟩
  have source : ProbabilityResult.Equivalent (query.sourceTerm.denote population reference)
      (some (⟨1, 2, by decide⟩ : QProb)) := by
    exact equivalentOfValueIs _ _ (by decide +kernel)
  have agreement := ProbabilityResult.trans (ProbabilityResult.symm source) answer.correct
  have zeroValue : answer.value = some QProb.zero := by
    simp only [CertifiedQuery.FormulaCertificate.At.value, zero,
      ProbabilityTerm.observationalDenote]
  rw [zeroValue] at agreement
  cases agreement with
  | value impossible => cases impossible

/-! ## The same belief also keeps cross-world dependence -/

/-- Ask whether the outcome is true when X is forced to the specified bit. -/
def potentialY (setting : Bool) : CounterfactualEvent signature :=
  .atom ⟨((HardIntervention.empty signature).set x setting).value, y, true⟩

/-- The two hypothetical outcomes are complements at every source unit.
Conditioning on one true outcome makes the other a defined zero. -/
def exclusiveQuery : CounterfactualQuery signature :=
  ⟨potentialY false, potentialY true⟩

theorem current_counterfactual_zero :
    valueIs (policy.mode.currentCounterfactual exclusiveQuery) 0 1 = true := by
  decide +kernel

/-- Conditioning on both outcomes being true has no supporting source unit. -/
def unsupportedQuery : CounterfactualQuery signature :=
  ⟨.truth, .conj (potentialY false) (potentialY true)⟩

theorem unsupported_cross_world_condition :
    (policy.mode.currentCounterfactual unsupportedQuery).isNone = true := by
  decide +kernel

end Thesis.Examples.CurrentBeliefInference
