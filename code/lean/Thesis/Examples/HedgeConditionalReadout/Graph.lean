import Thesis.Causality.ConditionalIdentificationKernel

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalMergedReadout

open Probability

/-!
# Concrete graph and engine checks for the merged conditional readout

This fixture defines the original six-node Boolean graph, query and finite
value witnesses. The companion exchange/failure modules retain the actual
engine checks. This module does not construct countermodels or import the large
carrier/readout development merely to perform these graph computations.

The statements and proof bodies are unchanged from `HedgeConditionalReadout`.
That original example imports this module and retains all routing, denominator
preservation and original-query countermodel assertions. Both halves remain
inside the full build and transitive axiom audit; splitting them does not
replace a computation by an assumption or raise any checking resource cap.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Two confounded roots, an unconfounded merge, and a retained conditioner -/

def signature : ObservedSignature where
  count := 6
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ (child.val = 1 ∨ child.val = 2)) ∨
      ((parent.val = 1 ∨ parent.val = 2) ∧ child.val = 3) ∨
      (parent.val = 3 ∧ child.val = 4) ∨ (parent.val = 4 ∧ child.val = 5))
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    rcases selected with ⟨_, _ | _⟩ | ⟨(_ | _), _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right ∧ left.val < 3 ∧ right.val < 3)
  bidirected_symmetric := by
    intro left right edge
    have selected := of_decide_eq_true edge
    exact decide_eq_true ⟨Ne.symm selected.1, selected.2.2, selected.2.1⟩
  bidirected_irreflexive := by
    intro node
    exact decide_eq_false (fun selected => selected.1 rfl)

def actionNode : Fin signature.count := ⟨0, by decide⟩
def firstRoot : Fin signature.count := ⟨1, by decide⟩
def secondRoot : Fin signature.count := ⟨2, by decide⟩
def mergeNode : Fin signature.count := ⟨3, by decide⟩
def outcomeNode : Fin signature.count := ⟨4, by decide⟩
def conditionNode : Fin signature.count := ⟨5, by decide⟩
def forestHost : NodeSet signature := fun node => decide (node.val < 3)
def rootMask : NodeSet signature := fun node => decide (node.val = 1 ∨ node.val = 2)

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton conditionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := fun _ => List.mem_cons_self
  second_enumerated := fun _ => List.mem_cons.mpr (Or.inr List.mem_cons_self)
  different := fun _ => Bool.false_ne_true

/-! ## Actual engine failure, without replacing the terminal query -/

theorem condition_nonempty : NodeSet.isEmpty query.condition = false := by decide +kernel

end HedgeConditionalMergedReadout
end Examples
end Causality
end Thesis
