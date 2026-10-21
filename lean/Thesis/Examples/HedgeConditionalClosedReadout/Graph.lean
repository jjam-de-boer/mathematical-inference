import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalClosedReentry

open Probability
open CurrentKernelFailureExtraction (partitionGraph)

/-!
# The original three-valued closed-readout graph and queries

Only the concrete signature, graph, node sets, value witnesses and both
original queries are defined here. Countermodel geometry and readout semantics
remain separate from the executable graph computations.

The original entry point `Examples.HedgeConditionalClosedReadout` still
imports these checks and constructs the same semantic countermodels. Every
original statement and proof body is retained, with no omitted finite test
and no increase to the local resource limits.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature : ObservedSignature where
  count := 6
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 4) ∨ (parent.val = 4 ∧ child.val = 5) ∨
      (parent.val = 3 ∧ child.val = 4) ∨ (parent.val = 1 ∧ child.val = 2) ∨
      (parent.val = 2 ∧ child.val = 3))
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    omega

def graph := partitionGraph signature (fun node => decide (node.val = 2 ∨ node.val = 5))
def actionNode : Fin signature.count := ⟨0, by decide⟩
def firstRoot : Fin signature.count := ⟨1, by decide⟩
def outsideNode : Fin signature.count := ⟨2, by decide⟩
def internalNode : Fin signature.count := ⟨3, by decide⟩
def lastRoot : Fin signature.count := ⟨4, by decide⟩
def outcomeNode : Fin signature.count := ⟨5, by decide⟩

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton internalNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def large : NodeSet signature := fun node => decide (node.val ≠ 2 ∧ node.val ≠ 5)
def small : NodeSet signature := fun node => decide (node.val = 1 ∨ node.val = 3 ∨ node.val = 4)
def child : ForestChild signature := fun parent => match parent.val with
  | 0 => some lastRoot
  | 3 => some lastRoot
  | _ => none
def roots : NodeSet signature := keptSinks large child

def earlierQuery : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton outsideNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

end HedgeConditionalClosedReentry
end Examples
end Causality
end Thesis
