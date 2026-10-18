import Thesis.Causality.Reductions

namespace Thesis.Causality.FiniteHiddenDAG

universe u
variable {S : ObservedSignature.{u}}

/-!
# Explicit observed-index lookup on a full hidden DAG

This graph-only lookup is shared by native constant models and standalone
finite templates. It was previously embedded in `HiddenDAGFullFamily`;
keeping it here avoids importing an entire semantic model family just to
construct a model's observed-index field. Public names and the search itself
are unchanged. No inverse is selected from a propositional existence proof.
-/

/-- Scan the explicit finite observed-node enumeration for an embedded node.
The input graph's injectivity makes any found index the unique correct one. -/
def observedIndex (H : FiniteHiddenDAG S) (node : Fin H.count) :
    Option (Fin S.count) :=
  (List.finRange S.count).find? (fun index => decide (H.observedNode index = node))

/-- A successful lookup has the declared observed embedding. -/
theorem observedIndex_sound (H : FiniteHiddenDAG S) (node : Fin H.count)
    (index : Fin S.count) (found : H.observedIndex node = some index) :
    H.observedNode index = node :=
  of_decide_eq_true
    (List.find?_some (p := fun candidate => decide (H.observedNode candidate = node)) found)

/-- Every embedded observed node is found, with its original index. Neither
case selects an index from a proposition to produce computational data. -/
theorem observedIndex_observed (H : FiniteHiddenDAG S) (index : Fin S.count) :
    H.observedIndex (H.observedNode index) = some index := by
  cases result : H.observedIndex (H.observedNode index) with
  | none =>
      have missing := (List.find?_eq_none.mp result) index (List.mem_finRange index)
      exact False.elim (missing (decide_eq_true rfl))
  | some found =>
      have same : found = index :=
        H.observedNode_injective (H.observedIndex_sound _ found result)
      exact congrArg some same

/-- A hidden node cannot be returned as an observed node. -/
theorem observedIndex_hidden (H : FiniteHiddenDAG S) (node : Fin H.count)
    (hidden : H.hidden node = true) : H.observedIndex node = none := by
  cases result : H.observedIndex node with
  | none => rfl
  | some index =>
      have embedding := H.observedIndex_sound node index result
      have notHidden : H.hidden node = false := embedding ▸ H.observed_not_hidden index
      exact False.elim (Bool.false_ne_true (notHidden.symm.trans hidden))

end Thesis.Causality.FiniteHiddenDAG
