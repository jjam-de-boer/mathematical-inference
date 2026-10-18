import Thesis.CausalTransport.HiddenDAGReachableValues

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Bounded hidden values on an unchanged full hidden DAG

Use the explicit retained domains to construct a native model whose endogenous
values are actual finite codes. At hidden nodes these codes represent only
retained trajectories. At observed nodes they represent the entire old domain,
and a two-sided conversion retains the original public observed signature,
including all permitted null intervention values. Noise types, their records,
independence, graph incidence and the original rank are kept verbatim.

The new equation decodes its parent inputs, runs the old equation, and encodes
its output. Encoding uses the explicit factual default off the retained domain.
The simulation proof is therefore essential: it establishes that every parent
and output along each retained trajectory lies in its domain, so those defaults
cannot change that trajectory. No statement is made for an unlisted action.

The factual intervention is always retained, even with an empty extra-action
list. Each hidden code cardinality is bounded by the number of retained action
positions times the number of declared noise assignments. After the separate
source adapter bounds each private alphabet by K, this gives the uniform bound
`(actions.length + 1) * K ^ numberOfNodes`. This is not yet an enumeration of
all finite mechanism tables or a representation theorem over varying topology.
-/

namespace FiniteHiddenDAGSCM

/-- Observed coding is genuinely two-sided on the full public domain.
Only hidden values use a partial-domain retraction. -/
def retainedObservedEquiv (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (index : Fin S.count) : ValueEquivalence (model.ValueCode actions (P.hiddenDAG.observedNode index)) (S.Value index) where
  forward := fun code => (model.observedEquiv index).forward (model.decodeValue actions _ code)
  backward := fun value => model.encodeValue actions _ ((model.observedEquiv index).backward value)
  forward_backward := by
    intro value
    rw [model.decodeValue_encodeValue actions _ _ (model.observedValue_mem_retainedNodeValues actions index _)]
    exact (model.observedEquiv index).forward_backward value
  backward_forward := by
    intro code
    rw [(model.observedEquiv index).backward_forward]
    exact model.encodeValue_decodeValue actions _ code

/-- Actual bounded finite endogenous types, with the same full graph and
the same independent private-source law. The public observed types do not
change; their native internal presentation is transported bijectively. -/
def retainedValueModel (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S)) :
    FiniteHiddenDAGSCM S P :=
  { model with
    NodeValue := model.ValueCode actions
    nodeEnumeration := fun node => List.finRange (model.valueWitness actions node).card
    node_complete := fun _ code => List.mem_finRange code
    nodeDecidableEq := fun _ => inferInstance
    observedEquiv := model.retainedObservedEquiv actions
    mechanism := fun child parents seed => model.encodeValue actions child
      (model.mechanism child (fun parent edge => model.decodeValue actions parent (parents parent edge)) seed) }

theorem retainedValueModel_nodeValue (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) :
    (model.retainedValueModel actions).NodeValue node = Fin (model.valueWitness actions node).card := rfl

theorem retainedValueModel_nodeEnumeration_length (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) :
    ((model.retainedValueModel actions).nodeEnumeration node).length = (model.valueWitness actions node).card :=
  List.length_finRange

/-- A forced observed value is encoded in full, never replaced by the
hidden fallback merely because it was observationally null. -/
theorem retainedValueModel_interventionValueAt (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (node : Fin P.hiddenDAG.count) :
    (model.retainedValueModel actions).interventionValueAt intervention node =
      (model.interventionValueAt intervention node).map (model.encodeValue actions node) := by
  unfold interventionValueAt
  change (match selected : model.observedIndex node with
    | none => none
    | some index => match intervention.value index with
      | none => none
      | some value => some (model.observedIndex_sound node index selected ▸
          (model.retainedObservedEquiv actions index).backward value)) = _
  cases selected : model.observedIndex node with
  | none => rfl
  | some index =>
      cases forced : intervention.value index with
      | none => rfl
      | some value =>
          have same := model.observedIndex_sound node index selected
          cases same
          rfl

/-- The new evaluator computes the encoded old trajectory. The supplied
action membership justifies every inverse-decoding step, including hidden
parents whose other possible values have deliberately been discarded. -/
theorem retainedValueModel_evalNode (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (listed : intervention ∈ HardIntervention.empty S :: actions)
    (noise : model.NoiseAssignment) (node : Fin P.hiddenDAG.count) :
    (model.retainedValueModel actions).evalNode intervention noise node =
      model.encodeValue actions node (model.evalNode intervention noise node) := by
  apply (model.retainedValueModel actions).evalNode_eq_of_solution intervention noise
    (fun current => model.encodeValue actions current (model.evalNode intervention noise current))
  intro current
  rw [model.retainedValueModel_interventionValueAt actions intervention current]
  rw [evalNode]
  cases forced : model.interventionValueAt intervention current with
  | some value => rfl
  | none =>
      change model.encodeValue actions current (model.mechanism current
          (fun parent _ => model.evalNode intervention noise parent) (noise current)) =
        model.encodeValue actions current (model.mechanism current
          (fun parent _ => model.decodeValue actions parent
            (model.encodeValue actions parent (model.evalNode intervention noise parent))) (noise current))
      have sameParents :
          (fun parent (_ : P.hiddenDAG.edge parent current = true) => model.decodeValue actions parent
            (model.encodeValue actions parent (model.evalNode intervention noise parent))) =
          (fun parent (_ : P.hiddenDAG.edge parent current = true) => model.evalNode intervention noise parent) := by
        funext parent edge
        exact model.decodeValue_encodeValue actions parent _
          (model.evalNode_mem_retainedNodeValues actions intervention listed noise parent)
      rw [sameParents]

theorem retainedValueModel_evalObserved (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (listed : intervention ∈ HardIntervention.empty S :: actions)
    (noise : model.NoiseAssignment) :
    (model.retainedValueModel actions).evalObserved intervention noise = model.evalObserved intervention noise := by
  funext index
  change (model.observedEquiv index).forward
      (model.decodeValue actions _ ((model.retainedValueModel actions).evalNode intervention noise (P.hiddenDAG.observedNode index))) = _
  rw [model.retainedValueModel_evalNode actions intervention listed noise]
  rw [model.decodeValue_encodeValue actions _ _ (model.observedValue_mem_retainedNodeValues actions index _)]
  rfl

/-- Complete records agree, not just selected event values or positive cells.
The prior is unchanged, so pointwise evaluator simulation suffices here. -/
theorem retainedValueModel_interventionalDist (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (listed : intervention ∈ HardIntervention.empty S :: actions) :
    (model.retainedValueModel actions).interventionalDist intervention = model.interventionalDist intervention := by
  change model.prior.map ((model.retainedValueModel actions).evalObserved intervention) =
    model.prior.map (model.evalObserved intervention)
  apply congrArg (fun evaluation => model.prior.map evaluation)
  funext noise
  exact model.retainedValueModel_evalObserved actions intervention listed noise

theorem retainedValueModel_observationalDist (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S)) :
    (model.retainedValueModel actions).observationalDist = model.observationalDist :=
  model.retainedValueModel_interventionalDist actions _ List.mem_cons_self

theorem retainedValueModel_interventionalValue (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (listed : intervention ∈ HardIntervention.empty S :: actions)
    (event : Event S.Assignment) :
    (model.retainedValueModel actions).interventionalValue intervention event = model.interventionalValue intervention event := by
  unfold interventionalValue
  rw [model.retainedValueModel_interventionalDist actions intervention listed]

theorem retainedValueModel_eventPositive_iff (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (listed : intervention ∈ HardIntervention.empty S :: actions)
    (evidence : Event S.Assignment) :
    ((model.retainedValueModel actions).interventionalDist intervention).EventPositive evidence ↔
      (model.interventionalDist intervention).EventPositive evidence := by
  rw [model.retainedValueModel_interventionalDist actions intervention listed]

theorem retainedValueModel_conditionOn_probVal (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (listed : intervention ∈ HardIntervention.empty S :: actions)
    (evidence event : Event S.Assignment) (supported : (model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      ((((model.retainedValueModel actions).interventionalDist intervention).conditionOn evidence
        ((model.retainedValueModel_eventPositive_iff actions intervention listed evidence).mpr supported)).probVal event)
      (((model.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  rw [model.retainedValueModel_interventionalDist actions intervention listed]
  exact QProb.equiv_refl _

end FiniteHiddenDAGSCM
end Thesis.Causality
